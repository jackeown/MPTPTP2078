%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:27 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  91 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 274 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(k2_funct_1(B_7),A_6) = k9_relat_1(B_7,A_6)
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_60,plain,(
    ! [B_22,A_23] :
      ( k9_relat_1(k2_funct_1(B_22),A_23) = k10_relat_1(B_22,A_23)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k9_relat_1(B_5,k10_relat_1(B_5,A_4)),A_4)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(k10_relat_1(B_33,k10_relat_1(k2_funct_1(B_33),A_34)),A_34)
      | ~ v1_funct_1(k2_funct_1(B_33))
      | ~ v1_relat_1(k2_funct_1(B_33))
      | ~ v2_funct_1(B_33)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_145,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k10_relat_1(B_37,k9_relat_1(B_37,A_38)),A_38)
      | ~ v1_funct_1(k2_funct_1(B_37))
      | ~ v1_relat_1(k2_funct_1(B_37))
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_126])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(A_26,k10_relat_1(C_27,B_28))
      | ~ r1_tarski(k9_relat_1(C_27,A_26),B_28)
      | ~ r1_tarski(A_26,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_95,plain,(
    ! [A_29,C_30] :
      ( r1_tarski(A_29,k10_relat_1(C_30,k9_relat_1(C_30,A_29)))
      | ~ r1_tarski(A_29,k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [C_30,A_29] :
      ( k10_relat_1(C_30,k9_relat_1(C_30,A_29)) = A_29
      | ~ r1_tarski(k10_relat_1(C_30,k9_relat_1(C_30,A_29)),A_29)
      | ~ r1_tarski(A_29,k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_160,plain,(
    ! [B_39,A_40] :
      ( k10_relat_1(B_39,k9_relat_1(B_39,A_40)) = A_40
      | ~ r1_tarski(A_40,k1_relat_1(B_39))
      | ~ v1_funct_1(k2_funct_1(B_39))
      | ~ v1_relat_1(k2_funct_1(B_39))
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_145,c_110])).

tff(c_174,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_184,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_174])).

tff(c_185,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_184])).

tff(c_187,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_190,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_190])).

tff(c_195,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_199,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_195])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.30  
% 1.99/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.20/1.30  
% 2.20/1.30  %Foreground sorts:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Background operators:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Foreground operators:
% 2.20/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.20/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.20/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.20/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.30  
% 2.20/1.31  tff(f_82, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 2.20/1.31  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.20/1.31  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 2.20/1.31  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.20/1.31  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.20/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.20/1.31  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 2.20/1.31  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.31  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.31  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.31  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.31  tff(c_20, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.31  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.31  tff(c_24, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.31  tff(c_14, plain, (![B_7, A_6]: (k10_relat_1(k2_funct_1(B_7), A_6)=k9_relat_1(B_7, A_6) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.31  tff(c_60, plain, (![B_22, A_23]: (k9_relat_1(k2_funct_1(B_22), A_23)=k10_relat_1(B_22, A_23) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.20/1.31  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k9_relat_1(B_5, k10_relat_1(B_5, A_4)), A_4) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.31  tff(c_126, plain, (![B_33, A_34]: (r1_tarski(k10_relat_1(B_33, k10_relat_1(k2_funct_1(B_33), A_34)), A_34) | ~v1_funct_1(k2_funct_1(B_33)) | ~v1_relat_1(k2_funct_1(B_33)) | ~v2_funct_1(B_33) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 2.20/1.31  tff(c_145, plain, (![B_37, A_38]: (r1_tarski(k10_relat_1(B_37, k9_relat_1(B_37, A_38)), A_38) | ~v1_funct_1(k2_funct_1(B_37)) | ~v1_relat_1(k2_funct_1(B_37)) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_14, c_126])).
% 2.20/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.31  tff(c_81, plain, (![A_26, C_27, B_28]: (r1_tarski(A_26, k10_relat_1(C_27, B_28)) | ~r1_tarski(k9_relat_1(C_27, A_26), B_28) | ~r1_tarski(A_26, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.20/1.31  tff(c_95, plain, (![A_29, C_30]: (r1_tarski(A_29, k10_relat_1(C_30, k9_relat_1(C_30, A_29))) | ~r1_tarski(A_29, k1_relat_1(C_30)) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.20/1.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.31  tff(c_110, plain, (![C_30, A_29]: (k10_relat_1(C_30, k9_relat_1(C_30, A_29))=A_29 | ~r1_tarski(k10_relat_1(C_30, k9_relat_1(C_30, A_29)), A_29) | ~r1_tarski(A_29, k1_relat_1(C_30)) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(resolution, [status(thm)], [c_95, c_2])).
% 2.20/1.31  tff(c_160, plain, (![B_39, A_40]: (k10_relat_1(B_39, k9_relat_1(B_39, A_40))=A_40 | ~r1_tarski(A_40, k1_relat_1(B_39)) | ~v1_funct_1(k2_funct_1(B_39)) | ~v1_relat_1(k2_funct_1(B_39)) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_145, c_110])).
% 2.20/1.31  tff(c_174, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_160])).
% 2.20/1.31  tff(c_184, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_174])).
% 2.20/1.31  tff(c_185, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_20, c_184])).
% 2.20/1.31  tff(c_187, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_185])).
% 2.20/1.31  tff(c_190, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_187])).
% 2.20/1.31  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_190])).
% 2.20/1.31  tff(c_195, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_185])).
% 2.20/1.31  tff(c_199, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_195])).
% 2.20/1.31  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_199])).
% 2.20/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  
% 2.20/1.31  Inference rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Ref     : 0
% 2.20/1.31  #Sup     : 39
% 2.20/1.31  #Fact    : 0
% 2.20/1.31  #Define  : 0
% 2.20/1.31  #Split   : 2
% 2.20/1.31  #Chain   : 0
% 2.20/1.31  #Close   : 0
% 2.20/1.31  
% 2.20/1.31  Ordering : KBO
% 2.20/1.31  
% 2.20/1.31  Simplification rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Subsume      : 0
% 2.20/1.31  #Demod        : 10
% 2.20/1.31  #Tautology    : 7
% 2.20/1.31  #SimpNegUnit  : 1
% 2.20/1.31  #BackRed      : 0
% 2.20/1.31  
% 2.20/1.31  #Partial instantiations: 0
% 2.20/1.31  #Strategies tried      : 1
% 2.20/1.31  
% 2.20/1.31  Timing (in seconds)
% 2.20/1.31  ----------------------
% 2.20/1.32  Preprocessing        : 0.28
% 2.20/1.32  Parsing              : 0.16
% 2.20/1.32  CNF conversion       : 0.02
% 2.20/1.32  Main loop            : 0.20
% 2.20/1.32  Inferencing          : 0.08
% 2.20/1.32  Reduction            : 0.05
% 2.20/1.32  Demodulation         : 0.04
% 2.20/1.32  BG Simplification    : 0.01
% 2.20/1.32  Subsumption          : 0.05
% 2.20/1.32  Abstraction          : 0.01
% 2.20/1.32  MUC search           : 0.00
% 2.20/1.32  Cooper               : 0.00
% 2.20/1.32  Total                : 0.50
% 2.20/1.32  Index Insertion      : 0.00
% 2.20/1.32  Index Deletion       : 0.00
% 2.20/1.32  Index Matching       : 0.00
% 2.20/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
