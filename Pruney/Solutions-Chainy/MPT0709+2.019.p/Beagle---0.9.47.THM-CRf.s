%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:27 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   45 (  85 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 248 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_78,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_67,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

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
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k10_relat_1(k2_funct_1(B_9),A_8) = k9_relat_1(B_9,A_8)
      | ~ v2_funct_1(B_9)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [B_21,A_22] :
      ( k9_relat_1(k2_funct_1(B_21),A_22) = k10_relat_1(B_21,A_22)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k9_relat_1(B_5,k10_relat_1(B_5,A_4)),A_4)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k10_relat_1(B_31,k10_relat_1(k2_funct_1(B_31),A_32)),A_32)
      | ~ v1_funct_1(k2_funct_1(B_31))
      | ~ v1_relat_1(k2_funct_1(B_31))
      | ~ v2_funct_1(B_31)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_12])).

tff(c_144,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_16,c_111])).

tff(c_48,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k10_relat_1(B_20,k9_relat_1(B_20,A_19)))
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [B_20,A_19] :
      ( k10_relat_1(B_20,k9_relat_1(B_20,A_19)) = A_19
      | ~ r1_tarski(k10_relat_1(B_20,k9_relat_1(B_20,A_19)),A_19)
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_159,plain,(
    ! [B_39,A_40] :
      ( k10_relat_1(B_39,k9_relat_1(B_39,A_40)) = A_40
      | ~ r1_tarski(A_40,k1_relat_1(B_39))
      | ~ v1_funct_1(k2_funct_1(B_39))
      | ~ v1_relat_1(k2_funct_1(B_39))
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_144,c_51])).

tff(c_173,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_159])).

tff(c_183,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_173])).

tff(c_184,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_183])).

tff(c_186,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_189,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_189])).

tff(c_194,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_198,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:45:53 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.16/1.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.16/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.27  
% 2.16/1.29  tff(f_78, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 2.16/1.29  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.16/1.29  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 2.16/1.29  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.16/1.29  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.16/1.29  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.16/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.29  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.29  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.29  tff(c_20, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_24, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_16, plain, (![B_9, A_8]: (k10_relat_1(k2_funct_1(B_9), A_8)=k9_relat_1(B_9, A_8) | ~v2_funct_1(B_9) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.29  tff(c_52, plain, (![B_21, A_22]: (k9_relat_1(k2_funct_1(B_21), A_22)=k10_relat_1(B_21, A_22) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.29  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k9_relat_1(B_5, k10_relat_1(B_5, A_4)), A_4) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.29  tff(c_111, plain, (![B_31, A_32]: (r1_tarski(k10_relat_1(B_31, k10_relat_1(k2_funct_1(B_31), A_32)), A_32) | ~v1_funct_1(k2_funct_1(B_31)) | ~v1_relat_1(k2_funct_1(B_31)) | ~v2_funct_1(B_31) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_52, c_12])).
% 2.16/1.29  tff(c_144, plain, (![B_37, A_38]: (r1_tarski(k10_relat_1(B_37, k9_relat_1(B_37, A_38)), A_38) | ~v1_funct_1(k2_funct_1(B_37)) | ~v1_relat_1(k2_funct_1(B_37)) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_16, c_111])).
% 2.16/1.29  tff(c_48, plain, (![A_19, B_20]: (r1_tarski(A_19, k10_relat_1(B_20, k9_relat_1(B_20, A_19))) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.29  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.29  tff(c_51, plain, (![B_20, A_19]: (k10_relat_1(B_20, k9_relat_1(B_20, A_19))=A_19 | ~r1_tarski(k10_relat_1(B_20, k9_relat_1(B_20, A_19)), A_19) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_48, c_2])).
% 2.16/1.29  tff(c_159, plain, (![B_39, A_40]: (k10_relat_1(B_39, k9_relat_1(B_39, A_40))=A_40 | ~r1_tarski(A_40, k1_relat_1(B_39)) | ~v1_funct_1(k2_funct_1(B_39)) | ~v1_relat_1(k2_funct_1(B_39)) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_144, c_51])).
% 2.16/1.29  tff(c_173, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_159])).
% 2.16/1.29  tff(c_183, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_173])).
% 2.16/1.29  tff(c_184, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_20, c_183])).
% 2.16/1.29  tff(c_186, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_184])).
% 2.16/1.29  tff(c_189, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_186])).
% 2.16/1.29  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_189])).
% 2.16/1.29  tff(c_194, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_184])).
% 2.16/1.29  tff(c_198, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_194])).
% 2.16/1.29  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_198])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 40
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 2
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 1
% 2.16/1.29  #Demod        : 9
% 2.16/1.29  #Tautology    : 6
% 2.16/1.29  #SimpNegUnit  : 1
% 2.16/1.29  #BackRed      : 0
% 2.16/1.29  
% 2.16/1.29  #Partial instantiations: 0
% 2.16/1.29  #Strategies tried      : 1
% 2.16/1.29  
% 2.16/1.29  Timing (in seconds)
% 2.16/1.29  ----------------------
% 2.16/1.29  Preprocessing        : 0.30
% 2.16/1.29  Parsing              : 0.17
% 2.16/1.29  CNF conversion       : 0.02
% 2.16/1.29  Main loop            : 0.23
% 2.16/1.29  Inferencing          : 0.09
% 2.16/1.29  Reduction            : 0.06
% 2.16/1.29  Demodulation         : 0.04
% 2.16/1.29  BG Simplification    : 0.02
% 2.16/1.29  Subsumption          : 0.05
% 2.16/1.29  Abstraction          : 0.01
% 2.16/1.29  MUC search           : 0.00
% 2.16/1.29  Cooper               : 0.00
% 2.16/1.29  Total                : 0.56
% 2.16/1.29  Index Insertion      : 0.00
% 2.16/1.29  Index Deletion       : 0.00
% 2.16/1.29  Index Matching       : 0.00
% 2.16/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
