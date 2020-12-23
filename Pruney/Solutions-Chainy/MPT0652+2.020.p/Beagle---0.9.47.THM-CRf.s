%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:55 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   46 (  97 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 273 expanded)
%              Number of equality atoms :   22 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_210,plain,(
    ! [B_31,A_32] :
      ( k2_relat_1(k5_relat_1(B_31,A_32)) = k2_relat_1(A_32)
      | ~ r1_tarski(k1_relat_1(A_32),k2_relat_1(B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_258,plain,(
    ! [A_38,A_39] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_38),A_39)) = k2_relat_1(A_39)
      | ~ r1_tarski(k1_relat_1(A_39),k1_relat_1(A_38))
      | ~ v1_relat_1(k2_funct_1(A_38))
      | ~ v1_relat_1(A_39)
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_210])).

tff(c_282,plain,(
    ! [A_40] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_40),A_40)) = k2_relat_1(A_40)
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_18,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    ! [A_20,B_21] :
      ( k1_relat_1(k5_relat_1(A_20,B_21)) = k1_relat_1(A_20)
      | ~ r1_tarski(k2_relat_1(A_20),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_137,plain,(
    ! [A_28,B_29] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_28),B_29)) = k1_relat_1(k2_funct_1(A_28))
      | ~ r1_tarski(k1_relat_1(A_28),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k2_funct_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_155,plain,(
    ! [A_30] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_30),A_30)) = k1_relat_1(k2_funct_1(A_30))
      | ~ v1_relat_1(k2_funct_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_179,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_56])).

tff(c_185,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_179])).

tff(c_187,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_190,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_190])).

tff(c_195,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_199,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_195])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_199])).

tff(c_204,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_300,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_204])).

tff(c_307,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_300])).

tff(c_311,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_307])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.27  
% 2.32/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.27  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.32/1.27  
% 2.32/1.27  %Foreground sorts:
% 2.32/1.27  
% 2.32/1.27  
% 2.32/1.27  %Background operators:
% 2.32/1.27  
% 2.32/1.27  
% 2.32/1.27  %Foreground operators:
% 2.32/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.32/1.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.32/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.27  
% 2.32/1.28  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.32/1.28  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.32/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.32/1.28  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.32/1.28  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.32/1.28  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.32/1.28  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.32/1.28  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.32/1.28  tff(c_14, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.32/1.28  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.32/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.28  tff(c_16, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.32/1.28  tff(c_210, plain, (![B_31, A_32]: (k2_relat_1(k5_relat_1(B_31, A_32))=k2_relat_1(A_32) | ~r1_tarski(k1_relat_1(A_32), k2_relat_1(B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.28  tff(c_258, plain, (![A_38, A_39]: (k2_relat_1(k5_relat_1(k2_funct_1(A_38), A_39))=k2_relat_1(A_39) | ~r1_tarski(k1_relat_1(A_39), k1_relat_1(A_38)) | ~v1_relat_1(k2_funct_1(A_38)) | ~v1_relat_1(A_39) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_16, c_210])).
% 2.32/1.28  tff(c_282, plain, (![A_40]: (k2_relat_1(k5_relat_1(k2_funct_1(A_40), A_40))=k2_relat_1(A_40) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_6, c_258])).
% 2.32/1.28  tff(c_18, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.32/1.28  tff(c_64, plain, (![A_20, B_21]: (k1_relat_1(k5_relat_1(A_20, B_21))=k1_relat_1(A_20) | ~r1_tarski(k2_relat_1(A_20), k1_relat_1(B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.32/1.28  tff(c_137, plain, (![A_28, B_29]: (k1_relat_1(k5_relat_1(k2_funct_1(A_28), B_29))=k1_relat_1(k2_funct_1(A_28)) | ~r1_tarski(k1_relat_1(A_28), k1_relat_1(B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(k2_funct_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_16, c_64])).
% 2.32/1.28  tff(c_155, plain, (![A_30]: (k1_relat_1(k5_relat_1(k2_funct_1(A_30), A_30))=k1_relat_1(k2_funct_1(A_30)) | ~v1_relat_1(k2_funct_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_6, c_137])).
% 2.32/1.28  tff(c_20, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.32/1.28  tff(c_56, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.32/1.28  tff(c_179, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_155, c_56])).
% 2.32/1.28  tff(c_185, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_179])).
% 2.32/1.28  tff(c_187, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_185])).
% 2.32/1.28  tff(c_190, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_187])).
% 2.32/1.28  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_190])).
% 2.32/1.28  tff(c_195, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_185])).
% 2.32/1.28  tff(c_199, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_195])).
% 2.32/1.28  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_199])).
% 2.32/1.28  tff(c_204, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.32/1.28  tff(c_300, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_282, c_204])).
% 2.32/1.28  tff(c_307, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_300])).
% 2.32/1.28  tff(c_311, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_307])).
% 2.32/1.28  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_311])).
% 2.32/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.28  
% 2.32/1.28  Inference rules
% 2.32/1.28  ----------------------
% 2.32/1.28  #Ref     : 0
% 2.32/1.28  #Sup     : 73
% 2.32/1.28  #Fact    : 0
% 2.32/1.28  #Define  : 0
% 2.32/1.28  #Split   : 3
% 2.32/1.28  #Chain   : 0
% 2.32/1.28  #Close   : 0
% 2.32/1.28  
% 2.32/1.28  Ordering : KBO
% 2.32/1.28  
% 2.32/1.28  Simplification rules
% 2.32/1.28  ----------------------
% 2.32/1.28  #Subsume      : 3
% 2.32/1.28  #Demod        : 15
% 2.32/1.28  #Tautology    : 18
% 2.32/1.28  #SimpNegUnit  : 0
% 2.32/1.28  #BackRed      : 0
% 2.32/1.28  
% 2.32/1.28  #Partial instantiations: 0
% 2.32/1.28  #Strategies tried      : 1
% 2.32/1.28  
% 2.32/1.28  Timing (in seconds)
% 2.32/1.28  ----------------------
% 2.32/1.28  Preprocessing        : 0.27
% 2.32/1.28  Parsing              : 0.15
% 2.32/1.28  CNF conversion       : 0.02
% 2.32/1.28  Main loop            : 0.25
% 2.32/1.28  Inferencing          : 0.09
% 2.32/1.28  Reduction            : 0.06
% 2.32/1.28  Demodulation         : 0.04
% 2.32/1.28  BG Simplification    : 0.02
% 2.32/1.28  Subsumption          : 0.06
% 2.32/1.28  Abstraction          : 0.01
% 2.32/1.28  MUC search           : 0.00
% 2.32/1.28  Cooper               : 0.00
% 2.32/1.28  Total                : 0.55
% 2.32/1.28  Index Insertion      : 0.00
% 2.32/1.28  Index Deletion       : 0.00
% 2.32/1.28  Index Matching       : 0.00
% 2.32/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
