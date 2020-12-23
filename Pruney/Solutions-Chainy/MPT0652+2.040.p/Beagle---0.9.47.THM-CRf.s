%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:57 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 109 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 344 expanded)
%              Number of equality atoms :   24 (  87 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_51,plain,(
    ! [A_19] :
      ( k2_relat_1(k5_relat_1(A_19,k2_funct_1(A_19))) = k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_1,B_3)),k2_relat_1(B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_449,plain,(
    ! [A_48] :
      ( r1_tarski(k1_relat_1(A_48),k2_relat_1(k2_funct_1(A_48)))
      | ~ v1_relat_1(k2_funct_1(A_48))
      | ~ v1_relat_1(A_48)
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_2])).

tff(c_6,plain,(
    ! [B_9,A_7] :
      ( k2_relat_1(k5_relat_1(B_9,A_7)) = k2_relat_1(A_7)
      | ~ r1_tarski(k1_relat_1(A_7),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_466,plain,(
    ! [A_49] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_49),A_49)) = k2_relat_1(A_49)
      | ~ v1_relat_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_449,c_6])).

tff(c_14,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_12] :
      ( k2_relat_1(k5_relat_1(A_12,k2_funct_1(A_12))) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_47,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_17,B_18)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_26,A_27] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_26,k2_funct_1(A_27))),k1_relat_1(A_27))
      | ~ v1_relat_1(k2_funct_1(A_27))
      | ~ v1_relat_1(A_26)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_47])).

tff(c_125,plain,(
    ! [A_12] :
      ( r1_tarski(k1_relat_1(A_12),k1_relat_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_116])).

tff(c_89,plain,(
    ! [A_23,B_24] :
      ( k1_relat_1(k5_relat_1(A_23,B_24)) = k1_relat_1(A_23)
      | ~ r1_tarski(k2_relat_1(A_23),k1_relat_1(B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_321,plain,(
    ! [A_40,B_41] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_40),B_41)) = k1_relat_1(k2_funct_1(A_40))
      | ~ r1_tarski(k1_relat_1(A_40),k1_relat_1(B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_338,plain,(
    ! [A_42] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_42),A_42)) = k1_relat_1(k2_funct_1(A_42))
      | ~ v1_relat_1(k2_funct_1(A_42))
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_125,c_321])).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_377,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_66])).

tff(c_383,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_377])).

tff(c_385,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_388,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_385])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_388])).

tff(c_393,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_397,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_393])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_397])).

tff(c_402,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_478,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_402])).

tff(c_491,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_478])).

tff(c_495,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_491])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.48  
% 2.98/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.48  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.98/1.48  
% 2.98/1.48  %Foreground sorts:
% 2.98/1.48  
% 2.98/1.48  
% 2.98/1.48  %Background operators:
% 2.98/1.48  
% 2.98/1.48  
% 2.98/1.48  %Foreground operators:
% 2.98/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.98/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.98/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.98/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.48  
% 2.98/1.50  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.98/1.50  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.98/1.50  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 2.98/1.50  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.98/1.50  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.98/1.50  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.98/1.50  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.98/1.50  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.98/1.50  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.98/1.50  tff(c_10, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.98/1.50  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.98/1.50  tff(c_51, plain, (![A_19]: (k2_relat_1(k5_relat_1(A_19, k2_funct_1(A_19)))=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.98/1.50  tff(c_2, plain, (![A_1, B_3]: (r1_tarski(k2_relat_1(k5_relat_1(A_1, B_3)), k2_relat_1(B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.50  tff(c_449, plain, (![A_48]: (r1_tarski(k1_relat_1(A_48), k2_relat_1(k2_funct_1(A_48))) | ~v1_relat_1(k2_funct_1(A_48)) | ~v1_relat_1(A_48) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_51, c_2])).
% 2.98/1.50  tff(c_6, plain, (![B_9, A_7]: (k2_relat_1(k5_relat_1(B_9, A_7))=k2_relat_1(A_7) | ~r1_tarski(k1_relat_1(A_7), k2_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.50  tff(c_466, plain, (![A_49]: (k2_relat_1(k5_relat_1(k2_funct_1(A_49), A_49))=k2_relat_1(A_49) | ~v1_relat_1(k2_funct_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_449, c_6])).
% 2.98/1.50  tff(c_14, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.50  tff(c_16, plain, (![A_12]: (k2_relat_1(k5_relat_1(A_12, k2_funct_1(A_12)))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.98/1.50  tff(c_12, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.50  tff(c_47, plain, (![A_17, B_18]: (r1_tarski(k2_relat_1(k5_relat_1(A_17, B_18)), k2_relat_1(B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.50  tff(c_116, plain, (![A_26, A_27]: (r1_tarski(k2_relat_1(k5_relat_1(A_26, k2_funct_1(A_27))), k1_relat_1(A_27)) | ~v1_relat_1(k2_funct_1(A_27)) | ~v1_relat_1(A_26) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_12, c_47])).
% 2.98/1.50  tff(c_125, plain, (![A_12]: (r1_tarski(k1_relat_1(A_12), k1_relat_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_116])).
% 2.98/1.50  tff(c_89, plain, (![A_23, B_24]: (k1_relat_1(k5_relat_1(A_23, B_24))=k1_relat_1(A_23) | ~r1_tarski(k2_relat_1(A_23), k1_relat_1(B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.50  tff(c_321, plain, (![A_40, B_41]: (k1_relat_1(k5_relat_1(k2_funct_1(A_40), B_41))=k1_relat_1(k2_funct_1(A_40)) | ~r1_tarski(k1_relat_1(A_40), k1_relat_1(B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 2.98/1.50  tff(c_338, plain, (![A_42]: (k1_relat_1(k5_relat_1(k2_funct_1(A_42), A_42))=k1_relat_1(k2_funct_1(A_42)) | ~v1_relat_1(k2_funct_1(A_42)) | ~v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_125, c_321])).
% 2.98/1.50  tff(c_20, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.98/1.50  tff(c_66, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.98/1.50  tff(c_377, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_338, c_66])).
% 2.98/1.50  tff(c_383, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_377])).
% 2.98/1.50  tff(c_385, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_383])).
% 2.98/1.50  tff(c_388, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_385])).
% 2.98/1.50  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_388])).
% 2.98/1.50  tff(c_393, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_383])).
% 2.98/1.50  tff(c_397, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_393])).
% 2.98/1.50  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_397])).
% 2.98/1.50  tff(c_402, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.98/1.50  tff(c_478, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_466, c_402])).
% 2.98/1.50  tff(c_491, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_478])).
% 2.98/1.50  tff(c_495, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_491])).
% 2.98/1.50  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_495])).
% 2.98/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.50  
% 2.98/1.50  Inference rules
% 2.98/1.50  ----------------------
% 2.98/1.50  #Ref     : 0
% 2.98/1.50  #Sup     : 132
% 2.98/1.50  #Fact    : 0
% 2.98/1.50  #Define  : 0
% 2.98/1.50  #Split   : 2
% 2.98/1.50  #Chain   : 0
% 2.98/1.50  #Close   : 0
% 2.98/1.50  
% 2.98/1.50  Ordering : KBO
% 2.98/1.50  
% 2.98/1.50  Simplification rules
% 2.98/1.50  ----------------------
% 2.98/1.50  #Subsume      : 7
% 2.98/1.50  #Demod        : 13
% 2.98/1.50  #Tautology    : 20
% 2.98/1.50  #SimpNegUnit  : 0
% 2.98/1.50  #BackRed      : 0
% 2.98/1.50  
% 2.98/1.50  #Partial instantiations: 0
% 2.98/1.50  #Strategies tried      : 1
% 2.98/1.50  
% 2.98/1.50  Timing (in seconds)
% 2.98/1.50  ----------------------
% 2.98/1.50  Preprocessing        : 0.31
% 2.98/1.50  Parsing              : 0.17
% 2.98/1.51  CNF conversion       : 0.02
% 2.98/1.51  Main loop            : 0.37
% 2.98/1.51  Inferencing          : 0.14
% 2.98/1.51  Reduction            : 0.10
% 2.98/1.51  Demodulation         : 0.07
% 2.98/1.51  BG Simplification    : 0.03
% 2.98/1.51  Subsumption          : 0.08
% 2.98/1.51  Abstraction          : 0.02
% 2.98/1.51  MUC search           : 0.00
% 2.98/1.51  Cooper               : 0.00
% 2.98/1.51  Total                : 0.72
% 2.98/1.51  Index Insertion      : 0.00
% 2.98/1.51  Index Deletion       : 0.00
% 2.98/1.51  Index Matching       : 0.00
% 2.98/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
