%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:13 EST 2020

% Result     : Theorem 24.02s
% Output     : CNFRefutation 24.02s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 278 expanded)
%              Number of leaves         :   32 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 585 expanded)
%              Number of equality atoms :   25 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k3_xboole_0(k1_relat_1(B),A),k9_relat_1(k4_relat_1(B),k9_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => r1_tarski(k5_relat_1(k7_relat_1(B,A),C),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).

tff(f_73,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5] :
      ( v1_relat_1(k4_relat_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_15] :
      ( k1_relat_1(k4_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_354,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_relat_1(A_56),k1_relat_1(B_57))
      | ~ r1_tarski(A_56,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2810,plain,(
    ! [A_166,A_167] :
      ( r1_tarski(k1_relat_1(A_166),k2_relat_1(A_167))
      | ~ r1_tarski(A_166,k4_relat_1(A_167))
      | ~ v1_relat_1(k4_relat_1(A_167))
      | ~ v1_relat_1(A_166)
      | ~ v1_relat_1(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_354])).

tff(c_38879,plain,(
    ! [A_728,B_729,A_730] :
      ( r1_tarski(k1_relat_1(A_728),k9_relat_1(B_729,A_730))
      | ~ r1_tarski(A_728,k4_relat_1(k7_relat_1(B_729,A_730)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(B_729,A_730)))
      | ~ v1_relat_1(A_728)
      | ~ v1_relat_1(k7_relat_1(B_729,A_730))
      | ~ v1_relat_1(B_729) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2810])).

tff(c_266,plain,(
    ! [B_50,A_51] :
      ( k3_xboole_0(k1_relat_1(B_50),A_51) = k1_relat_1(k7_relat_1(B_50,A_51))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_292,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,k1_relat_1(B_53)) = k1_relat_1(k7_relat_1(B_53,A_52))
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_2])).

tff(c_36,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1'),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_39,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1',k1_relat_1('#skF_2')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_302,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_39])).

tff(c_329,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_302])).

tff(c_38952,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38879,c_329])).

tff(c_38976,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38952])).

tff(c_38979,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_38976])).

tff(c_38983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38979])).

tff(c_38985,plain,(
    v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38952])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_219,plain,(
    ! [B_46,A_47] :
      ( k2_relat_1(k7_relat_1(B_46,A_47)) = k9_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3427,plain,(
    ! [B_178,A_179] :
      ( k5_relat_1(k7_relat_1(B_178,A_179),k6_relat_1(k9_relat_1(B_178,A_179))) = k7_relat_1(B_178,A_179)
      | ~ v1_relat_1(k7_relat_1(B_178,A_179))
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_28])).

tff(c_32,plain,(
    ! [B_24,A_23,C_26] :
      ( r1_tarski(k5_relat_1(k7_relat_1(B_24,A_23),C_26),k5_relat_1(B_24,C_26))
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3444,plain,(
    ! [B_178,A_179] :
      ( r1_tarski(k7_relat_1(B_178,A_179),k5_relat_1(B_178,k6_relat_1(k9_relat_1(B_178,A_179))))
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(B_178,A_179)))
      | ~ v1_relat_1(B_178)
      | ~ v1_relat_1(k7_relat_1(B_178,A_179))
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3427,c_32])).

tff(c_3481,plain,(
    ! [B_178,A_179] :
      ( r1_tarski(k7_relat_1(B_178,A_179),k5_relat_1(B_178,k6_relat_1(k9_relat_1(B_178,A_179))))
      | ~ v1_relat_1(k7_relat_1(B_178,A_179))
      | ~ v1_relat_1(B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3444])).

tff(c_26,plain,(
    ! [A_19] : k4_relat_1(k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_relat_1(A_27),B_28) = k7_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12,plain,(
    ! [A_9] :
      ( k4_relat_1(k4_relat_1(A_9)) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_469,plain,(
    ! [B_74,A_75] :
      ( k5_relat_1(k4_relat_1(B_74),k4_relat_1(A_75)) = k4_relat_1(k5_relat_1(A_75,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1377,plain,(
    ! [A_135,A_136] :
      ( k4_relat_1(k5_relat_1(A_135,k4_relat_1(A_136))) = k5_relat_1(A_136,k4_relat_1(A_135))
      | ~ v1_relat_1(k4_relat_1(A_136))
      | ~ v1_relat_1(A_135)
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_469])).

tff(c_1432,plain,(
    ! [A_136,A_27] :
      ( k5_relat_1(A_136,k4_relat_1(k6_relat_1(A_27))) = k4_relat_1(k7_relat_1(k4_relat_1(A_136),A_27))
      | ~ v1_relat_1(k4_relat_1(A_136))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(A_136)
      | ~ v1_relat_1(k4_relat_1(A_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1377])).

tff(c_1446,plain,(
    ! [A_136,A_27] :
      ( k4_relat_1(k7_relat_1(k4_relat_1(A_136),A_27)) = k5_relat_1(A_136,k6_relat_1(A_27))
      | ~ v1_relat_1(A_136)
      | ~ v1_relat_1(k4_relat_1(A_136)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26,c_1432])).

tff(c_38984,plain,
    ( ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_38952])).

tff(c_39088,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_38984])).

tff(c_39091,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k6_relat_1(k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1446,c_39088])).

tff(c_39093,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k6_relat_1(k9_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38985,c_38,c_39091])).

tff(c_39096,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3481,c_39093])).

tff(c_39099,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_39096])).

tff(c_39102,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_39099])).

tff(c_39106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_39102])).

tff(c_39107,plain,
    ( ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_38984])).

tff(c_39438,plain,(
    ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_39107])).

tff(c_39441,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_39438])).

tff(c_39445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38985,c_39441])).

tff(c_39447,plain,(
    v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_39107])).

tff(c_39446,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_39107])).

tff(c_39448,plain,(
    ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_39446])).

tff(c_39457,plain,(
    ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_39448])).

tff(c_39466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39447,c_39457])).

tff(c_39467,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_39446])).

tff(c_39471,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_39467])).

tff(c_39475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_39471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:14:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.02/11.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.02/11.76  
% 24.02/11.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.02/11.76  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 24.02/11.76  
% 24.02/11.76  %Foreground sorts:
% 24.02/11.76  
% 24.02/11.76  
% 24.02/11.76  %Background operators:
% 24.02/11.76  
% 24.02/11.76  
% 24.02/11.76  %Foreground operators:
% 24.02/11.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.02/11.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 24.02/11.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 24.02/11.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.02/11.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 24.02/11.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.02/11.76  tff('#skF_2', type, '#skF_2': $i).
% 24.02/11.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 24.02/11.76  tff('#skF_1', type, '#skF_1': $i).
% 24.02/11.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.02/11.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.02/11.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 24.02/11.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.02/11.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.02/11.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.02/11.76  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 24.02/11.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.02/11.76  
% 24.02/11.78  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k3_xboole_0(k1_relat_1(B), A), k9_relat_1(k4_relat_1(B), k9_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_relat_1)).
% 24.02/11.78  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 24.02/11.78  tff(f_33, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 24.02/11.78  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 24.02/11.78  tff(f_64, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 24.02/11.78  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 24.02/11.78  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 24.02/11.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.02/11.78  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 24.02/11.78  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 24.02/11.78  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(k7_relat_1(B, A), C), k5_relat_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_relat_1)).
% 24.02/11.78  tff(f_73, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 24.02/11.78  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 24.02/11.78  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 24.02/11.78  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 24.02/11.78  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 24.02/11.78  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.02/11.78  tff(c_6, plain, (![A_5]: (v1_relat_1(k4_relat_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.02/11.78  tff(c_14, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.02/11.78  tff(c_22, plain, (![A_15]: (k1_relat_1(k4_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 24.02/11.78  tff(c_354, plain, (![A_56, B_57]: (r1_tarski(k1_relat_1(A_56), k1_relat_1(B_57)) | ~r1_tarski(A_56, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.02/11.78  tff(c_2810, plain, (![A_166, A_167]: (r1_tarski(k1_relat_1(A_166), k2_relat_1(A_167)) | ~r1_tarski(A_166, k4_relat_1(A_167)) | ~v1_relat_1(k4_relat_1(A_167)) | ~v1_relat_1(A_166) | ~v1_relat_1(A_167))), inference(superposition, [status(thm), theory('equality')], [c_22, c_354])).
% 24.02/11.78  tff(c_38879, plain, (![A_728, B_729, A_730]: (r1_tarski(k1_relat_1(A_728), k9_relat_1(B_729, A_730)) | ~r1_tarski(A_728, k4_relat_1(k7_relat_1(B_729, A_730))) | ~v1_relat_1(k4_relat_1(k7_relat_1(B_729, A_730))) | ~v1_relat_1(A_728) | ~v1_relat_1(k7_relat_1(B_729, A_730)) | ~v1_relat_1(B_729))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2810])).
% 24.02/11.78  tff(c_266, plain, (![B_50, A_51]: (k3_xboole_0(k1_relat_1(B_50), A_51)=k1_relat_1(k7_relat_1(B_50, A_51)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.02/11.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.02/11.78  tff(c_292, plain, (![A_52, B_53]: (k3_xboole_0(A_52, k1_relat_1(B_53))=k1_relat_1(k7_relat_1(B_53, A_52)) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_266, c_2])).
% 24.02/11.78  tff(c_36, plain, (~r1_tarski(k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 24.02/11.78  tff(c_39, plain, (~r1_tarski(k3_xboole_0('#skF_1', k1_relat_1('#skF_2')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 24.02/11.78  tff(c_302, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_292, c_39])).
% 24.02/11.78  tff(c_329, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_302])).
% 24.02/11.78  tff(c_38952, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38879, c_329])).
% 24.02/11.78  tff(c_38976, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_38952])).
% 24.02/11.78  tff(c_38979, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_38976])).
% 24.02/11.78  tff(c_38983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_38979])).
% 24.02/11.78  tff(c_38985, plain, (v1_relat_1(k4_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_38952])).
% 24.02/11.78  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.02/11.78  tff(c_219, plain, (![B_46, A_47]: (k2_relat_1(k7_relat_1(B_46, A_47))=k9_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.02/11.78  tff(c_28, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.02/11.78  tff(c_3427, plain, (![B_178, A_179]: (k5_relat_1(k7_relat_1(B_178, A_179), k6_relat_1(k9_relat_1(B_178, A_179)))=k7_relat_1(B_178, A_179) | ~v1_relat_1(k7_relat_1(B_178, A_179)) | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_219, c_28])).
% 24.02/11.78  tff(c_32, plain, (![B_24, A_23, C_26]: (r1_tarski(k5_relat_1(k7_relat_1(B_24, A_23), C_26), k5_relat_1(B_24, C_26)) | ~v1_relat_1(C_26) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.02/11.78  tff(c_3444, plain, (![B_178, A_179]: (r1_tarski(k7_relat_1(B_178, A_179), k5_relat_1(B_178, k6_relat_1(k9_relat_1(B_178, A_179)))) | ~v1_relat_1(k6_relat_1(k9_relat_1(B_178, A_179))) | ~v1_relat_1(B_178) | ~v1_relat_1(k7_relat_1(B_178, A_179)) | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_3427, c_32])).
% 24.02/11.78  tff(c_3481, plain, (![B_178, A_179]: (r1_tarski(k7_relat_1(B_178, A_179), k5_relat_1(B_178, k6_relat_1(k9_relat_1(B_178, A_179)))) | ~v1_relat_1(k7_relat_1(B_178, A_179)) | ~v1_relat_1(B_178))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3444])).
% 24.02/11.78  tff(c_26, plain, (![A_19]: (k4_relat_1(k6_relat_1(A_19))=k6_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.02/11.78  tff(c_34, plain, (![A_27, B_28]: (k5_relat_1(k6_relat_1(A_27), B_28)=k7_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.02/11.78  tff(c_12, plain, (![A_9]: (k4_relat_1(k4_relat_1(A_9))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.02/11.78  tff(c_469, plain, (![B_74, A_75]: (k5_relat_1(k4_relat_1(B_74), k4_relat_1(A_75))=k4_relat_1(k5_relat_1(A_75, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_71])).
% 24.02/11.78  tff(c_1377, plain, (![A_135, A_136]: (k4_relat_1(k5_relat_1(A_135, k4_relat_1(A_136)))=k5_relat_1(A_136, k4_relat_1(A_135)) | ~v1_relat_1(k4_relat_1(A_136)) | ~v1_relat_1(A_135) | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_12, c_469])).
% 24.02/11.78  tff(c_1432, plain, (![A_136, A_27]: (k5_relat_1(A_136, k4_relat_1(k6_relat_1(A_27)))=k4_relat_1(k7_relat_1(k4_relat_1(A_136), A_27)) | ~v1_relat_1(k4_relat_1(A_136)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(A_136) | ~v1_relat_1(k4_relat_1(A_136)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1377])).
% 24.02/11.78  tff(c_1446, plain, (![A_136, A_27]: (k4_relat_1(k7_relat_1(k4_relat_1(A_136), A_27))=k5_relat_1(A_136, k6_relat_1(A_27)) | ~v1_relat_1(A_136) | ~v1_relat_1(k4_relat_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26, c_1432])).
% 24.02/11.78  tff(c_38984, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitRight, [status(thm)], [c_38952])).
% 24.02/11.78  tff(c_39088, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitLeft, [status(thm)], [c_38984])).
% 24.02/11.78  tff(c_39091, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k6_relat_1(k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1446, c_39088])).
% 24.02/11.78  tff(c_39093, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k6_relat_1(k9_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38985, c_38, c_39091])).
% 24.02/11.78  tff(c_39096, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3481, c_39093])).
% 24.02/11.78  tff(c_39099, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_39096])).
% 24.02/11.78  tff(c_39102, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_39099])).
% 24.02/11.78  tff(c_39106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_39102])).
% 24.02/11.78  tff(c_39107, plain, (~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_38984])).
% 24.02/11.78  tff(c_39438, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_39107])).
% 24.02/11.78  tff(c_39441, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_39438])).
% 24.02/11.78  tff(c_39445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38985, c_39441])).
% 24.02/11.78  tff(c_39447, plain, (v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_39107])).
% 24.02/11.78  tff(c_39446, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitRight, [status(thm)], [c_39107])).
% 24.02/11.78  tff(c_39448, plain, (~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitLeft, [status(thm)], [c_39446])).
% 24.02/11.78  tff(c_39457, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(resolution, [status(thm)], [c_6, c_39448])).
% 24.02/11.78  tff(c_39466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39447, c_39457])).
% 24.02/11.78  tff(c_39467, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_39446])).
% 24.02/11.78  tff(c_39471, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_39467])).
% 24.02/11.78  tff(c_39475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_39471])).
% 24.02/11.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.02/11.78  
% 24.02/11.78  Inference rules
% 24.02/11.78  ----------------------
% 24.02/11.78  #Ref     : 0
% 24.02/11.78  #Sup     : 10097
% 24.02/11.78  #Fact    : 0
% 24.02/11.78  #Define  : 0
% 24.02/11.78  #Split   : 4
% 24.02/11.78  #Chain   : 0
% 24.02/11.78  #Close   : 0
% 24.02/11.78  
% 24.02/11.78  Ordering : KBO
% 24.02/11.78  
% 24.02/11.78  Simplification rules
% 24.02/11.78  ----------------------
% 24.02/11.78  #Subsume      : 912
% 24.02/11.78  #Demod        : 16988
% 24.02/11.78  #Tautology    : 2381
% 24.02/11.78  #SimpNegUnit  : 0
% 24.02/11.78  #BackRed      : 14
% 24.02/11.78  
% 24.02/11.78  #Partial instantiations: 0
% 24.02/11.78  #Strategies tried      : 1
% 24.02/11.78  
% 24.02/11.78  Timing (in seconds)
% 24.02/11.78  ----------------------
% 24.02/11.78  Preprocessing        : 0.50
% 24.02/11.78  Parsing              : 0.25
% 24.02/11.78  CNF conversion       : 0.04
% 24.02/11.78  Main loop            : 10.35
% 24.02/11.78  Inferencing          : 2.19
% 24.02/11.78  Reduction            : 4.20
% 24.02/11.78  Demodulation         : 3.57
% 24.02/11.78  BG Simplification    : 0.29
% 24.02/11.78  Subsumption          : 3.11
% 24.02/11.78  Abstraction          : 0.38
% 24.02/11.78  MUC search           : 0.00
% 24.02/11.78  Cooper               : 0.00
% 24.02/11.78  Total                : 10.89
% 24.02/11.78  Index Insertion      : 0.00
% 24.02/11.78  Index Deletion       : 0.00
% 24.02/11.78  Index Matching       : 0.00
% 24.02/11.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
