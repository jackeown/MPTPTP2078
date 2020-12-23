%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:13 EST 2020

% Result     : Theorem 19.97s
% Output     : CNFRefutation 19.97s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 277 expanded)
%              Number of leaves         :   31 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 585 expanded)
%              Number of equality atoms :   25 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(c_422,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_relat_1(A_60),k1_relat_1(B_61))
      | ~ r1_tarski(A_60,B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1702,plain,(
    ! [A_144,A_145] :
      ( r1_tarski(k1_relat_1(A_144),k2_relat_1(A_145))
      | ~ r1_tarski(A_144,k4_relat_1(A_145))
      | ~ v1_relat_1(k4_relat_1(A_145))
      | ~ v1_relat_1(A_144)
      | ~ v1_relat_1(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_422])).

tff(c_39424,plain,(
    ! [A_713,B_714,A_715] :
      ( r1_tarski(k1_relat_1(A_713),k9_relat_1(B_714,A_715))
      | ~ r1_tarski(A_713,k4_relat_1(k7_relat_1(B_714,A_715)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(B_714,A_715)))
      | ~ v1_relat_1(A_713)
      | ~ v1_relat_1(k7_relat_1(B_714,A_715))
      | ~ v1_relat_1(B_714) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1702])).

tff(c_272,plain,(
    ! [B_50,A_51] :
      ( k3_xboole_0(k1_relat_1(B_50),A_51) = k1_relat_1(k7_relat_1(B_50,A_51))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_320,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,k1_relat_1(B_55)) = k1_relat_1(k7_relat_1(B_55,A_54))
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_2])).

tff(c_36,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1'),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_39,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1',k1_relat_1('#skF_2')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_333,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_39])).

tff(c_360,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_333])).

tff(c_39500,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_39424,c_360])).

tff(c_39606,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_39500])).

tff(c_39609,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_39606])).

tff(c_39613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_39609])).

tff(c_39615,plain,(
    v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_39500])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_225,plain,(
    ! [B_46,A_47] :
      ( k2_relat_1(k7_relat_1(B_46,A_47)) = k9_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4687,plain,(
    ! [B_201,A_202] :
      ( k5_relat_1(k7_relat_1(B_201,A_202),k6_relat_1(k9_relat_1(B_201,A_202))) = k7_relat_1(B_201,A_202)
      | ~ v1_relat_1(k7_relat_1(B_201,A_202))
      | ~ v1_relat_1(B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_28])).

tff(c_32,plain,(
    ! [B_24,A_23,C_26] :
      ( r1_tarski(k5_relat_1(k7_relat_1(B_24,A_23),C_26),k5_relat_1(B_24,C_26))
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4704,plain,(
    ! [B_201,A_202] :
      ( r1_tarski(k7_relat_1(B_201,A_202),k5_relat_1(B_201,k6_relat_1(k9_relat_1(B_201,A_202))))
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(B_201,A_202)))
      | ~ v1_relat_1(B_201)
      | ~ v1_relat_1(k7_relat_1(B_201,A_202))
      | ~ v1_relat_1(B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4687,c_32])).

tff(c_4741,plain,(
    ! [B_201,A_202] :
      ( r1_tarski(k7_relat_1(B_201,A_202),k5_relat_1(B_201,k6_relat_1(k9_relat_1(B_201,A_202))))
      | ~ v1_relat_1(k7_relat_1(B_201,A_202))
      | ~ v1_relat_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4704])).

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

tff(c_493,plain,(
    ! [B_68,A_69] :
      ( k5_relat_1(k4_relat_1(B_68),k4_relat_1(A_69)) = k4_relat_1(k5_relat_1(A_69,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2501,plain,(
    ! [A_165,A_166] :
      ( k4_relat_1(k5_relat_1(A_165,k4_relat_1(A_166))) = k5_relat_1(A_166,k4_relat_1(A_165))
      | ~ v1_relat_1(k4_relat_1(A_166))
      | ~ v1_relat_1(A_165)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_493])).

tff(c_2601,plain,(
    ! [A_166,A_27] :
      ( k5_relat_1(A_166,k4_relat_1(k6_relat_1(A_27))) = k4_relat_1(k7_relat_1(k4_relat_1(A_166),A_27))
      | ~ v1_relat_1(k4_relat_1(A_166))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(A_166)
      | ~ v1_relat_1(k4_relat_1(A_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2501])).

tff(c_2623,plain,(
    ! [A_166,A_27] :
      ( k4_relat_1(k7_relat_1(k4_relat_1(A_166),A_27)) = k5_relat_1(A_166,k6_relat_1(A_27))
      | ~ v1_relat_1(A_166)
      | ~ v1_relat_1(k4_relat_1(A_166)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26,c_2601])).

tff(c_39614,plain,
    ( ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_39500])).

tff(c_40060,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_39614])).

tff(c_40063,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k6_relat_1(k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_40060])).

tff(c_40065,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k6_relat_1(k9_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39615,c_38,c_40063])).

tff(c_40068,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4741,c_40065])).

tff(c_40071,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40068])).

tff(c_40074,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_40071])).

tff(c_40078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40074])).

tff(c_40079,plain,
    ( ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_39614])).

tff(c_40427,plain,(
    ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_40079])).

tff(c_40430,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_40427])).

tff(c_40434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39615,c_40430])).

tff(c_40436,plain,(
    v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40079])).

tff(c_40435,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_40079])).

tff(c_40998,plain,(
    ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_40435])).

tff(c_41007,plain,(
    ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_40998])).

tff(c_41016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40436,c_41007])).

tff(c_41017,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_40435])).

tff(c_41021,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_41017])).

tff(c_41025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_41021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.97/9.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.97/9.69  
% 19.97/9.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.97/9.69  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 19.97/9.69  
% 19.97/9.69  %Foreground sorts:
% 19.97/9.69  
% 19.97/9.69  
% 19.97/9.69  %Background operators:
% 19.97/9.69  
% 19.97/9.69  
% 19.97/9.69  %Foreground operators:
% 19.97/9.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.97/9.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.97/9.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.97/9.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.97/9.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.97/9.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.97/9.69  tff('#skF_2', type, '#skF_2': $i).
% 19.97/9.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 19.97/9.69  tff('#skF_1', type, '#skF_1': $i).
% 19.97/9.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.97/9.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.97/9.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 19.97/9.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.97/9.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.97/9.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.97/9.69  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 19.97/9.69  
% 19.97/9.71  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k3_xboole_0(k1_relat_1(B), A), k9_relat_1(k4_relat_1(B), k9_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_relat_1)).
% 19.97/9.71  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 19.97/9.71  tff(f_33, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 19.97/9.71  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 19.97/9.71  tff(f_64, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 19.97/9.71  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 19.97/9.71  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 19.97/9.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 19.97/9.71  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 19.97/9.71  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 19.97/9.71  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(k7_relat_1(B, A), C), k5_relat_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_relat_1)).
% 19.97/9.71  tff(f_73, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 19.97/9.71  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 19.97/9.71  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 19.97/9.71  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 19.97/9.71  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.97/9.71  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.97/9.71  tff(c_6, plain, (![A_5]: (v1_relat_1(k4_relat_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.97/9.71  tff(c_14, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.97/9.71  tff(c_22, plain, (![A_15]: (k1_relat_1(k4_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.97/9.71  tff(c_422, plain, (![A_60, B_61]: (r1_tarski(k1_relat_1(A_60), k1_relat_1(B_61)) | ~r1_tarski(A_60, B_61) | ~v1_relat_1(B_61) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.97/9.71  tff(c_1702, plain, (![A_144, A_145]: (r1_tarski(k1_relat_1(A_144), k2_relat_1(A_145)) | ~r1_tarski(A_144, k4_relat_1(A_145)) | ~v1_relat_1(k4_relat_1(A_145)) | ~v1_relat_1(A_144) | ~v1_relat_1(A_145))), inference(superposition, [status(thm), theory('equality')], [c_22, c_422])).
% 19.97/9.71  tff(c_39424, plain, (![A_713, B_714, A_715]: (r1_tarski(k1_relat_1(A_713), k9_relat_1(B_714, A_715)) | ~r1_tarski(A_713, k4_relat_1(k7_relat_1(B_714, A_715))) | ~v1_relat_1(k4_relat_1(k7_relat_1(B_714, A_715))) | ~v1_relat_1(A_713) | ~v1_relat_1(k7_relat_1(B_714, A_715)) | ~v1_relat_1(B_714))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1702])).
% 19.97/9.71  tff(c_272, plain, (![B_50, A_51]: (k3_xboole_0(k1_relat_1(B_50), A_51)=k1_relat_1(k7_relat_1(B_50, A_51)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.97/9.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.97/9.71  tff(c_320, plain, (![A_54, B_55]: (k3_xboole_0(A_54, k1_relat_1(B_55))=k1_relat_1(k7_relat_1(B_55, A_54)) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_272, c_2])).
% 19.97/9.71  tff(c_36, plain, (~r1_tarski(k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.97/9.71  tff(c_39, plain, (~r1_tarski(k3_xboole_0('#skF_1', k1_relat_1('#skF_2')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 19.97/9.71  tff(c_333, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_320, c_39])).
% 19.97/9.71  tff(c_360, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_333])).
% 19.97/9.71  tff(c_39500, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_39424, c_360])).
% 19.97/9.71  tff(c_39606, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_39500])).
% 19.97/9.71  tff(c_39609, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_39606])).
% 19.97/9.71  tff(c_39613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_39609])).
% 19.97/9.71  tff(c_39615, plain, (v1_relat_1(k4_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_39500])).
% 19.97/9.71  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.97/9.71  tff(c_225, plain, (![B_46, A_47]: (k2_relat_1(k7_relat_1(B_46, A_47))=k9_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.97/9.71  tff(c_28, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.97/9.71  tff(c_4687, plain, (![B_201, A_202]: (k5_relat_1(k7_relat_1(B_201, A_202), k6_relat_1(k9_relat_1(B_201, A_202)))=k7_relat_1(B_201, A_202) | ~v1_relat_1(k7_relat_1(B_201, A_202)) | ~v1_relat_1(B_201))), inference(superposition, [status(thm), theory('equality')], [c_225, c_28])).
% 19.97/9.71  tff(c_32, plain, (![B_24, A_23, C_26]: (r1_tarski(k5_relat_1(k7_relat_1(B_24, A_23), C_26), k5_relat_1(B_24, C_26)) | ~v1_relat_1(C_26) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 19.97/9.71  tff(c_4704, plain, (![B_201, A_202]: (r1_tarski(k7_relat_1(B_201, A_202), k5_relat_1(B_201, k6_relat_1(k9_relat_1(B_201, A_202)))) | ~v1_relat_1(k6_relat_1(k9_relat_1(B_201, A_202))) | ~v1_relat_1(B_201) | ~v1_relat_1(k7_relat_1(B_201, A_202)) | ~v1_relat_1(B_201))), inference(superposition, [status(thm), theory('equality')], [c_4687, c_32])).
% 19.97/9.71  tff(c_4741, plain, (![B_201, A_202]: (r1_tarski(k7_relat_1(B_201, A_202), k5_relat_1(B_201, k6_relat_1(k9_relat_1(B_201, A_202)))) | ~v1_relat_1(k7_relat_1(B_201, A_202)) | ~v1_relat_1(B_201))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4704])).
% 19.97/9.71  tff(c_26, plain, (![A_19]: (k4_relat_1(k6_relat_1(A_19))=k6_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.97/9.71  tff(c_34, plain, (![A_27, B_28]: (k5_relat_1(k6_relat_1(A_27), B_28)=k7_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 19.97/9.71  tff(c_12, plain, (![A_9]: (k4_relat_1(k4_relat_1(A_9))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.97/9.71  tff(c_493, plain, (![B_68, A_69]: (k5_relat_1(k4_relat_1(B_68), k4_relat_1(A_69))=k4_relat_1(k5_relat_1(A_69, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.97/9.71  tff(c_2501, plain, (![A_165, A_166]: (k4_relat_1(k5_relat_1(A_165, k4_relat_1(A_166)))=k5_relat_1(A_166, k4_relat_1(A_165)) | ~v1_relat_1(k4_relat_1(A_166)) | ~v1_relat_1(A_165) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_12, c_493])).
% 19.97/9.71  tff(c_2601, plain, (![A_166, A_27]: (k5_relat_1(A_166, k4_relat_1(k6_relat_1(A_27)))=k4_relat_1(k7_relat_1(k4_relat_1(A_166), A_27)) | ~v1_relat_1(k4_relat_1(A_166)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(A_166) | ~v1_relat_1(k4_relat_1(A_166)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2501])).
% 19.97/9.71  tff(c_2623, plain, (![A_166, A_27]: (k4_relat_1(k7_relat_1(k4_relat_1(A_166), A_27))=k5_relat_1(A_166, k6_relat_1(A_27)) | ~v1_relat_1(A_166) | ~v1_relat_1(k4_relat_1(A_166)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26, c_2601])).
% 19.97/9.71  tff(c_39614, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitRight, [status(thm)], [c_39500])).
% 19.97/9.71  tff(c_40060, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitLeft, [status(thm)], [c_39614])).
% 19.97/9.71  tff(c_40063, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k6_relat_1(k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_40060])).
% 19.97/9.71  tff(c_40065, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k6_relat_1(k9_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_39615, c_38, c_40063])).
% 19.97/9.71  tff(c_40068, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4741, c_40065])).
% 19.97/9.71  tff(c_40071, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40068])).
% 19.97/9.71  tff(c_40074, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_40071])).
% 19.97/9.71  tff(c_40078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_40074])).
% 19.97/9.71  tff(c_40079, plain, (~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_39614])).
% 19.97/9.71  tff(c_40427, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_40079])).
% 19.97/9.71  tff(c_40430, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_40427])).
% 19.97/9.71  tff(c_40434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39615, c_40430])).
% 19.97/9.71  tff(c_40436, plain, (v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_40079])).
% 19.97/9.71  tff(c_40435, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitRight, [status(thm)], [c_40079])).
% 19.97/9.71  tff(c_40998, plain, (~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitLeft, [status(thm)], [c_40435])).
% 19.97/9.71  tff(c_41007, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(resolution, [status(thm)], [c_6, c_40998])).
% 19.97/9.71  tff(c_41016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40436, c_41007])).
% 19.97/9.71  tff(c_41017, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_40435])).
% 19.97/9.71  tff(c_41021, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_41017])).
% 19.97/9.71  tff(c_41025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_41021])).
% 19.97/9.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.97/9.71  
% 19.97/9.71  Inference rules
% 19.97/9.71  ----------------------
% 19.97/9.71  #Ref     : 0
% 19.97/9.71  #Sup     : 10473
% 19.97/9.71  #Fact    : 0
% 19.97/9.71  #Define  : 0
% 19.97/9.71  #Split   : 4
% 19.97/9.71  #Chain   : 0
% 19.97/9.71  #Close   : 0
% 19.97/9.71  
% 19.97/9.71  Ordering : KBO
% 19.97/9.71  
% 19.97/9.71  Simplification rules
% 19.97/9.71  ----------------------
% 19.97/9.71  #Subsume      : 937
% 19.97/9.71  #Demod        : 16560
% 19.97/9.71  #Tautology    : 2395
% 19.97/9.71  #SimpNegUnit  : 0
% 19.97/9.71  #BackRed      : 14
% 19.97/9.71  
% 19.97/9.71  #Partial instantiations: 0
% 19.97/9.71  #Strategies tried      : 1
% 19.97/9.71  
% 19.97/9.71  Timing (in seconds)
% 19.97/9.71  ----------------------
% 19.97/9.71  Preprocessing        : 0.31
% 19.97/9.71  Parsing              : 0.17
% 19.97/9.71  CNF conversion       : 0.02
% 19.97/9.71  Main loop            : 8.62
% 19.97/9.71  Inferencing          : 1.64
% 19.97/9.71  Reduction            : 3.71
% 19.97/9.71  Demodulation         : 3.21
% 19.97/9.71  BG Simplification    : 0.23
% 19.97/9.71  Subsumption          : 2.57
% 19.97/9.71  Abstraction          : 0.30
% 19.97/9.71  MUC search           : 0.00
% 19.97/9.71  Cooper               : 0.00
% 19.97/9.71  Total                : 8.97
% 19.97/9.71  Index Insertion      : 0.00
% 19.97/9.71  Index Deletion       : 0.00
% 19.97/9.71  Index Matching       : 0.00
% 19.97/9.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
