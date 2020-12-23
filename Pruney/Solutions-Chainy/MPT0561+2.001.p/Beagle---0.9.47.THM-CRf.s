%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:13 EST 2020

% Result     : Theorem 18.64s
% Output     : CNFRefutation 18.64s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 375 expanded)
%              Number of leaves         :   34 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  149 ( 681 expanded)
%              Number of equality atoms :   30 ( 208 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k3_xboole_0(k1_relat_1(B),A),k9_relat_1(k4_relat_1(B),k9_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => r1_tarski(k5_relat_1(k7_relat_1(B,A),C),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).

tff(f_75,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] :
      ( v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_17] :
      ( k1_relat_1(k4_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_428,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_relat_1(A_64),k1_relat_1(B_65))
      | ~ r1_tarski(A_64,B_65)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1548,plain,(
    ! [A_144,A_145] :
      ( r1_tarski(k1_relat_1(A_144),k2_relat_1(A_145))
      | ~ r1_tarski(A_144,k4_relat_1(A_145))
      | ~ v1_relat_1(k4_relat_1(A_145))
      | ~ v1_relat_1(A_144)
      | ~ v1_relat_1(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_428])).

tff(c_36325,plain,(
    ! [A_693,B_694,A_695] :
      ( r1_tarski(k1_relat_1(A_693),k9_relat_1(B_694,A_695))
      | ~ r1_tarski(A_693,k4_relat_1(k7_relat_1(B_694,A_695)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(B_694,A_695)))
      | ~ v1_relat_1(A_693)
      | ~ v1_relat_1(k7_relat_1(B_694,A_695))
      | ~ v1_relat_1(B_694) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1548])).

tff(c_340,plain,(
    ! [B_58,A_59] :
      ( k3_xboole_0(k1_relat_1(B_58),A_59) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [B_46,A_47] : k1_setfam_1(k2_tarski(B_46,A_47)) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_6])).

tff(c_366,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,k1_relat_1(B_61)) = k1_relat_1(k7_relat_1(B_61,A_60))
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_189])).

tff(c_38,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1'),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_206,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1',k1_relat_1('#skF_2')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_38])).

tff(c_376,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_206])).

tff(c_403,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_376])).

tff(c_36392,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36325,c_403])).

tff(c_36677,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_36392])).

tff(c_36680,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_36677])).

tff(c_36684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36680])).

tff(c_36686,plain,(
    v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36392])).

tff(c_10,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_294,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(k7_relat_1(B_54,A_55)) = k9_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k6_relat_1(k2_relat_1(A_22))) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4369,plain,(
    ! [B_201,A_202] :
      ( k5_relat_1(k7_relat_1(B_201,A_202),k6_relat_1(k9_relat_1(B_201,A_202))) = k7_relat_1(B_201,A_202)
      | ~ v1_relat_1(k7_relat_1(B_201,A_202))
      | ~ v1_relat_1(B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_30])).

tff(c_34,plain,(
    ! [B_26,A_25,C_28] :
      ( r1_tarski(k5_relat_1(k7_relat_1(B_26,A_25),C_28),k5_relat_1(B_26,C_28))
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4386,plain,(
    ! [B_201,A_202] :
      ( r1_tarski(k7_relat_1(B_201,A_202),k5_relat_1(B_201,k6_relat_1(k9_relat_1(B_201,A_202))))
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(B_201,A_202)))
      | ~ v1_relat_1(B_201)
      | ~ v1_relat_1(k7_relat_1(B_201,A_202))
      | ~ v1_relat_1(B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4369,c_34])).

tff(c_4429,plain,(
    ! [B_201,A_202] :
      ( r1_tarski(k7_relat_1(B_201,A_202),k5_relat_1(B_201,k6_relat_1(k9_relat_1(B_201,A_202))))
      | ~ v1_relat_1(k7_relat_1(B_201,A_202))
      | ~ v1_relat_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4386])).

tff(c_28,plain,(
    ! [A_21] : k4_relat_1(k6_relat_1(A_21)) = k6_relat_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( k5_relat_1(k6_relat_1(A_29),B_30) = k7_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    ! [A_11] :
      ( k4_relat_1(k4_relat_1(A_11)) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_447,plain,(
    ! [B_68,A_69] :
      ( k5_relat_1(k4_relat_1(B_68),k4_relat_1(A_69)) = k4_relat_1(k5_relat_1(A_69,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1706,plain,(
    ! [A_153,A_154] :
      ( k4_relat_1(k5_relat_1(A_153,k4_relat_1(A_154))) = k5_relat_1(A_154,k4_relat_1(A_153))
      | ~ v1_relat_1(k4_relat_1(A_154))
      | ~ v1_relat_1(A_153)
      | ~ v1_relat_1(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_447])).

tff(c_1778,plain,(
    ! [A_154,A_29] :
      ( k5_relat_1(A_154,k4_relat_1(k6_relat_1(A_29))) = k4_relat_1(k7_relat_1(k4_relat_1(A_154),A_29))
      | ~ v1_relat_1(k4_relat_1(A_154))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(A_154)
      | ~ v1_relat_1(k4_relat_1(A_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1706])).

tff(c_1796,plain,(
    ! [A_154,A_29] :
      ( k4_relat_1(k7_relat_1(k4_relat_1(A_154),A_29)) = k5_relat_1(A_154,k6_relat_1(A_29))
      | ~ v1_relat_1(A_154)
      | ~ v1_relat_1(k4_relat_1(A_154)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28,c_1778])).

tff(c_36685,plain,
    ( ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_36392])).

tff(c_36968,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_36685])).

tff(c_36971,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k6_relat_1(k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1796,c_36968])).

tff(c_36973,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k6_relat_1(k9_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36686,c_40,c_36971])).

tff(c_36976,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4429,c_36973])).

tff(c_36979,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36976])).

tff(c_36982,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_36979])).

tff(c_36986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36982])).

tff(c_36987,plain,
    ( ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_36685])).

tff(c_37085,plain,(
    ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_36987])).

tff(c_37088,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_37085])).

tff(c_37092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36686,c_37088])).

tff(c_37094,plain,(
    v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_36987])).

tff(c_37093,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_36987])).

tff(c_37095,plain,(
    ~ v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_37093])).

tff(c_37104,plain,(
    ~ v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_37095])).

tff(c_37113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37094,c_37104])).

tff(c_37114,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_37093])).

tff(c_37118,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_37114])).

tff(c_37122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.64/8.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.64/8.78  
% 18.64/8.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.64/8.78  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 18.64/8.78  
% 18.64/8.78  %Foreground sorts:
% 18.64/8.78  
% 18.64/8.78  
% 18.64/8.78  %Background operators:
% 18.64/8.78  
% 18.64/8.78  
% 18.64/8.78  %Foreground operators:
% 18.64/8.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.64/8.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.64/8.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.64/8.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.64/8.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.64/8.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.64/8.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.64/8.78  tff('#skF_2', type, '#skF_2': $i).
% 18.64/8.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.64/8.78  tff('#skF_1', type, '#skF_1': $i).
% 18.64/8.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.64/8.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.64/8.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.64/8.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.64/8.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.64/8.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.64/8.78  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 18.64/8.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.64/8.78  
% 18.64/8.80  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k3_xboole_0(k1_relat_1(B), A), k9_relat_1(k4_relat_1(B), k9_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_relat_1)).
% 18.64/8.80  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 18.64/8.80  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 18.64/8.80  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 18.64/8.80  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 18.64/8.80  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 18.64/8.80  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 18.64/8.80  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 18.64/8.80  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 18.64/8.80  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 18.64/8.80  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 18.64/8.80  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(k7_relat_1(B, A), C), k5_relat_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_relat_1)).
% 18.64/8.80  tff(f_75, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 18.64/8.80  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 18.64/8.80  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 18.64/8.80  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 18.64/8.80  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.64/8.80  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.64/8.80  tff(c_8, plain, (![A_7]: (v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.64/8.80  tff(c_16, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.64/8.80  tff(c_24, plain, (![A_17]: (k1_relat_1(k4_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.64/8.80  tff(c_428, plain, (![A_64, B_65]: (r1_tarski(k1_relat_1(A_64), k1_relat_1(B_65)) | ~r1_tarski(A_64, B_65) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.64/8.80  tff(c_1548, plain, (![A_144, A_145]: (r1_tarski(k1_relat_1(A_144), k2_relat_1(A_145)) | ~r1_tarski(A_144, k4_relat_1(A_145)) | ~v1_relat_1(k4_relat_1(A_145)) | ~v1_relat_1(A_144) | ~v1_relat_1(A_145))), inference(superposition, [status(thm), theory('equality')], [c_24, c_428])).
% 18.64/8.80  tff(c_36325, plain, (![A_693, B_694, A_695]: (r1_tarski(k1_relat_1(A_693), k9_relat_1(B_694, A_695)) | ~r1_tarski(A_693, k4_relat_1(k7_relat_1(B_694, A_695))) | ~v1_relat_1(k4_relat_1(k7_relat_1(B_694, A_695))) | ~v1_relat_1(A_693) | ~v1_relat_1(k7_relat_1(B_694, A_695)) | ~v1_relat_1(B_694))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1548])).
% 18.64/8.80  tff(c_340, plain, (![B_58, A_59]: (k3_xboole_0(k1_relat_1(B_58), A_59)=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.64/8.80  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.64/8.80  tff(c_151, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.64/8.80  tff(c_183, plain, (![B_46, A_47]: (k1_setfam_1(k2_tarski(B_46, A_47))=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 18.64/8.80  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.64/8.80  tff(c_189, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_183, c_6])).
% 18.64/8.80  tff(c_366, plain, (![A_60, B_61]: (k3_xboole_0(A_60, k1_relat_1(B_61))=k1_relat_1(k7_relat_1(B_61, A_60)) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_340, c_189])).
% 18.64/8.80  tff(c_38, plain, (~r1_tarski(k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.64/8.80  tff(c_206, plain, (~r1_tarski(k3_xboole_0('#skF_1', k1_relat_1('#skF_2')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_38])).
% 18.64/8.80  tff(c_376, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_366, c_206])).
% 18.64/8.80  tff(c_403, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_376])).
% 18.64/8.80  tff(c_36392, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_36325, c_403])).
% 18.64/8.80  tff(c_36677, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_36392])).
% 18.64/8.80  tff(c_36680, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_36677])).
% 18.64/8.80  tff(c_36684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36680])).
% 18.64/8.80  tff(c_36686, plain, (v1_relat_1(k4_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_36392])).
% 18.64/8.80  tff(c_10, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.64/8.80  tff(c_294, plain, (![B_54, A_55]: (k2_relat_1(k7_relat_1(B_54, A_55))=k9_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.64/8.80  tff(c_30, plain, (![A_22]: (k5_relat_1(A_22, k6_relat_1(k2_relat_1(A_22)))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 18.64/8.80  tff(c_4369, plain, (![B_201, A_202]: (k5_relat_1(k7_relat_1(B_201, A_202), k6_relat_1(k9_relat_1(B_201, A_202)))=k7_relat_1(B_201, A_202) | ~v1_relat_1(k7_relat_1(B_201, A_202)) | ~v1_relat_1(B_201))), inference(superposition, [status(thm), theory('equality')], [c_294, c_30])).
% 18.64/8.80  tff(c_34, plain, (![B_26, A_25, C_28]: (r1_tarski(k5_relat_1(k7_relat_1(B_26, A_25), C_28), k5_relat_1(B_26, C_28)) | ~v1_relat_1(C_28) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 18.64/8.80  tff(c_4386, plain, (![B_201, A_202]: (r1_tarski(k7_relat_1(B_201, A_202), k5_relat_1(B_201, k6_relat_1(k9_relat_1(B_201, A_202)))) | ~v1_relat_1(k6_relat_1(k9_relat_1(B_201, A_202))) | ~v1_relat_1(B_201) | ~v1_relat_1(k7_relat_1(B_201, A_202)) | ~v1_relat_1(B_201))), inference(superposition, [status(thm), theory('equality')], [c_4369, c_34])).
% 18.64/8.80  tff(c_4429, plain, (![B_201, A_202]: (r1_tarski(k7_relat_1(B_201, A_202), k5_relat_1(B_201, k6_relat_1(k9_relat_1(B_201, A_202)))) | ~v1_relat_1(k7_relat_1(B_201, A_202)) | ~v1_relat_1(B_201))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4386])).
% 18.64/8.80  tff(c_28, plain, (![A_21]: (k4_relat_1(k6_relat_1(A_21))=k6_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.64/8.80  tff(c_36, plain, (![A_29, B_30]: (k5_relat_1(k6_relat_1(A_29), B_30)=k7_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_94])).
% 18.64/8.80  tff(c_14, plain, (![A_11]: (k4_relat_1(k4_relat_1(A_11))=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.64/8.80  tff(c_447, plain, (![B_68, A_69]: (k5_relat_1(k4_relat_1(B_68), k4_relat_1(A_69))=k4_relat_1(k5_relat_1(A_69, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.64/8.80  tff(c_1706, plain, (![A_153, A_154]: (k4_relat_1(k5_relat_1(A_153, k4_relat_1(A_154)))=k5_relat_1(A_154, k4_relat_1(A_153)) | ~v1_relat_1(k4_relat_1(A_154)) | ~v1_relat_1(A_153) | ~v1_relat_1(A_154))), inference(superposition, [status(thm), theory('equality')], [c_14, c_447])).
% 18.64/8.80  tff(c_1778, plain, (![A_154, A_29]: (k5_relat_1(A_154, k4_relat_1(k6_relat_1(A_29)))=k4_relat_1(k7_relat_1(k4_relat_1(A_154), A_29)) | ~v1_relat_1(k4_relat_1(A_154)) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(A_154) | ~v1_relat_1(k4_relat_1(A_154)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1706])).
% 18.64/8.80  tff(c_1796, plain, (![A_154, A_29]: (k4_relat_1(k7_relat_1(k4_relat_1(A_154), A_29))=k5_relat_1(A_154, k6_relat_1(A_29)) | ~v1_relat_1(A_154) | ~v1_relat_1(k4_relat_1(A_154)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28, c_1778])).
% 18.64/8.80  tff(c_36685, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitRight, [status(thm)], [c_36392])).
% 18.64/8.80  tff(c_36968, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitLeft, [status(thm)], [c_36685])).
% 18.64/8.80  tff(c_36971, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k6_relat_1(k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1796, c_36968])).
% 18.64/8.80  tff(c_36973, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k6_relat_1(k9_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36686, c_40, c_36971])).
% 18.64/8.80  tff(c_36976, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4429, c_36973])).
% 18.64/8.80  tff(c_36979, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36976])).
% 18.64/8.80  tff(c_36982, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_36979])).
% 18.64/8.80  tff(c_36986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36982])).
% 18.64/8.80  tff(c_36987, plain, (~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_36685])).
% 18.64/8.80  tff(c_37085, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_36987])).
% 18.64/8.80  tff(c_37088, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_37085])).
% 18.64/8.80  tff(c_37092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36686, c_37088])).
% 18.64/8.80  tff(c_37094, plain, (v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_36987])).
% 18.64/8.80  tff(c_37093, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitRight, [status(thm)], [c_36987])).
% 18.64/8.80  tff(c_37095, plain, (~v1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))))), inference(splitLeft, [status(thm)], [c_37093])).
% 18.64/8.80  tff(c_37104, plain, (~v1_relat_1(k7_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(resolution, [status(thm)], [c_8, c_37095])).
% 18.64/8.80  tff(c_37113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37094, c_37104])).
% 18.64/8.80  tff(c_37114, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_37093])).
% 18.64/8.80  tff(c_37118, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_37114])).
% 18.64/8.80  tff(c_37122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_37118])).
% 18.64/8.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.64/8.80  
% 18.64/8.80  Inference rules
% 18.64/8.80  ----------------------
% 18.64/8.80  #Ref     : 0
% 18.64/8.80  #Sup     : 9524
% 18.64/8.80  #Fact    : 0
% 18.64/8.80  #Define  : 0
% 18.64/8.80  #Split   : 4
% 18.64/8.80  #Chain   : 0
% 18.64/8.80  #Close   : 0
% 18.64/8.80  
% 18.64/8.80  Ordering : KBO
% 18.64/8.80  
% 18.64/8.80  Simplification rules
% 18.64/8.80  ----------------------
% 18.64/8.80  #Subsume      : 897
% 18.64/8.80  #Demod        : 15704
% 18.64/8.80  #Tautology    : 2253
% 18.64/8.80  #SimpNegUnit  : 0
% 18.64/8.80  #BackRed      : 16
% 18.64/8.80  
% 18.64/8.80  #Partial instantiations: 0
% 18.64/8.80  #Strategies tried      : 1
% 18.64/8.80  
% 18.64/8.80  Timing (in seconds)
% 18.64/8.80  ----------------------
% 18.64/8.80  Preprocessing        : 0.37
% 18.64/8.80  Parsing              : 0.20
% 18.64/8.80  CNF conversion       : 0.02
% 18.64/8.80  Main loop            : 7.64
% 18.64/8.80  Inferencing          : 1.46
% 18.64/8.80  Reduction            : 3.18
% 18.64/8.80  Demodulation         : 2.74
% 18.64/8.80  BG Simplification    : 0.20
% 18.64/8.80  Subsumption          : 2.38
% 18.64/8.80  Abstraction          : 0.25
% 18.64/8.80  MUC search           : 0.00
% 18.64/8.80  Cooper               : 0.00
% 18.64/8.80  Total                : 8.04
% 18.64/8.80  Index Insertion      : 0.00
% 18.64/8.80  Index Deletion       : 0.00
% 18.64/8.80  Index Matching       : 0.00
% 18.64/8.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
