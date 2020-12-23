%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:44 EST 2020

% Result     : Theorem 13.83s
% Output     : CNFRefutation 13.83s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 557 expanded)
%              Number of leaves         :   30 ( 200 expanded)
%              Depth                    :   15
%              Number of atoms          :  128 ( 753 expanded)
%              Number of equality atoms :   95 ( 508 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_85,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_42,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_376,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_401,plain,(
    ! [A_35,B_36] : k3_xboole_0(A_35,k2_xboole_0(A_35,B_36)) = A_35 ),
    inference(resolution,[status(thm)],[c_40,c_376])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_633,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_xboole_0(A_70,C_71)
      | ~ r1_xboole_0(A_70,k2_xboole_0(B_72,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6019,plain,(
    ! [A_203,C_204,B_205] :
      ( r1_xboole_0(A_203,C_204)
      | k3_xboole_0(A_203,k2_xboole_0(B_205,C_204)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_633])).

tff(c_6105,plain,(
    ! [A_206,B_207] :
      ( r1_xboole_0(A_206,B_207)
      | k1_xboole_0 != A_206 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_6019])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6234,plain,(
    ! [A_211,B_212] :
      ( k3_xboole_0(A_211,B_212) = k1_xboole_0
      | k1_xboole_0 != A_211 ) ),
    inference(resolution,[status(thm)],[c_6105,c_6])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6358,plain,(
    ! [A_211,B_212] :
      ( k4_xboole_0(A_211,k1_xboole_0) = k4_xboole_0(A_211,B_212)
      | k1_xboole_0 != A_211 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6234,c_24])).

tff(c_7406,plain,(
    ! [A_225,B_226] :
      ( k4_xboole_0(A_225,B_226) = A_225
      | k1_xboole_0 != A_225 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6358])).

tff(c_26,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8400,plain,(
    ! [A_237,B_238] :
      ( k3_xboole_0(A_237,B_238) = A_237
      | k1_xboole_0 != A_237 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7406,c_26])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_678,plain,(
    ! [A_75,B_76] : k2_xboole_0(A_75,k2_xboole_0(A_75,B_76)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_728,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_678])).

tff(c_741,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_728])).

tff(c_2152,plain,(
    ! [A_120,B_121,C_122] : k3_xboole_0(k2_xboole_0(A_120,B_121),k2_xboole_0(A_120,C_122)) = k2_xboole_0(A_120,k3_xboole_0(B_121,C_122)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2193,plain,(
    ! [A_9,C_122] : k3_xboole_0(A_9,k2_xboole_0(A_9,C_122)) = k2_xboole_0(A_9,k3_xboole_0(A_9,C_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_2152])).

tff(c_2338,plain,(
    ! [A_125,C_126] : k2_xboole_0(A_125,k3_xboole_0(A_125,C_126)) = A_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_2193])).

tff(c_2454,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2338])).

tff(c_9831,plain,(
    ! [B_238] : k2_xboole_0(B_238,k1_xboole_0) = B_238 ),
    inference(superposition,[status(thm),theory(equality)],[c_8400,c_2454])).

tff(c_46,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_265,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | ~ r1_xboole_0(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_271,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_265])).

tff(c_302,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_315,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_271,c_302])).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_317,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_302])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_49,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_14090,plain,(
    ! [C_314] : k3_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k2_xboole_0('#skF_1',C_314)) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_314)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_2152])).

tff(c_2234,plain,(
    ! [B_2,B_121,A_1] : k3_xboole_0(k2_xboole_0(B_2,B_121),k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,k3_xboole_0(B_121,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2152])).

tff(c_14097,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_4',k3_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14090,c_2234])).

tff(c_14279,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9831,c_9831,c_315,c_317,c_4,c_4,c_14097])).

tff(c_14327,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14279,c_315])).

tff(c_87,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_105,plain,(
    ! [B_43,A_44] : r1_tarski(B_43,k2_xboole_0(A_44,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_40])).

tff(c_396,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,k2_xboole_0(A_44,B_43)) = B_43 ),
    inference(resolution,[status(thm)],[c_105,c_376])).

tff(c_270,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_265])).

tff(c_316,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_270,c_302])).

tff(c_526,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_550,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_526])).

tff(c_575,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_550])).

tff(c_183,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_199,plain,(
    ! [A_48] : k3_xboole_0(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_18])).

tff(c_562,plain,(
    ! [A_48] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_526])).

tff(c_579,plain,(
    ! [A_48] : k4_xboole_0(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_562])).

tff(c_851,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_892,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_851])).

tff(c_905,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_892])).

tff(c_1444,plain,(
    ! [A_101,B_102,C_103] : k4_xboole_0(k4_xboole_0(A_101,B_102),C_103) = k4_xboole_0(A_101,k2_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1478,plain,(
    ! [A_16,C_103] : k4_xboole_0(A_16,k2_xboole_0(A_16,C_103)) = k4_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_1444])).

tff(c_1533,plain,(
    ! [A_104,C_105] : k4_xboole_0(A_104,k2_xboole_0(A_104,C_105)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_1478])).

tff(c_1592,plain,(
    ! [A_106,B_107] : k4_xboole_0(A_106,k2_xboole_0(B_107,A_106)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1533])).

tff(c_1643,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_1592])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k4_xboole_0(A_17,B_18),C_19) = k4_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1461,plain,(
    ! [A_101,B_102,B_23] : k4_xboole_0(A_101,k2_xboole_0(B_102,k4_xboole_0(k4_xboole_0(A_101,B_102),B_23))) = k3_xboole_0(k4_xboole_0(A_101,B_102),B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_1444,c_26])).

tff(c_20280,plain,(
    ! [A_377,B_378,B_379] : k4_xboole_0(A_377,k2_xboole_0(B_378,k4_xboole_0(A_377,k2_xboole_0(B_378,B_379)))) = k3_xboole_0(k4_xboole_0(A_377,B_378),B_379) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1461])).

tff(c_20498,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1643,c_20280])).

tff(c_20569,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_9831,c_575,c_4,c_20498])).

tff(c_2398,plain,(
    ! [A_125,C_126] : r1_tarski(k3_xboole_0(A_125,C_126),A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_2338,c_105])).

tff(c_20674,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20569,c_2398])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20724,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20674,c_16])).

tff(c_9833,plain,(
    ! [B_249,A_250] :
      ( k2_xboole_0(B_249,A_250) = B_249
      | k1_xboole_0 != A_250 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8400,c_2454])).

tff(c_11160,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9833])).

tff(c_109,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_1146,plain,(
    ! [A_90,B_91,C_92] : k2_xboole_0(k2_xboole_0(A_90,B_91),C_92) = k2_xboole_0(A_90,k2_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7780,plain,(
    ! [C_233,A_234,B_235] : k2_xboole_0(C_233,k2_xboole_0(A_234,B_235)) = k2_xboole_0(A_234,k2_xboole_0(B_235,C_233)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_2])).

tff(c_30660,plain,(
    ! [A_465,C_466] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_465,C_466)) = k2_xboole_0(C_466,A_465) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_7780])).

tff(c_31023,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),A_3) = k2_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_2454,c_30660])).

tff(c_33708,plain,(
    ! [B_485,A_486] : k2_xboole_0(k3_xboole_0(B_485,A_486),A_486) = A_486 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11160,c_31023])).

tff(c_34058,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20724,c_33708])).

tff(c_13457,plain,(
    ! [B_307,B_308,A_309] : k3_xboole_0(k2_xboole_0(B_307,B_308),k2_xboole_0(A_309,B_307)) = k2_xboole_0(B_307,k3_xboole_0(B_308,A_309)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2152])).

tff(c_13748,plain,(
    ! [B_308] : k3_xboole_0(k2_xboole_0('#skF_2',B_308),k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2',k3_xboole_0(B_308,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_13457])).

tff(c_19532,plain,(
    ! [B_308] : k3_xboole_0(k2_xboole_0('#skF_2',B_308),k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2',k3_xboole_0(B_308,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14279,c_13748])).

tff(c_34281,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34058,c_19532])).

tff(c_34488,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9831,c_14327,c_396,c_4,c_34281])).

tff(c_34490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:39:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.83/5.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.83/5.81  
% 13.83/5.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.83/5.81  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.83/5.81  
% 13.83/5.81  %Foreground sorts:
% 13.83/5.81  
% 13.83/5.81  
% 13.83/5.81  %Background operators:
% 13.83/5.81  
% 13.83/5.81  
% 13.83/5.81  %Foreground operators:
% 13.83/5.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.83/5.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.83/5.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.83/5.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.83/5.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.83/5.81  tff('#skF_2', type, '#skF_2': $i).
% 13.83/5.81  tff('#skF_3', type, '#skF_3': $i).
% 13.83/5.81  tff('#skF_1', type, '#skF_1': $i).
% 13.83/5.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.83/5.81  tff('#skF_4', type, '#skF_4': $i).
% 13.83/5.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.83/5.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.83/5.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.83/5.81  
% 13.83/5.83  tff(f_94, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 13.83/5.83  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.83/5.83  tff(f_85, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.83/5.83  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.83/5.83  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.83/5.83  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 13.83/5.83  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 13.83/5.83  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.83/5.83  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.83/5.83  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.83/5.83  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 13.83/5.83  tff(f_41, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_xboole_1)).
% 13.83/5.83  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.83/5.83  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.83/5.83  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 13.83/5.83  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.83/5.83  tff(f_57, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 13.83/5.83  tff(c_42, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.83/5.83  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.83/5.83  tff(c_40, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.83/5.83  tff(c_376, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.83/5.83  tff(c_401, plain, (![A_35, B_36]: (k3_xboole_0(A_35, k2_xboole_0(A_35, B_36))=A_35)), inference(resolution, [status(thm)], [c_40, c_376])).
% 13.83/5.83  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.83/5.83  tff(c_633, plain, (![A_70, C_71, B_72]: (r1_xboole_0(A_70, C_71) | ~r1_xboole_0(A_70, k2_xboole_0(B_72, C_71)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.83/5.83  tff(c_6019, plain, (![A_203, C_204, B_205]: (r1_xboole_0(A_203, C_204) | k3_xboole_0(A_203, k2_xboole_0(B_205, C_204))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_633])).
% 13.83/5.83  tff(c_6105, plain, (![A_206, B_207]: (r1_xboole_0(A_206, B_207) | k1_xboole_0!=A_206)), inference(superposition, [status(thm), theory('equality')], [c_401, c_6019])).
% 13.83/5.83  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.83/5.83  tff(c_6234, plain, (![A_211, B_212]: (k3_xboole_0(A_211, B_212)=k1_xboole_0 | k1_xboole_0!=A_211)), inference(resolution, [status(thm)], [c_6105, c_6])).
% 13.83/5.83  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.83/5.83  tff(c_6358, plain, (![A_211, B_212]: (k4_xboole_0(A_211, k1_xboole_0)=k4_xboole_0(A_211, B_212) | k1_xboole_0!=A_211)), inference(superposition, [status(thm), theory('equality')], [c_6234, c_24])).
% 13.83/5.83  tff(c_7406, plain, (![A_225, B_226]: (k4_xboole_0(A_225, B_226)=A_225 | k1_xboole_0!=A_225)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6358])).
% 13.83/5.83  tff(c_26, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.83/5.83  tff(c_8400, plain, (![A_237, B_238]: (k3_xboole_0(A_237, B_238)=A_237 | k1_xboole_0!=A_237)), inference(superposition, [status(thm), theory('equality')], [c_7406, c_26])).
% 13.83/5.83  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.83/5.83  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.83/5.83  tff(c_678, plain, (![A_75, B_76]: (k2_xboole_0(A_75, k2_xboole_0(A_75, B_76))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.83/5.83  tff(c_728, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_678])).
% 13.83/5.83  tff(c_741, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_728])).
% 13.83/5.83  tff(c_2152, plain, (![A_120, B_121, C_122]: (k3_xboole_0(k2_xboole_0(A_120, B_121), k2_xboole_0(A_120, C_122))=k2_xboole_0(A_120, k3_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.83/5.83  tff(c_2193, plain, (![A_9, C_122]: (k3_xboole_0(A_9, k2_xboole_0(A_9, C_122))=k2_xboole_0(A_9, k3_xboole_0(A_9, C_122)))), inference(superposition, [status(thm), theory('equality')], [c_741, c_2152])).
% 13.83/5.83  tff(c_2338, plain, (![A_125, C_126]: (k2_xboole_0(A_125, k3_xboole_0(A_125, C_126))=A_125)), inference(demodulation, [status(thm), theory('equality')], [c_401, c_2193])).
% 13.83/5.83  tff(c_2454, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2338])).
% 13.83/5.83  tff(c_9831, plain, (![B_238]: (k2_xboole_0(B_238, k1_xboole_0)=B_238)), inference(superposition, [status(thm), theory('equality')], [c_8400, c_2454])).
% 13.83/5.83  tff(c_46, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.83/5.83  tff(c_265, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | ~r1_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.83/5.83  tff(c_271, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_265])).
% 13.83/5.83  tff(c_302, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.83/5.83  tff(c_315, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_271, c_302])).
% 13.83/5.83  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.83/5.83  tff(c_317, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_302])).
% 13.83/5.83  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.83/5.83  tff(c_48, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.83/5.83  tff(c_49, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 13.83/5.83  tff(c_14090, plain, (![C_314]: (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k2_xboole_0('#skF_1', C_314))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_314)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_2152])).
% 13.83/5.83  tff(c_2234, plain, (![B_2, B_121, A_1]: (k3_xboole_0(k2_xboole_0(B_2, B_121), k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, k3_xboole_0(B_121, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2152])).
% 13.83/5.83  tff(c_14097, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_4', k3_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14090, c_2234])).
% 13.83/5.83  tff(c_14279, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9831, c_9831, c_315, c_317, c_4, c_4, c_14097])).
% 13.83/5.83  tff(c_14327, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14279, c_315])).
% 13.83/5.83  tff(c_87, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.83/5.83  tff(c_105, plain, (![B_43, A_44]: (r1_tarski(B_43, k2_xboole_0(A_44, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_40])).
% 13.83/5.83  tff(c_396, plain, (![B_43, A_44]: (k3_xboole_0(B_43, k2_xboole_0(A_44, B_43))=B_43)), inference(resolution, [status(thm)], [c_105, c_376])).
% 13.83/5.83  tff(c_270, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_265])).
% 13.83/5.83  tff(c_316, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_270, c_302])).
% 13.83/5.83  tff(c_526, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.83/5.83  tff(c_550, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_316, c_526])).
% 13.83/5.83  tff(c_575, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_550])).
% 13.83/5.83  tff(c_183, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.83/5.83  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.83/5.83  tff(c_199, plain, (![A_48]: (k3_xboole_0(k1_xboole_0, A_48)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_183, c_18])).
% 13.83/5.83  tff(c_562, plain, (![A_48]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_48))), inference(superposition, [status(thm), theory('equality')], [c_199, c_526])).
% 13.83/5.83  tff(c_579, plain, (![A_48]: (k4_xboole_0(k1_xboole_0, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_562])).
% 13.83/5.83  tff(c_851, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.83/5.83  tff(c_892, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_851])).
% 13.83/5.83  tff(c_905, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_892])).
% 13.83/5.83  tff(c_1444, plain, (![A_101, B_102, C_103]: (k4_xboole_0(k4_xboole_0(A_101, B_102), C_103)=k4_xboole_0(A_101, k2_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.83/5.83  tff(c_1478, plain, (![A_16, C_103]: (k4_xboole_0(A_16, k2_xboole_0(A_16, C_103))=k4_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_905, c_1444])).
% 13.83/5.83  tff(c_1533, plain, (![A_104, C_105]: (k4_xboole_0(A_104, k2_xboole_0(A_104, C_105))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_579, c_1478])).
% 13.83/5.83  tff(c_1592, plain, (![A_106, B_107]: (k4_xboole_0(A_106, k2_xboole_0(B_107, A_106))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1533])).
% 13.83/5.83  tff(c_1643, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_49, c_1592])).
% 13.83/5.83  tff(c_22, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k4_xboole_0(A_17, B_18), C_19)=k4_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.83/5.83  tff(c_1461, plain, (![A_101, B_102, B_23]: (k4_xboole_0(A_101, k2_xboole_0(B_102, k4_xboole_0(k4_xboole_0(A_101, B_102), B_23)))=k3_xboole_0(k4_xboole_0(A_101, B_102), B_23))), inference(superposition, [status(thm), theory('equality')], [c_1444, c_26])).
% 13.83/5.83  tff(c_20280, plain, (![A_377, B_378, B_379]: (k4_xboole_0(A_377, k2_xboole_0(B_378, k4_xboole_0(A_377, k2_xboole_0(B_378, B_379))))=k3_xboole_0(k4_xboole_0(A_377, B_378), B_379))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1461])).
% 13.83/5.83  tff(c_20498, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1643, c_20280])).
% 13.83/5.83  tff(c_20569, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_575, c_9831, c_575, c_4, c_20498])).
% 13.83/5.83  tff(c_2398, plain, (![A_125, C_126]: (r1_tarski(k3_xboole_0(A_125, C_126), A_125))), inference(superposition, [status(thm), theory('equality')], [c_2338, c_105])).
% 13.83/5.83  tff(c_20674, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20569, c_2398])).
% 13.83/5.83  tff(c_16, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.83/5.83  tff(c_20724, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_20674, c_16])).
% 13.83/5.83  tff(c_9833, plain, (![B_249, A_250]: (k2_xboole_0(B_249, A_250)=B_249 | k1_xboole_0!=A_250)), inference(superposition, [status(thm), theory('equality')], [c_8400, c_2454])).
% 13.83/5.83  tff(c_11160, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_9833])).
% 13.83/5.83  tff(c_109, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 13.83/5.83  tff(c_1146, plain, (![A_90, B_91, C_92]: (k2_xboole_0(k2_xboole_0(A_90, B_91), C_92)=k2_xboole_0(A_90, k2_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.83/5.83  tff(c_7780, plain, (![C_233, A_234, B_235]: (k2_xboole_0(C_233, k2_xboole_0(A_234, B_235))=k2_xboole_0(A_234, k2_xboole_0(B_235, C_233)))), inference(superposition, [status(thm), theory('equality')], [c_1146, c_2])).
% 13.83/5.83  tff(c_30660, plain, (![A_465, C_466]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_465, C_466))=k2_xboole_0(C_466, A_465))), inference(superposition, [status(thm), theory('equality')], [c_109, c_7780])).
% 13.83/5.83  tff(c_31023, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), A_3)=k2_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_2454, c_30660])).
% 13.83/5.83  tff(c_33708, plain, (![B_485, A_486]: (k2_xboole_0(k3_xboole_0(B_485, A_486), A_486)=A_486)), inference(demodulation, [status(thm), theory('equality')], [c_11160, c_31023])).
% 13.83/5.83  tff(c_34058, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_20724, c_33708])).
% 13.83/5.83  tff(c_13457, plain, (![B_307, B_308, A_309]: (k3_xboole_0(k2_xboole_0(B_307, B_308), k2_xboole_0(A_309, B_307))=k2_xboole_0(B_307, k3_xboole_0(B_308, A_309)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2152])).
% 13.83/5.83  tff(c_13748, plain, (![B_308]: (k3_xboole_0(k2_xboole_0('#skF_2', B_308), k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', k3_xboole_0(B_308, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_49, c_13457])).
% 13.83/5.83  tff(c_19532, plain, (![B_308]: (k3_xboole_0(k2_xboole_0('#skF_2', B_308), k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', k3_xboole_0(B_308, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14279, c_13748])).
% 13.83/5.83  tff(c_34281, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34058, c_19532])).
% 13.83/5.83  tff(c_34488, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9831, c_14327, c_396, c_4, c_34281])).
% 13.83/5.83  tff(c_34490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_34488])).
% 13.83/5.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.83/5.83  
% 13.83/5.83  Inference rules
% 13.83/5.83  ----------------------
% 13.83/5.83  #Ref     : 2
% 13.83/5.83  #Sup     : 8988
% 13.83/5.83  #Fact    : 0
% 13.83/5.83  #Define  : 0
% 13.83/5.83  #Split   : 6
% 13.83/5.83  #Chain   : 0
% 13.83/5.83  #Close   : 0
% 13.83/5.83  
% 13.83/5.83  Ordering : KBO
% 13.83/5.83  
% 13.83/5.83  Simplification rules
% 13.83/5.83  ----------------------
% 13.83/5.83  #Subsume      : 1678
% 13.83/5.83  #Demod        : 6637
% 13.83/5.83  #Tautology    : 4123
% 13.83/5.83  #SimpNegUnit  : 133
% 13.83/5.83  #BackRed      : 41
% 13.83/5.83  
% 13.83/5.83  #Partial instantiations: 0
% 13.83/5.83  #Strategies tried      : 1
% 13.83/5.83  
% 13.83/5.83  Timing (in seconds)
% 13.83/5.83  ----------------------
% 13.83/5.84  Preprocessing        : 0.32
% 13.83/5.84  Parsing              : 0.17
% 13.83/5.84  CNF conversion       : 0.02
% 13.83/5.84  Main loop            : 4.73
% 13.83/5.84  Inferencing          : 0.80
% 13.83/5.84  Reduction            : 2.80
% 13.83/5.84  Demodulation         : 2.45
% 13.83/5.84  BG Simplification    : 0.10
% 13.83/5.84  Subsumption          : 0.79
% 13.83/5.84  Abstraction          : 0.15
% 13.83/5.84  MUC search           : 0.00
% 13.83/5.84  Cooper               : 0.00
% 13.83/5.84  Total                : 5.10
% 13.83/5.84  Index Insertion      : 0.00
% 13.83/5.84  Index Deletion       : 0.00
% 13.83/5.84  Index Matching       : 0.00
% 13.83/5.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
