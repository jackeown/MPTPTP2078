%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:43 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 315 expanded)
%              Number of leaves         :   24 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  114 ( 398 expanded)
%              Number of equality atoms :   70 ( 232 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_290,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_314,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_16,c_290])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_717,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_879,plain,(
    ! [A_67,B_68] : r1_tarski(k3_xboole_0(A_67,B_68),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_16])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_959,plain,(
    ! [A_71,B_72] : k2_xboole_0(k3_xboole_0(A_71,B_72),A_71) = A_71 ),
    inference(resolution,[status(thm)],[c_879,c_14])).

tff(c_1017,plain,(
    ! [A_1,B_72] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_72)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_959])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_115,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(A_35,B_36)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_115])).

tff(c_168,plain,(
    ! [A_37] : r1_tarski(k1_xboole_0,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_16])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    ! [A_37] : k4_xboole_0(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_168,c_12])).

tff(c_774,plain,(
    ! [B_62] : k3_xboole_0(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_172])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_779,plain,(
    ! [B_62] : k3_xboole_0(B_62,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_4])).

tff(c_154,plain,(
    ! [A_35] : r1_tarski(k1_xboole_0,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_16])).

tff(c_315,plain,(
    ! [A_47] : k2_xboole_0(k1_xboole_0,A_47) = A_47 ),
    inference(resolution,[status(thm)],[c_154,c_290])).

tff(c_159,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_321,plain,(
    ! [A_47] : k4_xboole_0(A_47,A_47) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_159])).

tff(c_1800,plain,(
    ! [A_95] : k4_xboole_0(A_95,k1_xboole_0) = k3_xboole_0(A_95,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_717])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1842,plain,(
    ! [A_95] : k4_xboole_0(A_95,k3_xboole_0(A_95,A_95)) = k3_xboole_0(A_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1800,c_20])).

tff(c_1915,plain,(
    ! [A_97] : k4_xboole_0(A_97,k3_xboole_0(A_97,A_97)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_1842])).

tff(c_622,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | k4_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_629,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = B_57
      | k4_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_622,c_14])).

tff(c_1923,plain,(
    ! [A_97] : k2_xboole_0(A_97,k3_xboole_0(A_97,A_97)) = k3_xboole_0(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_629])).

tff(c_1968,plain,(
    ! [A_97] : k3_xboole_0(A_97,A_97) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_1923])).

tff(c_748,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = k3_xboole_0(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_717])).

tff(c_1982,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_748])).

tff(c_906,plain,(
    ! [B_4,A_3] : r1_tarski(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_879])).

tff(c_739,plain,(
    ! [A_60,B_61] : r1_tarski(k3_xboole_0(A_60,B_61),A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_16])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1037,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_xboole_0 = A_73
      | ~ r1_xboole_0(B_74,C_75)
      | ~ r1_tarski(A_73,C_75)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1109,plain,(
    ! [A_78] :
      ( k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,'#skF_2')
      | ~ r1_tarski(A_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_1037])).

tff(c_3362,plain,(
    ! [B_118] :
      ( k3_xboole_0('#skF_2',B_118) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_118),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_739,c_1109])).

tff(c_3387,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_906,c_3362])).

tff(c_720,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,k4_xboole_0(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_20])).

tff(c_3397,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_4')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3387,c_720])).

tff(c_3438,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_3397])).

tff(c_1242,plain,(
    ! [A_81,B_82] : k2_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_959])).

tff(c_1289,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1242])).

tff(c_3461,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_2') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3438,c_1289])).

tff(c_3487,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_3461])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_33,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_76,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(B_34,A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_24])).

tff(c_140,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_128])).

tff(c_797,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k4_xboole_0(A_63,B_64),C_65)
      | ~ r1_tarski(A_63,k2_xboole_0(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2568,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_xboole_0(k4_xboole_0(A_104,B_105),C_106) = C_106
      | ~ r1_tarski(A_104,k2_xboole_0(B_105,C_106)) ) ),
    inference(resolution,[status(thm)],[c_797,c_14])).

tff(c_2673,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_140,c_2568])).

tff(c_2825,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2673])).

tff(c_3496,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3487,c_2825])).

tff(c_545,plain,(
    ! [A_54,B_55] : k2_xboole_0(k4_xboole_0(A_54,B_55),A_54) = A_54 ),
    inference(resolution,[status(thm)],[c_16,c_290])).

tff(c_564,plain,(
    ! [A_54,B_55] : k2_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_2])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_459,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_471,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_459])).

tff(c_1683,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,k4_xboole_0(A_93,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_20])).

tff(c_1729,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_1683])).

tff(c_1784,plain,(
    r1_tarski(k4_xboole_0('#skF_3',k1_xboole_0),k4_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1729,c_906])).

tff(c_3164,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_1784])).

tff(c_3169,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_3164,c_14])).

tff(c_3175,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_3169])).

tff(c_91,plain,(
    ! [A_30,B_29] : r1_tarski(A_30,k2_xboole_0(B_29,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_24])).

tff(c_2219,plain,(
    ! [A_100,B_101,C_102] :
      ( k4_xboole_0(k4_xboole_0(A_100,B_101),C_102) = k1_xboole_0
      | ~ r1_tarski(A_100,k2_xboole_0(B_101,C_102)) ) ),
    inference(resolution,[status(thm)],[c_797,c_12])).

tff(c_4499,plain,(
    ! [A_127] :
      ( k4_xboole_0(k4_xboole_0(A_127,'#skF_1'),'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_127,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_2219])).

tff(c_4530,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_4499])).

tff(c_4552,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_4530])).

tff(c_4569,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4552,c_629])).

tff(c_4599,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3496,c_4569])).

tff(c_4601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n015.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:19:38 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.87  
% 4.60/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.87  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.60/1.87  
% 4.60/1.87  %Foreground sorts:
% 4.60/1.87  
% 4.60/1.87  
% 4.60/1.87  %Background operators:
% 4.60/1.87  
% 4.60/1.87  
% 4.60/1.87  %Foreground operators:
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.60/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.60/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.60/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.60/1.87  
% 4.60/1.89  tff(f_68, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 4.60/1.89  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.60/1.89  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.60/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.60/1.89  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.60/1.89  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.60/1.89  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.60/1.89  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.60/1.89  tff(f_57, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 4.60/1.89  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.60/1.89  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.60/1.89  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.60/1.89  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.60/1.89  tff(c_290, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.89  tff(c_314, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_16, c_290])).
% 4.60/1.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.60/1.89  tff(c_717, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.89  tff(c_879, plain, (![A_67, B_68]: (r1_tarski(k3_xboole_0(A_67, B_68), A_67))), inference(superposition, [status(thm), theory('equality')], [c_717, c_16])).
% 4.60/1.89  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.89  tff(c_959, plain, (![A_71, B_72]: (k2_xboole_0(k3_xboole_0(A_71, B_72), A_71)=A_71)), inference(resolution, [status(thm)], [c_879, c_14])).
% 4.60/1.89  tff(c_1017, plain, (![A_1, B_72]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_72))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_959])).
% 4.60/1.89  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.60/1.89  tff(c_115, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.89  tff(c_149, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(A_35, B_36))=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_115])).
% 4.60/1.89  tff(c_168, plain, (![A_37]: (r1_tarski(k1_xboole_0, A_37))), inference(superposition, [status(thm), theory('equality')], [c_149, c_16])).
% 4.60/1.89  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.89  tff(c_172, plain, (![A_37]: (k4_xboole_0(k1_xboole_0, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_168, c_12])).
% 4.60/1.89  tff(c_774, plain, (![B_62]: (k3_xboole_0(k1_xboole_0, B_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_717, c_172])).
% 4.60/1.89  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.60/1.89  tff(c_779, plain, (![B_62]: (k3_xboole_0(B_62, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_774, c_4])).
% 4.60/1.89  tff(c_154, plain, (![A_35]: (r1_tarski(k1_xboole_0, A_35))), inference(superposition, [status(thm), theory('equality')], [c_149, c_16])).
% 4.60/1.89  tff(c_315, plain, (![A_47]: (k2_xboole_0(k1_xboole_0, A_47)=A_47)), inference(resolution, [status(thm)], [c_154, c_290])).
% 4.60/1.89  tff(c_159, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 4.60/1.89  tff(c_321, plain, (![A_47]: (k4_xboole_0(A_47, A_47)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_315, c_159])).
% 4.60/1.89  tff(c_1800, plain, (![A_95]: (k4_xboole_0(A_95, k1_xboole_0)=k3_xboole_0(A_95, A_95))), inference(superposition, [status(thm), theory('equality')], [c_321, c_717])).
% 4.60/1.89  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.89  tff(c_1842, plain, (![A_95]: (k4_xboole_0(A_95, k3_xboole_0(A_95, A_95))=k3_xboole_0(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1800, c_20])).
% 4.60/1.89  tff(c_1915, plain, (![A_97]: (k4_xboole_0(A_97, k3_xboole_0(A_97, A_97))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_779, c_1842])).
% 4.60/1.89  tff(c_622, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | k4_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.89  tff(c_629, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=B_57 | k4_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_622, c_14])).
% 4.60/1.89  tff(c_1923, plain, (![A_97]: (k2_xboole_0(A_97, k3_xboole_0(A_97, A_97))=k3_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_629])).
% 4.60/1.89  tff(c_1968, plain, (![A_97]: (k3_xboole_0(A_97, A_97)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_1923])).
% 4.60/1.89  tff(c_748, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=k3_xboole_0(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_321, c_717])).
% 4.60/1.89  tff(c_1982, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_748])).
% 4.60/1.89  tff(c_906, plain, (![B_4, A_3]: (r1_tarski(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_879])).
% 4.60/1.89  tff(c_739, plain, (![A_60, B_61]: (r1_tarski(k3_xboole_0(A_60, B_61), A_60))), inference(superposition, [status(thm), theory('equality')], [c_717, c_16])).
% 4.60/1.89  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.60/1.89  tff(c_1037, plain, (![A_73, B_74, C_75]: (k1_xboole_0=A_73 | ~r1_xboole_0(B_74, C_75) | ~r1_tarski(A_73, C_75) | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.60/1.89  tff(c_1109, plain, (![A_78]: (k1_xboole_0=A_78 | ~r1_tarski(A_78, '#skF_2') | ~r1_tarski(A_78, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_1037])).
% 4.60/1.89  tff(c_3362, plain, (![B_118]: (k3_xboole_0('#skF_2', B_118)=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_2', B_118), '#skF_4'))), inference(resolution, [status(thm)], [c_739, c_1109])).
% 4.60/1.89  tff(c_3387, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_906, c_3362])).
% 4.60/1.89  tff(c_720, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k3_xboole_0(A_60, k4_xboole_0(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_717, c_20])).
% 4.60/1.89  tff(c_3397, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_4'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3387, c_720])).
% 4.60/1.89  tff(c_3438, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_3397])).
% 4.60/1.89  tff(c_1242, plain, (![A_81, B_82]: (k2_xboole_0(A_81, k3_xboole_0(A_81, B_82))=A_81)), inference(superposition, [status(thm), theory('equality')], [c_2, c_959])).
% 4.60/1.89  tff(c_1289, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1242])).
% 4.60/1.89  tff(c_3461, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_2')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3438, c_1289])).
% 4.60/1.89  tff(c_3487, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_3461])).
% 4.60/1.89  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.60/1.89  tff(c_33, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 4.60/1.89  tff(c_76, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.60/1.89  tff(c_128, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(B_34, A_33)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_24])).
% 4.60/1.89  tff(c_140, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_128])).
% 4.60/1.89  tff(c_797, plain, (![A_63, B_64, C_65]: (r1_tarski(k4_xboole_0(A_63, B_64), C_65) | ~r1_tarski(A_63, k2_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.60/1.89  tff(c_2568, plain, (![A_104, B_105, C_106]: (k2_xboole_0(k4_xboole_0(A_104, B_105), C_106)=C_106 | ~r1_tarski(A_104, k2_xboole_0(B_105, C_106)))), inference(resolution, [status(thm)], [c_797, c_14])).
% 4.60/1.89  tff(c_2673, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_140, c_2568])).
% 4.60/1.89  tff(c_2825, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_2673])).
% 4.60/1.89  tff(c_3496, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3487, c_2825])).
% 4.60/1.89  tff(c_545, plain, (![A_54, B_55]: (k2_xboole_0(k4_xboole_0(A_54, B_55), A_54)=A_54)), inference(resolution, [status(thm)], [c_16, c_290])).
% 4.60/1.89  tff(c_564, plain, (![A_54, B_55]: (k2_xboole_0(A_54, k4_xboole_0(A_54, B_55))=A_54)), inference(superposition, [status(thm), theory('equality')], [c_545, c_2])).
% 4.60/1.89  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.60/1.89  tff(c_459, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.89  tff(c_471, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_459])).
% 4.60/1.89  tff(c_1683, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k3_xboole_0(A_93, k4_xboole_0(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_717, c_20])).
% 4.60/1.89  tff(c_1729, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_471, c_1683])).
% 4.60/1.89  tff(c_1784, plain, (r1_tarski(k4_xboole_0('#skF_3', k1_xboole_0), k4_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1729, c_906])).
% 4.60/1.89  tff(c_3164, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_1784])).
% 4.60/1.89  tff(c_3169, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_3164, c_14])).
% 4.60/1.89  tff(c_3175, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_564, c_3169])).
% 4.60/1.89  tff(c_91, plain, (![A_30, B_29]: (r1_tarski(A_30, k2_xboole_0(B_29, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_24])).
% 4.60/1.89  tff(c_2219, plain, (![A_100, B_101, C_102]: (k4_xboole_0(k4_xboole_0(A_100, B_101), C_102)=k1_xboole_0 | ~r1_tarski(A_100, k2_xboole_0(B_101, C_102)))), inference(resolution, [status(thm)], [c_797, c_12])).
% 4.60/1.89  tff(c_4499, plain, (![A_127]: (k4_xboole_0(k4_xboole_0(A_127, '#skF_1'), '#skF_2')=k1_xboole_0 | ~r1_tarski(A_127, k2_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_33, c_2219])).
% 4.60/1.89  tff(c_4530, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_4499])).
% 4.60/1.89  tff(c_4552, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_4530])).
% 4.60/1.89  tff(c_4569, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4552, c_629])).
% 4.60/1.89  tff(c_4599, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3496, c_4569])).
% 4.60/1.89  tff(c_4601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4599])).
% 4.60/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.89  
% 4.60/1.89  Inference rules
% 4.60/1.89  ----------------------
% 4.60/1.89  #Ref     : 0
% 4.60/1.89  #Sup     : 1117
% 4.60/1.89  #Fact    : 0
% 4.60/1.89  #Define  : 0
% 4.60/1.89  #Split   : 5
% 4.60/1.89  #Chain   : 0
% 4.60/1.89  #Close   : 0
% 4.60/1.89  
% 4.60/1.89  Ordering : KBO
% 4.60/1.89  
% 4.60/1.89  Simplification rules
% 4.60/1.89  ----------------------
% 4.60/1.89  #Subsume      : 39
% 4.60/1.89  #Demod        : 906
% 4.60/1.89  #Tautology    : 784
% 4.60/1.89  #SimpNegUnit  : 19
% 4.60/1.89  #BackRed      : 18
% 4.60/1.89  
% 4.60/1.89  #Partial instantiations: 0
% 4.60/1.89  #Strategies tried      : 1
% 4.60/1.89  
% 4.60/1.89  Timing (in seconds)
% 4.60/1.89  ----------------------
% 4.60/1.89  Preprocessing        : 0.29
% 4.60/1.89  Parsing              : 0.16
% 4.60/1.89  CNF conversion       : 0.02
% 4.60/1.89  Main loop            : 0.86
% 4.60/1.89  Inferencing          : 0.25
% 4.60/1.89  Reduction            : 0.38
% 4.60/1.89  Demodulation         : 0.30
% 4.60/1.89  BG Simplification    : 0.03
% 4.60/1.89  Subsumption          : 0.15
% 4.60/1.89  Abstraction          : 0.03
% 4.60/1.89  MUC search           : 0.00
% 4.60/1.89  Cooper               : 0.00
% 4.60/1.89  Total                : 1.19
% 4.60/1.89  Index Insertion      : 0.00
% 4.60/1.89  Index Deletion       : 0.00
% 4.60/1.89  Index Matching       : 0.00
% 4.60/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
