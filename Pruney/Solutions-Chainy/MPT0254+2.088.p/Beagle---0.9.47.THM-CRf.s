%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:30 EST 2020

% Result     : Theorem 6.60s
% Output     : CNFRefutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 164 expanded)
%              Number of leaves         :   43 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 152 expanded)
%              Number of equality atoms :   58 ( 125 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_86,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_371,plain,(
    ! [A_94,B_95] : r1_xboole_0(k3_xboole_0(A_94,B_95),k5_xboole_0(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_392,plain,(
    ! [A_18] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_18,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_371])).

tff(c_401,plain,(
    ! [A_18] : r1_xboole_0(k1_xboole_0,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_392])).

tff(c_120,plain,(
    ! [A_71,B_72] : r1_tarski(k3_xboole_0(A_71,B_72),A_71) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_128,plain,(
    ! [B_72] : k3_xboole_0(k1_xboole_0,B_72) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_22])).

tff(c_606,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r1_xboole_0(A_115,B_116)
      | ~ r2_hidden(C_117,k3_xboole_0(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_618,plain,(
    ! [B_72,C_117] :
      ( ~ r1_xboole_0(k1_xboole_0,B_72)
      | ~ r2_hidden(C_117,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_606])).

tff(c_623,plain,(
    ! [C_117] : ~ r2_hidden(C_117,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_618])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_491,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_507,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_491])).

tff(c_1031,plain,(
    ! [A_142,B_143] : k5_xboole_0(k5_xboole_0(A_142,B_143),k3_xboole_0(A_142,B_143)) = k2_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1058,plain,(
    ! [A_142,B_143] : k5_xboole_0(k3_xboole_0(A_142,B_143),k5_xboole_0(A_142,B_143)) = k2_xboole_0(A_142,B_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_4])).

tff(c_788,plain,(
    ! [A_135,B_136,C_137] : k5_xboole_0(k5_xboole_0(A_135,B_136),C_137) = k5_xboole_0(A_135,k5_xboole_0(B_136,C_137)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6794,plain,(
    ! [C_16017,A_16018,B_16019] : k5_xboole_0(C_16017,k5_xboole_0(A_16018,B_16019)) = k5_xboole_0(A_16018,k5_xboole_0(B_16019,C_16017)) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_4])).

tff(c_7026,plain,(
    ! [A_142,B_143] : k5_xboole_0(A_142,k5_xboole_0(B_143,k3_xboole_0(A_142,B_143))) = k2_xboole_0(A_142,B_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_6794])).

tff(c_7882,plain,(
    ! [A_16853,B_16854] : k5_xboole_0(A_16853,k4_xboole_0(B_16854,A_16853)) = k2_xboole_0(A_16853,B_16854) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_7026])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7032,plain,(
    ! [B_143,A_142] : k5_xboole_0(B_143,k5_xboole_0(k3_xboole_0(A_142,B_143),A_142)) = k2_xboole_0(A_142,B_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_6794])).

tff(c_7219,plain,(
    ! [B_143,A_142] : k5_xboole_0(B_143,k4_xboole_0(A_142,B_143)) = k2_xboole_0(A_142,B_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4,c_7032])).

tff(c_8028,plain,(
    ! [B_17020,A_17021] : k2_xboole_0(B_17020,A_17021) = k2_xboole_0(A_17021,B_17020) ),
    inference(superposition,[status(thm),theory(equality)],[c_7882,c_7219])).

tff(c_8083,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8028,c_72])).

tff(c_174,plain,(
    ! [B_84,A_85] : k5_xboole_0(B_84,A_85) = k5_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_190,plain,(
    ! [A_85] : k5_xboole_0(k1_xboole_0,A_85) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_24])).

tff(c_28,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_858,plain,(
    ! [A_26,C_137] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_137)) = k5_xboole_0(k1_xboole_0,C_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_788])).

tff(c_871,plain,(
    ! [A_26,C_137] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_137)) = C_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_858])).

tff(c_8341,plain,(
    ! [A_17519,B_17520] : k5_xboole_0(A_17519,k2_xboole_0(A_17519,B_17520)) = k4_xboole_0(B_17520,A_17519) ),
    inference(superposition,[status(thm),theory(equality)],[c_7882,c_871])).

tff(c_8412,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8083,c_8341])).

tff(c_8470,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8412])).

tff(c_872,plain,(
    ! [A_138,C_139] : k5_xboole_0(A_138,k5_xboole_0(A_138,C_139)) = C_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_858])).

tff(c_944,plain,(
    ! [A_140,B_141] : k5_xboole_0(A_140,k5_xboole_0(B_141,A_140)) = B_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_872])).

tff(c_983,plain,(
    ! [A_26,C_137] : k5_xboole_0(k5_xboole_0(A_26,C_137),C_137) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_944])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_405,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4881,plain,(
    ! [A_13178,B_13179] : k3_xboole_0(k4_xboole_0(A_13178,B_13179),A_13178) = k4_xboole_0(A_13178,B_13179) ),
    inference(resolution,[status(thm)],[c_20,c_405])).

tff(c_5130,plain,(
    ! [A_13679,B_13680] : k3_xboole_0(A_13679,k4_xboole_0(A_13679,B_13680)) = k4_xboole_0(A_13679,B_13680) ),
    inference(superposition,[status(thm),theory(equality)],[c_4881,c_2])).

tff(c_30,plain,(
    ! [A_27,B_28] : k5_xboole_0(k5_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5166,plain,(
    ! [A_13679,B_13680] : k5_xboole_0(k5_xboole_0(A_13679,k4_xboole_0(A_13679,B_13680)),k4_xboole_0(A_13679,B_13680)) = k2_xboole_0(A_13679,k4_xboole_0(A_13679,B_13680)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5130,c_30])).

tff(c_5234,plain,(
    ! [A_13679,B_13680] : k2_xboole_0(A_13679,k4_xboole_0(A_13679,B_13680)) = A_13679 ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_5166])).

tff(c_8562,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8470,c_5234])).

tff(c_8598,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8562])).

tff(c_56,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_463,plain,(
    ! [A_103,B_104] : k1_enumset1(A_103,A_103,B_104) = k2_tarski(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    ! [E_35,B_30,C_31] : r2_hidden(E_35,k1_enumset1(E_35,B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_481,plain,(
    ! [A_105,B_106] : r2_hidden(A_105,k2_tarski(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_38])).

tff(c_484,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_481])).

tff(c_8620,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8598,c_484])).

tff(c_8624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_623,c_8620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:25:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.60/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.34  
% 6.73/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.73/2.34  
% 6.73/2.34  %Foreground sorts:
% 6.73/2.34  
% 6.73/2.34  
% 6.73/2.34  %Background operators:
% 6.73/2.34  
% 6.73/2.34  
% 6.73/2.34  %Foreground operators:
% 6.73/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.73/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.73/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.73/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.73/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.73/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.73/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.73/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.73/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.73/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.73/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.73/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.73/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.73/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.73/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.73/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.73/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.73/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.73/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.73/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.73/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.73/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.73/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.73/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.73/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.73/2.34  
% 6.73/2.35  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.73/2.35  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.73/2.35  tff(f_45, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.73/2.35  tff(f_49, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.73/2.35  tff(f_61, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.73/2.35  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.73/2.35  tff(f_104, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.73/2.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.73/2.35  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.73/2.35  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.73/2.35  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.73/2.35  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.73/2.35  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.73/2.36  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.73/2.36  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.73/2.36  tff(f_86, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.73/2.36  tff(f_88, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.73/2.36  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.73/2.36  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.73/2.36  tff(c_18, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.73/2.36  tff(c_371, plain, (![A_94, B_95]: (r1_xboole_0(k3_xboole_0(A_94, B_95), k5_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.73/2.36  tff(c_392, plain, (![A_18]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_18, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_371])).
% 6.73/2.36  tff(c_401, plain, (![A_18]: (r1_xboole_0(k1_xboole_0, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_392])).
% 6.73/2.36  tff(c_120, plain, (![A_71, B_72]: (r1_tarski(k3_xboole_0(A_71, B_72), A_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.73/2.36  tff(c_22, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.73/2.36  tff(c_128, plain, (![B_72]: (k3_xboole_0(k1_xboole_0, B_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_120, c_22])).
% 6.73/2.36  tff(c_606, plain, (![A_115, B_116, C_117]: (~r1_xboole_0(A_115, B_116) | ~r2_hidden(C_117, k3_xboole_0(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.73/2.36  tff(c_618, plain, (![B_72, C_117]: (~r1_xboole_0(k1_xboole_0, B_72) | ~r2_hidden(C_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_606])).
% 6.73/2.36  tff(c_623, plain, (![C_117]: (~r2_hidden(C_117, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_618])).
% 6.73/2.36  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.73/2.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.73/2.36  tff(c_491, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.73/2.36  tff(c_507, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_491])).
% 6.73/2.36  tff(c_1031, plain, (![A_142, B_143]: (k5_xboole_0(k5_xboole_0(A_142, B_143), k3_xboole_0(A_142, B_143))=k2_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.73/2.36  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.73/2.36  tff(c_1058, plain, (![A_142, B_143]: (k5_xboole_0(k3_xboole_0(A_142, B_143), k5_xboole_0(A_142, B_143))=k2_xboole_0(A_142, B_143))), inference(superposition, [status(thm), theory('equality')], [c_1031, c_4])).
% 6.73/2.36  tff(c_788, plain, (![A_135, B_136, C_137]: (k5_xboole_0(k5_xboole_0(A_135, B_136), C_137)=k5_xboole_0(A_135, k5_xboole_0(B_136, C_137)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.73/2.36  tff(c_6794, plain, (![C_16017, A_16018, B_16019]: (k5_xboole_0(C_16017, k5_xboole_0(A_16018, B_16019))=k5_xboole_0(A_16018, k5_xboole_0(B_16019, C_16017)))), inference(superposition, [status(thm), theory('equality')], [c_788, c_4])).
% 6.73/2.36  tff(c_7026, plain, (![A_142, B_143]: (k5_xboole_0(A_142, k5_xboole_0(B_143, k3_xboole_0(A_142, B_143)))=k2_xboole_0(A_142, B_143))), inference(superposition, [status(thm), theory('equality')], [c_1058, c_6794])).
% 6.73/2.36  tff(c_7882, plain, (![A_16853, B_16854]: (k5_xboole_0(A_16853, k4_xboole_0(B_16854, A_16853))=k2_xboole_0(A_16853, B_16854))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_7026])).
% 6.73/2.36  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.73/2.36  tff(c_7032, plain, (![B_143, A_142]: (k5_xboole_0(B_143, k5_xboole_0(k3_xboole_0(A_142, B_143), A_142))=k2_xboole_0(A_142, B_143))), inference(superposition, [status(thm), theory('equality')], [c_1058, c_6794])).
% 6.73/2.36  tff(c_7219, plain, (![B_143, A_142]: (k5_xboole_0(B_143, k4_xboole_0(A_142, B_143))=k2_xboole_0(A_142, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4, c_7032])).
% 6.73/2.36  tff(c_8028, plain, (![B_17020, A_17021]: (k2_xboole_0(B_17020, A_17021)=k2_xboole_0(A_17021, B_17020))), inference(superposition, [status(thm), theory('equality')], [c_7882, c_7219])).
% 6.73/2.36  tff(c_8083, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8028, c_72])).
% 6.73/2.36  tff(c_174, plain, (![B_84, A_85]: (k5_xboole_0(B_84, A_85)=k5_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.73/2.36  tff(c_190, plain, (![A_85]: (k5_xboole_0(k1_xboole_0, A_85)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_174, c_24])).
% 6.73/2.36  tff(c_28, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.73/2.36  tff(c_858, plain, (![A_26, C_137]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_137))=k5_xboole_0(k1_xboole_0, C_137))), inference(superposition, [status(thm), theory('equality')], [c_28, c_788])).
% 6.73/2.36  tff(c_871, plain, (![A_26, C_137]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_137))=C_137)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_858])).
% 6.73/2.36  tff(c_8341, plain, (![A_17519, B_17520]: (k5_xboole_0(A_17519, k2_xboole_0(A_17519, B_17520))=k4_xboole_0(B_17520, A_17519))), inference(superposition, [status(thm), theory('equality')], [c_7882, c_871])).
% 6.73/2.36  tff(c_8412, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8083, c_8341])).
% 6.73/2.36  tff(c_8470, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8412])).
% 6.73/2.36  tff(c_872, plain, (![A_138, C_139]: (k5_xboole_0(A_138, k5_xboole_0(A_138, C_139))=C_139)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_858])).
% 6.73/2.36  tff(c_944, plain, (![A_140, B_141]: (k5_xboole_0(A_140, k5_xboole_0(B_141, A_140))=B_141)), inference(superposition, [status(thm), theory('equality')], [c_4, c_872])).
% 6.73/2.36  tff(c_983, plain, (![A_26, C_137]: (k5_xboole_0(k5_xboole_0(A_26, C_137), C_137)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_871, c_944])).
% 6.73/2.36  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.73/2.36  tff(c_405, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.73/2.36  tff(c_4881, plain, (![A_13178, B_13179]: (k3_xboole_0(k4_xboole_0(A_13178, B_13179), A_13178)=k4_xboole_0(A_13178, B_13179))), inference(resolution, [status(thm)], [c_20, c_405])).
% 6.73/2.36  tff(c_5130, plain, (![A_13679, B_13680]: (k3_xboole_0(A_13679, k4_xboole_0(A_13679, B_13680))=k4_xboole_0(A_13679, B_13680))), inference(superposition, [status(thm), theory('equality')], [c_4881, c_2])).
% 6.73/2.36  tff(c_30, plain, (![A_27, B_28]: (k5_xboole_0(k5_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.73/2.36  tff(c_5166, plain, (![A_13679, B_13680]: (k5_xboole_0(k5_xboole_0(A_13679, k4_xboole_0(A_13679, B_13680)), k4_xboole_0(A_13679, B_13680))=k2_xboole_0(A_13679, k4_xboole_0(A_13679, B_13680)))), inference(superposition, [status(thm), theory('equality')], [c_5130, c_30])).
% 6.73/2.36  tff(c_5234, plain, (![A_13679, B_13680]: (k2_xboole_0(A_13679, k4_xboole_0(A_13679, B_13680))=A_13679)), inference(demodulation, [status(thm), theory('equality')], [c_983, c_5166])).
% 6.73/2.36  tff(c_8562, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8470, c_5234])).
% 6.73/2.36  tff(c_8598, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8562])).
% 6.73/2.36  tff(c_56, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.73/2.36  tff(c_463, plain, (![A_103, B_104]: (k1_enumset1(A_103, A_103, B_104)=k2_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.73/2.36  tff(c_38, plain, (![E_35, B_30, C_31]: (r2_hidden(E_35, k1_enumset1(E_35, B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.73/2.36  tff(c_481, plain, (![A_105, B_106]: (r2_hidden(A_105, k2_tarski(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_463, c_38])).
% 6.73/2.36  tff(c_484, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_481])).
% 6.73/2.36  tff(c_8620, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8598, c_484])).
% 6.73/2.36  tff(c_8624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_623, c_8620])).
% 6.73/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.36  
% 6.73/2.36  Inference rules
% 6.73/2.36  ----------------------
% 6.73/2.36  #Ref     : 0
% 6.73/2.36  #Sup     : 1708
% 6.73/2.36  #Fact    : 18
% 6.73/2.36  #Define  : 0
% 6.73/2.36  #Split   : 0
% 6.73/2.36  #Chain   : 0
% 6.73/2.36  #Close   : 0
% 6.73/2.36  
% 6.73/2.36  Ordering : KBO
% 6.73/2.36  
% 6.73/2.36  Simplification rules
% 6.73/2.36  ----------------------
% 6.73/2.36  #Subsume      : 117
% 6.73/2.36  #Demod        : 1374
% 6.73/2.36  #Tautology    : 962
% 6.73/2.36  #SimpNegUnit  : 12
% 6.73/2.36  #BackRed      : 7
% 6.73/2.36  
% 6.73/2.36  #Partial instantiations: 6213
% 6.73/2.36  #Strategies tried      : 1
% 6.73/2.36  
% 6.73/2.36  Timing (in seconds)
% 6.73/2.36  ----------------------
% 6.73/2.36  Preprocessing        : 0.33
% 6.73/2.36  Parsing              : 0.17
% 6.73/2.36  CNF conversion       : 0.02
% 6.73/2.36  Main loop            : 1.28
% 6.73/2.36  Inferencing          : 0.56
% 6.73/2.36  Reduction            : 0.46
% 6.73/2.36  Demodulation         : 0.39
% 6.73/2.36  BG Simplification    : 0.05
% 6.73/2.36  Subsumption          : 0.15
% 6.73/2.36  Abstraction          : 0.06
% 6.73/2.36  MUC search           : 0.00
% 6.73/2.36  Cooper               : 0.00
% 6.73/2.36  Total                : 1.64
% 6.73/2.36  Index Insertion      : 0.00
% 6.73/2.36  Index Deletion       : 0.00
% 6.73/2.36  Index Matching       : 0.00
% 6.73/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
