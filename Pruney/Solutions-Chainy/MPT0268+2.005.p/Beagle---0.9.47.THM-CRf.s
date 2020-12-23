%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:34 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 121 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 139 expanded)
%              Number of equality atoms :   46 (  78 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_85,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_96,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_138,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_50,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_289,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_325,plain,(
    ! [B_95] : k3_xboole_0(k1_xboole_0,B_95) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_54])).

tff(c_378,plain,(
    ! [A_99] : k3_xboole_0(A_99,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_325])).

tff(c_46,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_392,plain,(
    ! [A_99] : k5_xboole_0(A_99,k1_xboole_0) = k4_xboole_0(A_99,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_46])).

tff(c_422,plain,(
    ! [A_99] : k5_xboole_0(A_99,k1_xboole_0) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_392])).

tff(c_357,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_325])).

tff(c_314,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_289])).

tff(c_475,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_314])).

tff(c_92,plain,(
    ! [A_44,B_45] :
      ( r1_xboole_0(k1_tarski(A_44),B_45)
      | r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_221,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = A_75
      | ~ r1_xboole_0(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_624,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(k1_tarski(A_120),B_121) = k1_tarski(A_120)
      | r2_hidden(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_92,c_221])).

tff(c_52,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_637,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(k1_tarski(A_120),k1_tarski(A_120)) = k3_xboole_0(k1_tarski(A_120),B_121)
      | r2_hidden(A_120,B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_52])).

tff(c_674,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(k1_tarski(A_122),B_123) = k1_xboole_0
      | r2_hidden(A_122,B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_637])).

tff(c_245,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_260,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_245])).

tff(c_680,plain,(
    ! [B_123,A_122] :
      ( k4_xboole_0(B_123,k1_tarski(A_122)) = k5_xboole_0(B_123,k1_xboole_0)
      | r2_hidden(A_122,B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_260])).

tff(c_734,plain,(
    ! [B_124,A_125] :
      ( k4_xboole_0(B_124,k1_tarski(A_125)) = B_124
      | r2_hidden(A_125,B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_680])).

tff(c_94,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_174,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_760,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_174])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_760])).

tff(c_788,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_84,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_801,plain,(
    ! [A_133,B_134] : k1_enumset1(A_133,A_133,B_134) = k2_tarski(A_133,B_134) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    ! [E_33,B_28,C_29] : r2_hidden(E_33,k1_enumset1(E_33,B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_819,plain,(
    ! [A_135,B_136] : r2_hidden(A_135,k2_tarski(A_135,B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_66])).

tff(c_822,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_819])).

tff(c_789,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_98,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_826,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_98])).

tff(c_1159,plain,(
    ! [D_167,B_168,A_169] :
      ( ~ r2_hidden(D_167,B_168)
      | ~ r2_hidden(D_167,k4_xboole_0(A_169,B_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1179,plain,(
    ! [D_172] :
      ( ~ r2_hidden(D_172,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_172,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_1159])).

tff(c_1183,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_822,c_1179])).

tff(c_1187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_1183])).

tff(c_1188,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1242,plain,(
    ! [A_189,B_190] : k1_enumset1(A_189,A_189,B_190) = k2_tarski(A_189,B_190) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1265,plain,(
    ! [A_193,B_194] : r2_hidden(A_193,k2_tarski(A_193,B_194)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_66])).

tff(c_1268,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1265])).

tff(c_1189,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_100,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1276,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_100])).

tff(c_1307,plain,(
    ! [D_206,B_207,A_208] :
      ( ~ r2_hidden(D_206,B_207)
      | ~ r2_hidden(D_206,k4_xboole_0(A_208,B_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1346,plain,(
    ! [D_214] :
      ( ~ r2_hidden(D_214,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_214,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_1307])).

tff(c_1350,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_1268,c_1346])).

tff(c_1354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_1350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.54  
% 3.11/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 3.11/1.54  
% 3.11/1.54  %Foreground sorts:
% 3.11/1.54  
% 3.11/1.54  
% 3.11/1.54  %Background operators:
% 3.11/1.54  
% 3.11/1.54  
% 3.11/1.54  %Foreground operators:
% 3.11/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.11/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.11/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.11/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.54  tff('#skF_10', type, '#skF_10': $i).
% 3.11/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.11/1.54  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.11/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.11/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.11/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.11/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.11/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.54  
% 3.29/1.56  tff(f_102, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.29/1.56  tff(f_60, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.29/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.29/1.56  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.29/1.56  tff(f_64, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.29/1.56  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.29/1.56  tff(f_96, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.29/1.56  tff(f_68, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.29/1.56  tff(f_85, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/1.56  tff(f_87, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.29/1.56  tff(f_83, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.29/1.56  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.29/1.56  tff(c_96, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.56  tff(c_138, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_96])).
% 3.29/1.56  tff(c_50, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.56  tff(c_289, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.29/1.56  tff(c_54, plain, (![A_24]: (k4_xboole_0(k1_xboole_0, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.56  tff(c_325, plain, (![B_95]: (k3_xboole_0(k1_xboole_0, B_95)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_289, c_54])).
% 3.29/1.56  tff(c_378, plain, (![A_99]: (k3_xboole_0(A_99, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_325])).
% 3.29/1.56  tff(c_46, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.29/1.56  tff(c_392, plain, (![A_99]: (k5_xboole_0(A_99, k1_xboole_0)=k4_xboole_0(A_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_378, c_46])).
% 3.29/1.56  tff(c_422, plain, (![A_99]: (k5_xboole_0(A_99, k1_xboole_0)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_392])).
% 3.29/1.56  tff(c_357, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_325])).
% 3.29/1.56  tff(c_314, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_289])).
% 3.29/1.56  tff(c_475, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_314])).
% 3.29/1.56  tff(c_92, plain, (![A_44, B_45]: (r1_xboole_0(k1_tarski(A_44), B_45) | r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.29/1.56  tff(c_221, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=A_75 | ~r1_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.29/1.56  tff(c_624, plain, (![A_120, B_121]: (k4_xboole_0(k1_tarski(A_120), B_121)=k1_tarski(A_120) | r2_hidden(A_120, B_121))), inference(resolution, [status(thm)], [c_92, c_221])).
% 3.29/1.56  tff(c_52, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.29/1.56  tff(c_637, plain, (![A_120, B_121]: (k4_xboole_0(k1_tarski(A_120), k1_tarski(A_120))=k3_xboole_0(k1_tarski(A_120), B_121) | r2_hidden(A_120, B_121))), inference(superposition, [status(thm), theory('equality')], [c_624, c_52])).
% 3.29/1.56  tff(c_674, plain, (![A_122, B_123]: (k3_xboole_0(k1_tarski(A_122), B_123)=k1_xboole_0 | r2_hidden(A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_637])).
% 3.29/1.56  tff(c_245, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.29/1.56  tff(c_260, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_245])).
% 3.29/1.56  tff(c_680, plain, (![B_123, A_122]: (k4_xboole_0(B_123, k1_tarski(A_122))=k5_xboole_0(B_123, k1_xboole_0) | r2_hidden(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_674, c_260])).
% 3.29/1.56  tff(c_734, plain, (![B_124, A_125]: (k4_xboole_0(B_124, k1_tarski(A_125))=B_124 | r2_hidden(A_125, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_680])).
% 3.29/1.56  tff(c_94, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.56  tff(c_174, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_94])).
% 3.29/1.56  tff(c_760, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_734, c_174])).
% 3.29/1.56  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_760])).
% 3.29/1.56  tff(c_788, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_94])).
% 3.29/1.56  tff(c_84, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.29/1.56  tff(c_801, plain, (![A_133, B_134]: (k1_enumset1(A_133, A_133, B_134)=k2_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.29/1.56  tff(c_66, plain, (![E_33, B_28, C_29]: (r2_hidden(E_33, k1_enumset1(E_33, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.29/1.56  tff(c_819, plain, (![A_135, B_136]: (r2_hidden(A_135, k2_tarski(A_135, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_801, c_66])).
% 3.29/1.56  tff(c_822, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_819])).
% 3.29/1.56  tff(c_789, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_94])).
% 3.29/1.56  tff(c_98, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.56  tff(c_826, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_789, c_98])).
% 3.29/1.56  tff(c_1159, plain, (![D_167, B_168, A_169]: (~r2_hidden(D_167, B_168) | ~r2_hidden(D_167, k4_xboole_0(A_169, B_168)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.29/1.56  tff(c_1179, plain, (![D_172]: (~r2_hidden(D_172, k1_tarski('#skF_10')) | ~r2_hidden(D_172, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_826, c_1159])).
% 3.29/1.56  tff(c_1183, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_822, c_1179])).
% 3.29/1.56  tff(c_1187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_788, c_1183])).
% 3.29/1.56  tff(c_1188, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_96])).
% 3.29/1.56  tff(c_1242, plain, (![A_189, B_190]: (k1_enumset1(A_189, A_189, B_190)=k2_tarski(A_189, B_190))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.29/1.56  tff(c_1265, plain, (![A_193, B_194]: (r2_hidden(A_193, k2_tarski(A_193, B_194)))), inference(superposition, [status(thm), theory('equality')], [c_1242, c_66])).
% 3.29/1.56  tff(c_1268, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_1265])).
% 3.29/1.56  tff(c_1189, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_96])).
% 3.29/1.56  tff(c_100, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.56  tff(c_1276, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_100])).
% 3.29/1.56  tff(c_1307, plain, (![D_206, B_207, A_208]: (~r2_hidden(D_206, B_207) | ~r2_hidden(D_206, k4_xboole_0(A_208, B_207)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.29/1.56  tff(c_1346, plain, (![D_214]: (~r2_hidden(D_214, k1_tarski('#skF_10')) | ~r2_hidden(D_214, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1276, c_1307])).
% 3.29/1.56  tff(c_1350, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_1268, c_1346])).
% 3.29/1.56  tff(c_1354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1188, c_1350])).
% 3.29/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.56  
% 3.29/1.56  Inference rules
% 3.29/1.56  ----------------------
% 3.29/1.56  #Ref     : 0
% 3.29/1.56  #Sup     : 310
% 3.29/1.56  #Fact    : 0
% 3.29/1.56  #Define  : 0
% 3.29/1.56  #Split   : 2
% 3.29/1.56  #Chain   : 0
% 3.29/1.56  #Close   : 0
% 3.29/1.56  
% 3.29/1.56  Ordering : KBO
% 3.29/1.56  
% 3.29/1.56  Simplification rules
% 3.29/1.56  ----------------------
% 3.29/1.56  #Subsume      : 34
% 3.29/1.56  #Demod        : 84
% 3.29/1.56  #Tautology    : 210
% 3.29/1.56  #SimpNegUnit  : 1
% 3.29/1.56  #BackRed      : 2
% 3.29/1.56  
% 3.29/1.56  #Partial instantiations: 0
% 3.29/1.56  #Strategies tried      : 1
% 3.29/1.56  
% 3.29/1.56  Timing (in seconds)
% 3.29/1.56  ----------------------
% 3.29/1.56  Preprocessing        : 0.33
% 3.29/1.56  Parsing              : 0.16
% 3.29/1.56  CNF conversion       : 0.03
% 3.29/1.56  Main loop            : 0.38
% 3.29/1.56  Inferencing          : 0.14
% 3.29/1.56  Reduction            : 0.13
% 3.29/1.56  Demodulation         : 0.10
% 3.29/1.56  BG Simplification    : 0.02
% 3.29/1.56  Subsumption          : 0.06
% 3.29/1.56  Abstraction          : 0.02
% 3.29/1.56  MUC search           : 0.00
% 3.29/1.56  Cooper               : 0.00
% 3.29/1.56  Total                : 0.74
% 3.29/1.56  Index Insertion      : 0.00
% 3.29/1.56  Index Deletion       : 0.00
% 3.29/1.56  Index Matching       : 0.00
% 3.29/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
