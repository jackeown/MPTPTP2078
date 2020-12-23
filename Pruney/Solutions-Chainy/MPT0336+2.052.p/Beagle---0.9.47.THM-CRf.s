%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:07 EST 2020

% Result     : Theorem 6.51s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 351 expanded)
%              Number of leaves         :   33 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 626 expanded)
%              Number of equality atoms :   44 ( 191 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_119,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = k1_xboole_0
      | ~ r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_119])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_788,plain,(
    ! [A_103,B_104,C_105] :
      ( k3_xboole_0(A_103,k2_xboole_0(B_104,C_105)) = k3_xboole_0(A_103,C_105)
      | ~ r1_xboole_0(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_97,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(A_61,B_62)
      | k3_xboole_0(A_61,B_62) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_100,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_42])).

tff(c_102,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_827,plain,
    ( k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_102])).

tff(c_862,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2,c_827])).

tff(c_868,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_862])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_249,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,B_81)
      | ~ r2_hidden(C_82,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_268,plain,(
    ! [C_86] :
      ( ~ r2_hidden(C_86,'#skF_3')
      | ~ r2_hidden(C_86,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_249])).

tff(c_279,plain,(
    ! [B_87] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_87),'#skF_4')
      | r1_xboole_0('#skF_3',B_87) ) ),
    inference(resolution,[status(thm)],[c_12,c_268])).

tff(c_284,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_279])).

tff(c_323,plain,(
    ! [A_89,B_90,C_91] : k3_xboole_0(k3_xboole_0(A_89,B_90),C_91) = k3_xboole_0(A_89,k3_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_367,plain,(
    ! [C_91] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_91)) = k3_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_323])).

tff(c_1131,plain,(
    ! [A_116,B_117,C_118] : k3_xboole_0(k3_xboole_0(A_116,B_117),k3_xboole_0(A_116,C_118)) = k3_xboole_0(A_116,k3_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1258,plain,(
    ! [C_118] : k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_118)) = k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1131])).

tff(c_1317,plain,(
    ! [C_118] : k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_118)) = k3_xboole_0(k1_xboole_0,C_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_1258])).

tff(c_572,plain,(
    ! [C_96,A_97,B_98] :
      ( r1_xboole_0(k3_xboole_0(C_96,A_97),k3_xboole_0(C_96,B_98))
      | ~ r1_xboole_0(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_669,plain,(
    ! [B_99] :
      ( r1_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',B_99))
      | ~ r1_xboole_0('#skF_3',B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_572])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_697,plain,(
    ! [B_99] :
      ( k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',B_99)) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_99) ) ),
    inference(resolution,[status(thm)],[c_669,c_4])).

tff(c_1477,plain,(
    ! [B_121] :
      ( k3_xboole_0(k1_xboole_0,B_121) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_697])).

tff(c_1485,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_284,c_1477])).

tff(c_695,plain,(
    ! [A_1] :
      ( r1_xboole_0(k1_xboole_0,k3_xboole_0(A_1,'#skF_4'))
      | ~ r1_xboole_0('#skF_3',A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_669])).

tff(c_1499,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1485,c_695])).

tff(c_1581,plain,(
    ~ r1_xboole_0('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1499])).

tff(c_1585,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1581])).

tff(c_1323,plain,(
    ! [C_119] : k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_119)) = k3_xboole_0(k1_xboole_0,C_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_1258])).

tff(c_1361,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1323])).

tff(c_1376,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1361])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k3_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)) = k3_xboole_0(A_10,k3_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1490,plain,(
    ! [C_12] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_12)) = k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1485,c_14])).

tff(c_4320,plain,(
    ! [C_182] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_182)) = k3_xboole_0(k1_xboole_0,C_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1490])).

tff(c_1369,plain,(
    ! [A_1] : k3_xboole_0(k1_xboole_0,k3_xboole_0(A_1,'#skF_4')) = k3_xboole_0(k1_xboole_0,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1323])).

tff(c_4360,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4320,c_1369])).

tff(c_4451,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_1485,c_4360])).

tff(c_4453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1585,c_4451])).

tff(c_4454,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1499])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4475,plain,(
    ! [C_183] : ~ r2_hidden(C_183,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4454,c_8])).

tff(c_4504,plain,(
    ! [A_185] : r1_xboole_0(A_185,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_4475])).

tff(c_4516,plain,(
    ! [A_185] : k3_xboole_0(A_185,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4504,c_4])).

tff(c_170,plain,(
    ! [A_70,B_71] :
      ( r1_xboole_0(k1_tarski(A_70),B_71)
      | r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_177,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(k1_tarski(A_76),B_77) = k1_xboole_0
      | r2_hidden(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_183,plain,(
    ! [B_77,A_76] :
      ( k3_xboole_0(B_77,k1_tarski(A_76)) = k1_xboole_0
      | r2_hidden(A_76,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_2])).

tff(c_5747,plain,(
    ! [B_214,A_215,C_216] : k3_xboole_0(k3_xboole_0(B_214,A_215),C_216) = k3_xboole_0(A_215,k3_xboole_0(B_214,C_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_323])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_92,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_92])).

tff(c_5824,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',k1_tarski('#skF_5'))) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5747,c_96])).

tff(c_6562,plain,
    ( k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_5824])).

tff(c_6575,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_6562])).

tff(c_6576,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_868,c_6575])).

tff(c_258,plain,(
    ! [C_82] :
      ( ~ r2_hidden(C_82,'#skF_3')
      | ~ r2_hidden(C_82,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_249])).

tff(c_6579,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_6576,c_258])).

tff(c_6583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.51/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.33  
% 6.51/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.51/2.33  
% 6.51/2.33  %Foreground sorts:
% 6.51/2.33  
% 6.51/2.33  
% 6.51/2.33  %Background operators:
% 6.51/2.33  
% 6.51/2.33  
% 6.51/2.33  %Foreground operators:
% 6.51/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.51/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.51/2.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.51/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.51/2.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.51/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.51/2.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.51/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.51/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.51/2.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.51/2.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.51/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.51/2.33  tff('#skF_3', type, '#skF_3': $i).
% 6.51/2.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.51/2.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.51/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.51/2.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.51/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.51/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.51/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.51/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.51/2.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.51/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.51/2.33  
% 6.77/2.35  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.77/2.35  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.77/2.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.77/2.35  tff(f_65, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 6.77/2.35  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.77/2.35  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.77/2.35  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_xboole_1)).
% 6.77/2.35  tff(f_61, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 6.77/2.35  tff(f_84, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.77/2.35  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.77/2.35  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.77/2.35  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.35  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.77/2.35  tff(c_119, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=k1_xboole_0 | ~r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.35  tff(c_127, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_119])).
% 6.77/2.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.77/2.35  tff(c_788, plain, (![A_103, B_104, C_105]: (k3_xboole_0(A_103, k2_xboole_0(B_104, C_105))=k3_xboole_0(A_103, C_105) | ~r1_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.77/2.35  tff(c_97, plain, (![A_61, B_62]: (r1_xboole_0(A_61, B_62) | k3_xboole_0(A_61, B_62)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.35  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.77/2.35  tff(c_100, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_97, c_42])).
% 6.77/2.35  tff(c_102, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_100])).
% 6.77/2.35  tff(c_827, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_788, c_102])).
% 6.77/2.35  tff(c_862, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2, c_827])).
% 6.77/2.35  tff(c_868, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_862])).
% 6.77/2.35  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.77/2.35  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.77/2.35  tff(c_249, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, B_81) | ~r2_hidden(C_82, A_80))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.77/2.35  tff(c_268, plain, (![C_86]: (~r2_hidden(C_86, '#skF_3') | ~r2_hidden(C_86, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_249])).
% 6.77/2.35  tff(c_279, plain, (![B_87]: (~r2_hidden('#skF_1'('#skF_3', B_87), '#skF_4') | r1_xboole_0('#skF_3', B_87))), inference(resolution, [status(thm)], [c_12, c_268])).
% 6.77/2.35  tff(c_284, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_279])).
% 6.77/2.35  tff(c_323, plain, (![A_89, B_90, C_91]: (k3_xboole_0(k3_xboole_0(A_89, B_90), C_91)=k3_xboole_0(A_89, k3_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.77/2.35  tff(c_367, plain, (![C_91]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_91))=k3_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_127, c_323])).
% 6.77/2.35  tff(c_1131, plain, (![A_116, B_117, C_118]: (k3_xboole_0(k3_xboole_0(A_116, B_117), k3_xboole_0(A_116, C_118))=k3_xboole_0(A_116, k3_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.35  tff(c_1258, plain, (![C_118]: (k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_118))=k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_118)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_1131])).
% 6.77/2.35  tff(c_1317, plain, (![C_118]: (k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_118))=k3_xboole_0(k1_xboole_0, C_118))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_1258])).
% 6.77/2.35  tff(c_572, plain, (![C_96, A_97, B_98]: (r1_xboole_0(k3_xboole_0(C_96, A_97), k3_xboole_0(C_96, B_98)) | ~r1_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.77/2.35  tff(c_669, plain, (![B_99]: (r1_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', B_99)) | ~r1_xboole_0('#skF_3', B_99))), inference(superposition, [status(thm), theory('equality')], [c_127, c_572])).
% 6.77/2.35  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.35  tff(c_697, plain, (![B_99]: (k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', B_99))=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_99))), inference(resolution, [status(thm)], [c_669, c_4])).
% 6.77/2.35  tff(c_1477, plain, (![B_121]: (k3_xboole_0(k1_xboole_0, B_121)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_121))), inference(demodulation, [status(thm), theory('equality')], [c_1317, c_697])).
% 6.77/2.35  tff(c_1485, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_284, c_1477])).
% 6.77/2.35  tff(c_695, plain, (![A_1]: (r1_xboole_0(k1_xboole_0, k3_xboole_0(A_1, '#skF_4')) | ~r1_xboole_0('#skF_3', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_669])).
% 6.77/2.35  tff(c_1499, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r1_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1485, c_695])).
% 6.77/2.35  tff(c_1581, plain, (~r1_xboole_0('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1499])).
% 6.77/2.35  tff(c_1585, plain, (k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1581])).
% 6.77/2.35  tff(c_1323, plain, (![C_119]: (k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_119))=k3_xboole_0(k1_xboole_0, C_119))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_1258])).
% 6.77/2.35  tff(c_1361, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_127, c_1323])).
% 6.77/2.35  tff(c_1376, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1361])).
% 6.77/2.35  tff(c_14, plain, (![A_10, B_11, C_12]: (k3_xboole_0(k3_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12))=k3_xboole_0(A_10, k3_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.35  tff(c_1490, plain, (![C_12]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_12))=k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_12)))), inference(superposition, [status(thm), theory('equality')], [c_1485, c_14])).
% 6.77/2.35  tff(c_4320, plain, (![C_182]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_182))=k3_xboole_0(k1_xboole_0, C_182))), inference(demodulation, [status(thm), theory('equality')], [c_1317, c_1490])).
% 6.77/2.35  tff(c_1369, plain, (![A_1]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(A_1, '#skF_4'))=k3_xboole_0(k1_xboole_0, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1323])).
% 6.77/2.35  tff(c_4360, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4320, c_1369])).
% 6.77/2.35  tff(c_4451, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_1485, c_4360])).
% 6.77/2.35  tff(c_4453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1585, c_4451])).
% 6.77/2.35  tff(c_4454, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_1499])).
% 6.77/2.35  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.77/2.35  tff(c_4475, plain, (![C_183]: (~r2_hidden(C_183, k1_xboole_0))), inference(resolution, [status(thm)], [c_4454, c_8])).
% 6.77/2.35  tff(c_4504, plain, (![A_185]: (r1_xboole_0(A_185, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_4475])).
% 6.77/2.35  tff(c_4516, plain, (![A_185]: (k3_xboole_0(A_185, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4504, c_4])).
% 6.77/2.35  tff(c_170, plain, (![A_70, B_71]: (r1_xboole_0(k1_tarski(A_70), B_71) | r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.77/2.35  tff(c_177, plain, (![A_76, B_77]: (k3_xboole_0(k1_tarski(A_76), B_77)=k1_xboole_0 | r2_hidden(A_76, B_77))), inference(resolution, [status(thm)], [c_170, c_4])).
% 6.77/2.35  tff(c_183, plain, (![B_77, A_76]: (k3_xboole_0(B_77, k1_tarski(A_76))=k1_xboole_0 | r2_hidden(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_177, c_2])).
% 6.77/2.35  tff(c_5747, plain, (![B_214, A_215, C_216]: (k3_xboole_0(k3_xboole_0(B_214, A_215), C_216)=k3_xboole_0(A_215, k3_xboole_0(B_214, C_216)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_323])).
% 6.77/2.35  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.77/2.35  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 6.77/2.35  tff(c_92, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.77/2.35  tff(c_96, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_49, c_92])).
% 6.77/2.35  tff(c_5824, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', k1_tarski('#skF_5')))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5747, c_96])).
% 6.77/2.35  tff(c_6562, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_5824])).
% 6.77/2.35  tff(c_6575, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4516, c_6562])).
% 6.77/2.35  tff(c_6576, plain, (r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_868, c_6575])).
% 6.77/2.35  tff(c_258, plain, (![C_82]: (~r2_hidden(C_82, '#skF_3') | ~r2_hidden(C_82, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_249])).
% 6.77/2.35  tff(c_6579, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_6576, c_258])).
% 6.77/2.35  tff(c_6583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_6579])).
% 6.77/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.35  
% 6.77/2.35  Inference rules
% 6.77/2.35  ----------------------
% 6.77/2.35  #Ref     : 0
% 6.77/2.35  #Sup     : 1655
% 6.77/2.35  #Fact    : 0
% 6.77/2.35  #Define  : 0
% 6.77/2.35  #Split   : 7
% 6.77/2.35  #Chain   : 0
% 6.77/2.35  #Close   : 0
% 6.77/2.35  
% 6.77/2.35  Ordering : KBO
% 6.77/2.35  
% 6.77/2.35  Simplification rules
% 6.77/2.35  ----------------------
% 6.77/2.35  #Subsume      : 136
% 6.77/2.35  #Demod        : 1262
% 6.77/2.35  #Tautology    : 656
% 6.77/2.35  #SimpNegUnit  : 36
% 6.77/2.35  #BackRed      : 10
% 6.77/2.35  
% 6.77/2.35  #Partial instantiations: 0
% 6.77/2.35  #Strategies tried      : 1
% 6.77/2.35  
% 6.77/2.35  Timing (in seconds)
% 6.77/2.35  ----------------------
% 6.77/2.35  Preprocessing        : 0.32
% 6.77/2.35  Parsing              : 0.17
% 6.77/2.36  CNF conversion       : 0.02
% 6.77/2.36  Main loop            : 1.24
% 6.77/2.36  Inferencing          : 0.34
% 6.77/2.36  Reduction            : 0.61
% 6.77/2.36  Demodulation         : 0.50
% 6.77/2.36  BG Simplification    : 0.05
% 6.77/2.36  Subsumption          : 0.18
% 6.77/2.36  Abstraction          : 0.05
% 6.77/2.36  MUC search           : 0.00
% 6.77/2.36  Cooper               : 0.00
% 6.77/2.36  Total                : 1.60
% 6.77/2.36  Index Insertion      : 0.00
% 6.77/2.36  Index Deletion       : 0.00
% 6.77/2.36  Index Matching       : 0.00
% 6.81/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
