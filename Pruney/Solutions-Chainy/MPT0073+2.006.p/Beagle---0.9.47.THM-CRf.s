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
% DateTime   : Thu Dec  3 09:43:25 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 756 expanded)
%              Number of leaves         :   15 ( 238 expanded)
%              Depth                    :   19
%              Number of atoms          :  179 (1646 expanded)
%              Number of equality atoms :   68 ( 820 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_40,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_33,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_670,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden('#skF_1'(A_85,B_86,C_87),B_86)
      | r2_hidden('#skF_2'(A_85,B_86,C_87),C_87)
      | k3_xboole_0(A_85,B_86) = C_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_642,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(D_74,A_75)
      | ~ r2_hidden(D_74,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_648,plain,(
    ! [D_74,A_9] :
      ( r2_hidden(D_74,A_9)
      | ~ r2_hidden(D_74,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_642])).

tff(c_676,plain,(
    ! [A_85,C_87,A_9] :
      ( r2_hidden('#skF_1'(A_85,k1_xboole_0,C_87),A_9)
      | r2_hidden('#skF_2'(A_85,k1_xboole_0,C_87),C_87)
      | k3_xboole_0(A_85,k1_xboole_0) = C_87 ) ),
    inference(resolution,[status(thm)],[c_670,c_648])).

tff(c_697,plain,(
    ! [A_85,C_87,A_9] :
      ( r2_hidden('#skF_1'(A_85,k1_xboole_0,C_87),A_9)
      | r2_hidden('#skF_2'(A_85,k1_xboole_0,C_87),C_87)
      | k1_xboole_0 = C_87 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_676])).

tff(c_764,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r2_hidden('#skF_1'(A_94,B_95,C_96),C_96)
      | r2_hidden('#skF_2'(A_94,B_95,C_96),C_96)
      | k3_xboole_0(A_94,B_95) = C_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_772,plain,(
    ! [A_85,A_9] :
      ( k3_xboole_0(A_85,k1_xboole_0) = A_9
      | r2_hidden('#skF_2'(A_85,k1_xboole_0,A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(resolution,[status(thm)],[c_697,c_764])).

tff(c_862,plain,(
    ! [A_106,A_107] :
      ( k1_xboole_0 = A_106
      | r2_hidden('#skF_2'(A_107,k1_xboole_0,A_106),A_106)
      | k1_xboole_0 = A_106 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_772])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_43,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_33])).

tff(c_42,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_41,c_24])).

tff(c_126,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden('#skF_1'(A_32,B_33,C_34),B_33)
      | r2_hidden('#skF_2'(A_32,B_33,C_34),C_34)
      | k3_xboole_0(A_32,B_33) = C_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_95,plain,(
    ! [D_20,A_21,B_22] :
      ( r2_hidden(D_20,A_21)
      | ~ r2_hidden(D_20,k3_xboole_0(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [D_20,A_9] :
      ( r2_hidden(D_20,A_9)
      | ~ r2_hidden(D_20,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_95])).

tff(c_136,plain,(
    ! [A_32,C_34,A_9] :
      ( r2_hidden('#skF_1'(A_32,'#skF_4',C_34),A_9)
      | r2_hidden('#skF_2'(A_32,'#skF_4',C_34),C_34)
      | k3_xboole_0(A_32,'#skF_4') = C_34 ) ),
    inference(resolution,[status(thm)],[c_126,c_101])).

tff(c_154,plain,(
    ! [A_32,C_34,A_9] :
      ( r2_hidden('#skF_1'(A_32,'#skF_4',C_34),A_9)
      | r2_hidden('#skF_2'(A_32,'#skF_4',C_34),C_34)
      | C_34 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_136])).

tff(c_220,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r2_hidden('#skF_1'(A_41,B_42,C_43),C_43)
      | r2_hidden('#skF_2'(A_41,B_42,C_43),C_43)
      | k3_xboole_0(A_41,B_42) = C_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_228,plain,(
    ! [A_32,A_9] :
      ( k3_xboole_0(A_32,'#skF_4') = A_9
      | r2_hidden('#skF_2'(A_32,'#skF_4',A_9),A_9)
      | A_9 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_154,c_220])).

tff(c_239,plain,(
    ! [A_9,A_32] :
      ( A_9 = '#skF_4'
      | r2_hidden('#skF_2'(A_32,'#skF_4',A_9),A_9)
      | A_9 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_228])).

tff(c_354,plain,(
    ! [A_52,A_53] :
      ( A_52 = '#skF_4'
      | r2_hidden('#skF_2'(A_53,'#skF_4',A_52),A_52)
      | A_52 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_228])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_22])).

tff(c_30,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_66,plain,(
    k3_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_56])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66])).

tff(c_72,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = '#skF_4'
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_20])).

tff(c_84,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_75])).

tff(c_110,plain,(
    ! [D_28,A_29,B_30] :
      ( r2_hidden(D_28,k3_xboole_0(A_29,B_30))
      | ~ r2_hidden(D_28,B_30)
      | ~ r2_hidden(D_28,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_119,plain,(
    ! [D_28] :
      ( r2_hidden(D_28,'#skF_4')
      | ~ r2_hidden(D_28,'#skF_3')
      | ~ r2_hidden(D_28,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_110])).

tff(c_361,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_2'(A_53,'#skF_4','#skF_3'),'#skF_4')
      | ~ r2_hidden('#skF_2'(A_53,'#skF_4','#skF_3'),'#skF_3')
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_354,c_119])).

tff(c_477,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_2'(A_58,'#skF_4','#skF_3'),'#skF_4')
      | ~ r2_hidden('#skF_2'(A_58,'#skF_4','#skF_3'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_43,c_361])).

tff(c_485,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_2'(A_32,'#skF_4','#skF_3'),'#skF_4')
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_239,c_477])).

tff(c_505,plain,(
    ! [A_59] : r2_hidden('#skF_2'(A_59,'#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_43,c_485])).

tff(c_515,plain,(
    ! [A_59,A_9] : r2_hidden('#skF_2'(A_59,'#skF_4','#skF_3'),A_9) ),
    inference(resolution,[status(thm)],[c_505,c_101])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_242,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45,A_44),A_44)
      | k3_xboole_0(A_44,B_45) = A_44 ) ),
    inference(resolution,[status(thm)],[c_18,c_220])).

tff(c_257,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_2'('#skF_3',B_45,'#skF_3'),'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_3',B_45,'#skF_3'),'#skF_3')
      | k3_xboole_0('#skF_3',B_45) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_242,c_119])).

tff(c_358,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),'#skF_4')
    | k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_354,c_257])).

tff(c_374,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),'#skF_4')
    | '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_358])).

tff(c_375,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_43,c_374])).

tff(c_385,plain,(
    ! [A_9] : r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),A_9) ),
    inference(resolution,[status(thm)],[c_375,c_101])).

tff(c_425,plain,(
    ! [A_57] : r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),A_57) ),
    inference(resolution,[status(thm)],[c_375,c_101])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_428,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),'#skF_4')
    | k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_425,c_10])).

tff(c_449,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_385,c_428])).

tff(c_450,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_449])).

tff(c_476,plain,(
    ! [A_9] : r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_3'),A_9) ),
    inference(resolution,[status(thm)],[c_450,c_101])).

tff(c_594,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r2_hidden('#skF_1'(A_63,B_64,C_65),C_65)
      | ~ r2_hidden('#skF_2'(A_63,B_64,C_65),B_64)
      | ~ r2_hidden('#skF_2'(A_63,B_64,C_65),A_63)
      | k3_xboole_0(A_63,B_64) = C_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_597,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_3'),'#skF_3')
    | k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_476,c_594])).

tff(c_614,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_515,c_515,c_597])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_614])).

tff(c_617,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_621,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_629,plain,(
    k3_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_617,c_621])).

tff(c_650,plain,(
    ! [D_79,A_80,B_81] :
      ( r2_hidden(D_79,k3_xboole_0(A_80,B_81))
      | ~ r2_hidden(D_79,B_81)
      | ~ r2_hidden(D_79,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_665,plain,(
    ! [D_82] :
      ( r2_hidden(D_82,k1_xboole_0)
      | ~ r2_hidden(D_82,'#skF_3')
      | ~ r2_hidden(D_82,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_650])).

tff(c_668,plain,(
    ! [D_82,A_9] :
      ( r2_hidden(D_82,A_9)
      | ~ r2_hidden(D_82,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_665,c_648])).

tff(c_865,plain,(
    ! [A_107,A_9] :
      ( r2_hidden('#skF_2'(A_107,k1_xboole_0,'#skF_3'),A_9)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_862,c_668])).

tff(c_879,plain,(
    ! [A_107,A_9] : r2_hidden('#skF_2'(A_107,k1_xboole_0,'#skF_3'),A_9) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_33,c_865])).

tff(c_1024,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_hidden('#skF_1'(A_123,B_124,C_125),A_123)
      | ~ r2_hidden('#skF_2'(A_123,B_124,C_125),B_124)
      | ~ r2_hidden('#skF_2'(A_123,B_124,C_125),A_123)
      | k3_xboole_0(A_123,B_124) = C_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1042,plain,(
    ! [A_107] :
      ( r2_hidden('#skF_1'(A_107,k1_xboole_0,'#skF_3'),A_107)
      | ~ r2_hidden('#skF_2'(A_107,k1_xboole_0,'#skF_3'),A_107)
      | k3_xboole_0(A_107,k1_xboole_0) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_879,c_1024])).

tff(c_1072,plain,(
    ! [A_107] :
      ( r2_hidden('#skF_1'(A_107,k1_xboole_0,'#skF_3'),A_107)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_879,c_1042])).

tff(c_1082,plain,(
    ! [A_126] : r2_hidden('#skF_1'(A_126,k1_xboole_0,'#skF_3'),A_126) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_1072])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1085,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3',k1_xboole_0,'#skF_3'),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_3',k1_xboole_0,'#skF_3'),'#skF_3')
    | k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1082,c_8])).

tff(c_1106,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_879,c_879,c_1085])).

tff(c_1108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_1106])).

tff(c_1109,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1121,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1109,c_24])).

tff(c_1134,plain,(
    ! [A_128,B_129] :
      ( r1_xboole_0(A_128,B_129)
      | k3_xboole_0(A_128,B_129) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_22])).

tff(c_1110,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1115,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1110])).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1130,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1109,c_32])).

tff(c_1137,plain,(
    k3_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1134,c_1130])).

tff(c_1141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:02:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.49  
% 2.88/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.49  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.88/1.49  
% 2.88/1.49  %Foreground sorts:
% 2.88/1.49  
% 2.88/1.49  
% 2.88/1.49  %Background operators:
% 2.88/1.49  
% 2.88/1.49  
% 2.88/1.49  %Foreground operators:
% 2.88/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.49  
% 2.99/1.51  tff(f_53, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.99/1.51  tff(f_40, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.99/1.51  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.99/1.51  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.99/1.51  tff(c_28, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.99/1.51  tff(c_33, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_28])).
% 2.99/1.51  tff(c_24, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.99/1.51  tff(c_670, plain, (![A_85, B_86, C_87]: (r2_hidden('#skF_1'(A_85, B_86, C_87), B_86) | r2_hidden('#skF_2'(A_85, B_86, C_87), C_87) | k3_xboole_0(A_85, B_86)=C_87)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_642, plain, (![D_74, A_75, B_76]: (r2_hidden(D_74, A_75) | ~r2_hidden(D_74, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_648, plain, (![D_74, A_9]: (r2_hidden(D_74, A_9) | ~r2_hidden(D_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_642])).
% 2.99/1.51  tff(c_676, plain, (![A_85, C_87, A_9]: (r2_hidden('#skF_1'(A_85, k1_xboole_0, C_87), A_9) | r2_hidden('#skF_2'(A_85, k1_xboole_0, C_87), C_87) | k3_xboole_0(A_85, k1_xboole_0)=C_87)), inference(resolution, [status(thm)], [c_670, c_648])).
% 2.99/1.51  tff(c_697, plain, (![A_85, C_87, A_9]: (r2_hidden('#skF_1'(A_85, k1_xboole_0, C_87), A_9) | r2_hidden('#skF_2'(A_85, k1_xboole_0, C_87), C_87) | k1_xboole_0=C_87)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_676])).
% 2.99/1.51  tff(c_764, plain, (![A_94, B_95, C_96]: (~r2_hidden('#skF_1'(A_94, B_95, C_96), C_96) | r2_hidden('#skF_2'(A_94, B_95, C_96), C_96) | k3_xboole_0(A_94, B_95)=C_96)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_772, plain, (![A_85, A_9]: (k3_xboole_0(A_85, k1_xboole_0)=A_9 | r2_hidden('#skF_2'(A_85, k1_xboole_0, A_9), A_9) | k1_xboole_0=A_9)), inference(resolution, [status(thm)], [c_697, c_764])).
% 2.99/1.51  tff(c_862, plain, (![A_106, A_107]: (k1_xboole_0=A_106 | r2_hidden('#skF_2'(A_107, k1_xboole_0, A_106), A_106) | k1_xboole_0=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_772])).
% 2.99/1.51  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.99/1.51  tff(c_41, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 2.99/1.51  tff(c_43, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_33])).
% 2.99/1.51  tff(c_42, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_41, c_24])).
% 2.99/1.51  tff(c_126, plain, (![A_32, B_33, C_34]: (r2_hidden('#skF_1'(A_32, B_33, C_34), B_33) | r2_hidden('#skF_2'(A_32, B_33, C_34), C_34) | k3_xboole_0(A_32, B_33)=C_34)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_95, plain, (![D_20, A_21, B_22]: (r2_hidden(D_20, A_21) | ~r2_hidden(D_20, k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_101, plain, (![D_20, A_9]: (r2_hidden(D_20, A_9) | ~r2_hidden(D_20, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_95])).
% 2.99/1.51  tff(c_136, plain, (![A_32, C_34, A_9]: (r2_hidden('#skF_1'(A_32, '#skF_4', C_34), A_9) | r2_hidden('#skF_2'(A_32, '#skF_4', C_34), C_34) | k3_xboole_0(A_32, '#skF_4')=C_34)), inference(resolution, [status(thm)], [c_126, c_101])).
% 2.99/1.51  tff(c_154, plain, (![A_32, C_34, A_9]: (r2_hidden('#skF_1'(A_32, '#skF_4', C_34), A_9) | r2_hidden('#skF_2'(A_32, '#skF_4', C_34), C_34) | C_34='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_136])).
% 2.99/1.51  tff(c_220, plain, (![A_41, B_42, C_43]: (~r2_hidden('#skF_1'(A_41, B_42, C_43), C_43) | r2_hidden('#skF_2'(A_41, B_42, C_43), C_43) | k3_xboole_0(A_41, B_42)=C_43)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_228, plain, (![A_32, A_9]: (k3_xboole_0(A_32, '#skF_4')=A_9 | r2_hidden('#skF_2'(A_32, '#skF_4', A_9), A_9) | A_9='#skF_4')), inference(resolution, [status(thm)], [c_154, c_220])).
% 2.99/1.51  tff(c_239, plain, (![A_9, A_32]: (A_9='#skF_4' | r2_hidden('#skF_2'(A_32, '#skF_4', A_9), A_9) | A_9='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_228])).
% 2.99/1.51  tff(c_354, plain, (![A_52, A_53]: (A_52='#skF_4' | r2_hidden('#skF_2'(A_53, '#skF_4', A_52), A_52) | A_52='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_228])).
% 2.99/1.51  tff(c_22, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.51  tff(c_60, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_22])).
% 2.99/1.51  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.99/1.51  tff(c_56, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 2.99/1.51  tff(c_66, plain, (k3_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_60, c_56])).
% 2.99/1.51  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_66])).
% 2.99/1.51  tff(c_72, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.99/1.51  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.51  tff(c_75, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)='#skF_4' | ~r1_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_20])).
% 2.99/1.51  tff(c_84, plain, (k3_xboole_0('#skF_3', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_72, c_75])).
% 2.99/1.51  tff(c_110, plain, (![D_28, A_29, B_30]: (r2_hidden(D_28, k3_xboole_0(A_29, B_30)) | ~r2_hidden(D_28, B_30) | ~r2_hidden(D_28, A_29))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_119, plain, (![D_28]: (r2_hidden(D_28, '#skF_4') | ~r2_hidden(D_28, '#skF_3') | ~r2_hidden(D_28, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_110])).
% 2.99/1.51  tff(c_361, plain, (![A_53]: (r2_hidden('#skF_2'(A_53, '#skF_4', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_2'(A_53, '#skF_4', '#skF_3'), '#skF_3') | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_354, c_119])).
% 2.99/1.51  tff(c_477, plain, (![A_58]: (r2_hidden('#skF_2'(A_58, '#skF_4', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_2'(A_58, '#skF_4', '#skF_3'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_43, c_43, c_361])).
% 2.99/1.51  tff(c_485, plain, (![A_32]: (r2_hidden('#skF_2'(A_32, '#skF_4', '#skF_3'), '#skF_4') | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_239, c_477])).
% 2.99/1.51  tff(c_505, plain, (![A_59]: (r2_hidden('#skF_2'(A_59, '#skF_4', '#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_43, c_43, c_485])).
% 2.99/1.51  tff(c_515, plain, (![A_59, A_9]: (r2_hidden('#skF_2'(A_59, '#skF_4', '#skF_3'), A_9))), inference(resolution, [status(thm)], [c_505, c_101])).
% 2.99/1.51  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_242, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45, A_44), A_44) | k3_xboole_0(A_44, B_45)=A_44)), inference(resolution, [status(thm)], [c_18, c_220])).
% 2.99/1.51  tff(c_257, plain, (![B_45]: (r2_hidden('#skF_2'('#skF_3', B_45, '#skF_3'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_3', B_45, '#skF_3'), '#skF_3') | k3_xboole_0('#skF_3', B_45)='#skF_3')), inference(resolution, [status(thm)], [c_242, c_119])).
% 2.99/1.51  tff(c_358, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), '#skF_4') | k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_354, c_257])).
% 2.99/1.51  tff(c_374, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), '#skF_4') | '#skF_3'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_358])).
% 2.99/1.51  tff(c_375, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_43, c_43, c_374])).
% 2.99/1.51  tff(c_385, plain, (![A_9]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), A_9))), inference(resolution, [status(thm)], [c_375, c_101])).
% 2.99/1.51  tff(c_425, plain, (![A_57]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), A_57))), inference(resolution, [status(thm)], [c_375, c_101])).
% 2.99/1.51  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_428, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), '#skF_4') | k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_425, c_10])).
% 2.99/1.51  tff(c_449, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_385, c_428])).
% 2.99/1.51  tff(c_450, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_43, c_449])).
% 2.99/1.51  tff(c_476, plain, (![A_9]: (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_3'), A_9))), inference(resolution, [status(thm)], [c_450, c_101])).
% 2.99/1.51  tff(c_594, plain, (![A_63, B_64, C_65]: (~r2_hidden('#skF_1'(A_63, B_64, C_65), C_65) | ~r2_hidden('#skF_2'(A_63, B_64, C_65), B_64) | ~r2_hidden('#skF_2'(A_63, B_64, C_65), A_63) | k3_xboole_0(A_63, B_64)=C_65)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_597, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_3'), '#skF_3') | k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_476, c_594])).
% 2.99/1.51  tff(c_614, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_515, c_515, c_597])).
% 2.99/1.51  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_614])).
% 2.99/1.51  tff(c_617, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.99/1.51  tff(c_621, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.51  tff(c_629, plain, (k3_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_617, c_621])).
% 2.99/1.51  tff(c_650, plain, (![D_79, A_80, B_81]: (r2_hidden(D_79, k3_xboole_0(A_80, B_81)) | ~r2_hidden(D_79, B_81) | ~r2_hidden(D_79, A_80))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_665, plain, (![D_82]: (r2_hidden(D_82, k1_xboole_0) | ~r2_hidden(D_82, '#skF_3') | ~r2_hidden(D_82, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_629, c_650])).
% 2.99/1.51  tff(c_668, plain, (![D_82, A_9]: (r2_hidden(D_82, A_9) | ~r2_hidden(D_82, '#skF_3'))), inference(resolution, [status(thm)], [c_665, c_648])).
% 2.99/1.51  tff(c_865, plain, (![A_107, A_9]: (r2_hidden('#skF_2'(A_107, k1_xboole_0, '#skF_3'), A_9) | k1_xboole_0='#skF_3')), inference(resolution, [status(thm)], [c_862, c_668])).
% 2.99/1.51  tff(c_879, plain, (![A_107, A_9]: (r2_hidden('#skF_2'(A_107, k1_xboole_0, '#skF_3'), A_9))), inference(negUnitSimplification, [status(thm)], [c_33, c_33, c_865])).
% 2.99/1.51  tff(c_1024, plain, (![A_123, B_124, C_125]: (r2_hidden('#skF_1'(A_123, B_124, C_125), A_123) | ~r2_hidden('#skF_2'(A_123, B_124, C_125), B_124) | ~r2_hidden('#skF_2'(A_123, B_124, C_125), A_123) | k3_xboole_0(A_123, B_124)=C_125)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_1042, plain, (![A_107]: (r2_hidden('#skF_1'(A_107, k1_xboole_0, '#skF_3'), A_107) | ~r2_hidden('#skF_2'(A_107, k1_xboole_0, '#skF_3'), A_107) | k3_xboole_0(A_107, k1_xboole_0)='#skF_3')), inference(resolution, [status(thm)], [c_879, c_1024])).
% 2.99/1.51  tff(c_1072, plain, (![A_107]: (r2_hidden('#skF_1'(A_107, k1_xboole_0, '#skF_3'), A_107) | k1_xboole_0='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_879, c_1042])).
% 2.99/1.51  tff(c_1082, plain, (![A_126]: (r2_hidden('#skF_1'(A_126, k1_xboole_0, '#skF_3'), A_126))), inference(negUnitSimplification, [status(thm)], [c_33, c_1072])).
% 2.99/1.51  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.51  tff(c_1085, plain, (~r2_hidden('#skF_2'('#skF_3', k1_xboole_0, '#skF_3'), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_3', k1_xboole_0, '#skF_3'), '#skF_3') | k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_1082, c_8])).
% 2.99/1.51  tff(c_1106, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_879, c_879, c_1085])).
% 2.99/1.51  tff(c_1108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_1106])).
% 2.99/1.51  tff(c_1109, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 2.99/1.51  tff(c_1121, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1109, c_24])).
% 2.99/1.51  tff(c_1134, plain, (![A_128, B_129]: (r1_xboole_0(A_128, B_129) | k3_xboole_0(A_128, B_129)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_22])).
% 2.99/1.51  tff(c_1110, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.99/1.51  tff(c_1115, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1110])).
% 2.99/1.51  tff(c_32, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.99/1.51  tff(c_1130, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1109, c_32])).
% 2.99/1.51  tff(c_1137, plain, (k3_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_1134, c_1130])).
% 2.99/1.51  tff(c_1141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1137])).
% 2.99/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.51  
% 2.99/1.51  Inference rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Ref     : 0
% 2.99/1.51  #Sup     : 219
% 2.99/1.51  #Fact    : 0
% 2.99/1.51  #Define  : 0
% 2.99/1.51  #Split   : 3
% 2.99/1.51  #Chain   : 0
% 2.99/1.51  #Close   : 0
% 2.99/1.51  
% 2.99/1.51  Ordering : KBO
% 2.99/1.51  
% 2.99/1.51  Simplification rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Subsume      : 41
% 2.99/1.51  #Demod        : 109
% 2.99/1.51  #Tautology    : 73
% 2.99/1.51  #SimpNegUnit  : 19
% 2.99/1.51  #BackRed      : 2
% 2.99/1.51  
% 2.99/1.51  #Partial instantiations: 0
% 2.99/1.51  #Strategies tried      : 1
% 2.99/1.51  
% 2.99/1.51  Timing (in seconds)
% 2.99/1.51  ----------------------
% 2.99/1.52  Preprocessing        : 0.30
% 2.99/1.52  Parsing              : 0.15
% 2.99/1.52  CNF conversion       : 0.02
% 2.99/1.52  Main loop            : 0.40
% 2.99/1.52  Inferencing          : 0.16
% 2.99/1.52  Reduction            : 0.10
% 2.99/1.52  Demodulation         : 0.07
% 2.99/1.52  BG Simplification    : 0.02
% 2.99/1.52  Subsumption          : 0.08
% 2.99/1.52  Abstraction          : 0.02
% 2.99/1.52  MUC search           : 0.00
% 2.99/1.52  Cooper               : 0.00
% 2.99/1.52  Total                : 0.74
% 2.99/1.52  Index Insertion      : 0.00
% 2.99/1.52  Index Deletion       : 0.00
% 2.99/1.52  Index Matching       : 0.00
% 2.99/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
