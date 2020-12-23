%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:29 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  234 (2742 expanded)
%              Number of leaves         :   19 ( 858 expanded)
%              Depth                    :   23
%              Number of atoms          :  378 (6219 expanded)
%              Number of equality atoms :  166 (3876 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(c_24,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_28,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_176,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_tarski(k2_zfmisc_1(A_34,B_35),k2_zfmisc_1(A_34,C_36))
      | r1_tarski(B_35,C_36)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_182,plain,(
    ! [A_12,B_13,B_35,C_14] :
      ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),B_35),k3_zfmisc_1(A_12,B_13,C_14))
      | r1_tarski(B_35,C_14)
      | k2_zfmisc_1(A_12,B_13) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_176])).

tff(c_859,plain,(
    ! [A_113,B_114,B_115,C_116] :
      ( ~ r1_tarski(k3_zfmisc_1(A_113,B_114,B_115),k3_zfmisc_1(A_113,B_114,C_116))
      | r1_tarski(B_115,C_116)
      | k2_zfmisc_1(A_113,B_114) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_182])).

tff(c_886,plain,(
    ! [C_116] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k3_zfmisc_1('#skF_1','#skF_2',C_116))
      | r1_tarski('#skF_3',C_116)
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_859])).

tff(c_957,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_886])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1048,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_8])).

tff(c_1050,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1048])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1024,plain,(
    ! [C_14] : k3_zfmisc_1('#skF_1','#skF_2',C_14) = k2_zfmisc_1(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_22])).

tff(c_1047,plain,(
    ! [C_14] : k3_zfmisc_1('#skF_1','#skF_2',C_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1024])).

tff(c_1163,plain,(
    ! [C_14] : k3_zfmisc_1('#skF_1','#skF_2',C_14) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1047])).

tff(c_1164,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_28])).

tff(c_26,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_29,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_1081,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_29])).

tff(c_1194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_1081])).

tff(c_1195,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1048])).

tff(c_1227,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_29])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_22,B_23,C_24] : k2_zfmisc_1(k2_zfmisc_1(A_22,B_23),C_24) = k3_zfmisc_1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [A_3,C_24] : k3_zfmisc_1(A_3,k1_xboole_0,C_24) = k2_zfmisc_1(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_110,plain,(
    ! [A_3,C_24] : k3_zfmisc_1(A_3,k1_xboole_0,C_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_1223,plain,(
    ! [A_3,C_24] : k3_zfmisc_1(A_3,'#skF_2',C_24) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1195,c_110])).

tff(c_1325,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_28])).

tff(c_1327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1227,c_1325])).

tff(c_1329,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_886])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_389,plain,(
    ! [B_58,D_59,A_60,C_61] :
      ( r1_tarski(B_58,D_59)
      | k2_zfmisc_1(A_60,B_58) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_60,B_58),k2_zfmisc_1(C_61,D_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_392,plain,(
    ! [D_59,C_61,C_14,A_12,B_13] :
      ( r1_tarski(C_14,D_59)
      | k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_12,B_13,C_14),k2_zfmisc_1(C_61,D_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_389])).

tff(c_916,plain,(
    ! [C_121,B_118,D_122,A_120,C_119] :
      ( r1_tarski(C_121,D_122)
      | k3_zfmisc_1(A_120,B_118,C_121) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_120,B_118,C_121),k2_zfmisc_1(C_119,D_122)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_392])).

tff(c_934,plain,(
    ! [D_122,C_119] :
      ( r1_tarski('#skF_3',D_122)
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_119,D_122)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_916])).

tff(c_945,plain,(
    ! [D_122,C_119] :
      ( r1_tarski('#skF_3',D_122)
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_119,D_122)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_934])).

tff(c_947,plain,(
    ! [D_123,C_124] :
      ( r1_tarski('#skF_3',D_123)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_124,D_123)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_945])).

tff(c_1340,plain,(
    ! [C_139,A_140,B_141] :
      ( r1_tarski('#skF_3',C_139)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k3_zfmisc_1(A_140,B_141,C_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_947])).

tff(c_1362,plain,(
    r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_1340])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1365,plain,
    ( '#skF_6' = '#skF_3'
    | ~ r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1362,c_2])).

tff(c_1366,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1365])).

tff(c_665,plain,(
    ! [B_98,A_99,C_101,A_100,B_97] :
      ( r1_tarski(B_98,C_101)
      | k2_zfmisc_1(A_100,B_98) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_100,B_98),k3_zfmisc_1(A_99,B_97,C_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_389])).

tff(c_680,plain,(
    ! [A_99,C_101,C_14,A_12,B_13,B_97] :
      ( r1_tarski(C_14,C_101)
      | k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_12,B_13,C_14),k3_zfmisc_1(A_99,B_97,C_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_665])).

tff(c_1575,plain,(
    ! [A_171,C_173,A_169,B_168,C_172,B_170] :
      ( r1_tarski(C_173,C_172)
      | k3_zfmisc_1(A_171,B_168,C_173) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_171,B_168,C_173),k3_zfmisc_1(A_169,B_170,C_172)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_680])).

tff(c_1619,plain,(
    ! [C_174,A_175,B_176] :
      ( r1_tarski(C_174,'#skF_3')
      | k3_zfmisc_1(A_175,B_176,C_174) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_175,B_176,C_174),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1575])).

tff(c_1638,plain,
    ( r1_tarski('#skF_6','#skF_3')
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1619])).

tff(c_1649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_1366,c_1638])).

tff(c_1650,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1365])).

tff(c_239,plain,(
    ! [B_41,A_42,C_43] :
      ( ~ r1_tarski(k2_zfmisc_1(B_41,A_42),k2_zfmisc_1(C_43,A_42))
      | r1_tarski(B_41,C_43)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_551,plain,(
    ! [A_82,B_83,C_84,C_85] :
      ( ~ r1_tarski(k3_zfmisc_1(A_82,B_83,C_84),k2_zfmisc_1(C_85,C_84))
      | r1_tarski(k2_zfmisc_1(A_82,B_83),C_85)
      | k1_xboole_0 = C_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_239])).

tff(c_569,plain,(
    ! [C_85] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_85,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),C_85)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_551])).

tff(c_693,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_767,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_29])).

tff(c_90,plain,(
    ! [A_22,B_23] : k3_zfmisc_1(A_22,B_23,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_765,plain,(
    ! [A_22,B_23] : k3_zfmisc_1(A_22,B_23,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_693,c_90])).

tff(c_832,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_28])).

tff(c_834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_767,c_832])).

tff(c_836,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_631,plain,(
    ! [B_93,C_94,A_95,B_96] :
      ( ~ r1_tarski(k2_zfmisc_1(B_93,C_94),k3_zfmisc_1(A_95,B_96,C_94))
      | r1_tarski(B_93,k2_zfmisc_1(A_95,B_96))
      | k1_xboole_0 = C_94 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_239])).

tff(c_649,plain,(
    ! [B_93] :
      ( ~ r1_tarski(k2_zfmisc_1(B_93,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(B_93,k2_zfmisc_1('#skF_1','#skF_2'))
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_631])).

tff(c_907,plain,(
    ! [B_117] :
      ( ~ r1_tarski(k2_zfmisc_1(B_117,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(B_117,k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_836,c_649])).

tff(c_911,plain,(
    ! [A_12,B_13] :
      ( ~ r1_tarski(k3_zfmisc_1(A_12,B_13,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(k2_zfmisc_1(A_12,B_13),k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_907])).

tff(c_1933,plain,(
    ! [A_209,B_210] :
      ( ~ r1_tarski(k3_zfmisc_1(A_209,B_210,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_3'))
      | r1_tarski(k2_zfmisc_1(A_209,B_210),k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_911])).

tff(c_1958,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_1933])).

tff(c_18,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r1_tarski(B_9,D_11)
      | k2_zfmisc_1(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1967,plain,
    ( r1_tarski('#skF_5','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1958,c_18])).

tff(c_1970,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1967])).

tff(c_2097,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1970,c_8])).

tff(c_2099,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2097])).

tff(c_2072,plain,(
    ! [C_14] : k3_zfmisc_1('#skF_4','#skF_5',C_14) = k2_zfmisc_1(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_1970,c_22])).

tff(c_2096,plain,(
    ! [C_14] : k3_zfmisc_1('#skF_4','#skF_5',C_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2072])).

tff(c_2258,plain,(
    ! [C_14] : k3_zfmisc_1('#skF_4','#skF_5',C_14) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_2096])).

tff(c_1661,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_29])).

tff(c_2108,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_1661])).

tff(c_2269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_2108])).

tff(c_2270,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2097])).

tff(c_2304,plain,(
    ! [A_3,C_24] : k3_zfmisc_1(A_3,'#skF_5',C_24) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2270,c_2270,c_110])).

tff(c_2280,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2270,c_1661])).

tff(c_2523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_2280])).

tff(c_2524,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1967])).

tff(c_2528,plain,
    ( '#skF_5' = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_2524,c_2])).

tff(c_2529,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2528])).

tff(c_837,plain,(
    ! [C_110] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_110,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),C_110) ) ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_841,plain,(
    ! [A_12,B_13] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k3_zfmisc_1(A_12,B_13,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(A_12,B_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_837])).

tff(c_2538,plain,(
    ! [A_240,B_241] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_3'),k3_zfmisc_1(A_240,B_241,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(A_240,B_241)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_841])).

tff(c_2563,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_2538])).

tff(c_2566,plain,
    ( r1_tarski('#skF_2','#skF_5')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2563,c_18])).

tff(c_2575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1329,c_2529,c_2566])).

tff(c_2576,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2528])).

tff(c_2525,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1967])).

tff(c_2578,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_2525])).

tff(c_20,plain,(
    ! [A_8,C_10,B_9,D_11] :
      ( r1_tarski(A_8,C_10)
      | k2_zfmisc_1(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1968,plain,
    ( r1_tarski('#skF_4','#skF_1')
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1958,c_20])).

tff(c_2598,plain,
    ( r1_tarski('#skF_4','#skF_1')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_1968])).

tff(c_2599,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2578,c_2598])).

tff(c_2601,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_2599,c_2])).

tff(c_2604,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2601])).

tff(c_1969,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5')
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1958,c_2])).

tff(c_2792,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_2')
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_2576,c_1969])).

tff(c_2793,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2792])).

tff(c_2814,plain,(
    ! [A_256,B_257] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k3_zfmisc_1(A_256,B_257,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(A_256,B_257)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_1650,c_841])).

tff(c_2833,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_2814])).

tff(c_2842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2793,c_2833])).

tff(c_2843,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2792])).

tff(c_2891,plain,(
    ! [C_10,D_11] :
      ( r1_tarski('#skF_1',C_10)
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_20])).

tff(c_2932,plain,(
    ! [C_10,D_11] :
      ( r1_tarski('#skF_1',C_10)
      | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_2891])).

tff(c_3149,plain,(
    ! [C_272,D_273] :
      ( r1_tarski('#skF_1',C_272)
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1(C_272,D_273)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2578,c_2932])).

tff(c_3165,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_3149])).

tff(c_3171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2604,c_3165])).

tff(c_3173,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_3186,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3173,c_28])).

tff(c_3187,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3186,c_29])).

tff(c_3172,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_3178,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3172])).

tff(c_3512,plain,(
    ! [B_315,D_316,A_317,C_318] :
      ( r1_tarski(B_315,D_316)
      | k2_zfmisc_1(A_317,B_315) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_317,B_315),k2_zfmisc_1(C_318,D_316)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3515,plain,(
    ! [D_316,C_318,C_14,A_12,B_13] :
      ( r1_tarski(C_14,D_316)
      | k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_12,B_13,C_14),k2_zfmisc_1(C_318,D_316)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3512])).

tff(c_3935,plain,(
    ! [C_367,D_368,A_366,C_369,B_365] :
      ( r1_tarski(C_367,D_368)
      | k3_zfmisc_1(A_366,B_365,C_367) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_366,B_365,C_367),k2_zfmisc_1(C_369,D_368)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3515])).

tff(c_3953,plain,(
    ! [D_368,C_369] :
      ( r1_tarski('#skF_6',D_368)
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_369,D_368)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3186,c_3935])).

tff(c_3964,plain,(
    ! [D_368,C_369] :
      ( r1_tarski('#skF_6',D_368)
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_369,D_368)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3186,c_3953])).

tff(c_4013,plain,(
    ! [D_374,C_375] :
      ( r1_tarski('#skF_6',D_374)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_375,D_374)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3187,c_3964])).

tff(c_4023,plain,(
    ! [C_376,A_377,B_378] :
      ( r1_tarski('#skF_6',C_376)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k3_zfmisc_1(A_377,B_378,C_376)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4013])).

tff(c_4045,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_4023])).

tff(c_4047,plain,
    ( '#skF_6' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_4045,c_2])).

tff(c_4050,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3178,c_4047])).

tff(c_4515,plain,(
    ! [A_409,C_408,B_407,A_410,C_411,B_412] :
      ( r1_tarski(C_408,C_411)
      | k3_zfmisc_1(A_410,B_412,C_408) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_410,B_412,C_408),k3_zfmisc_1(A_409,B_407,C_411)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3935])).

tff(c_4657,plain,(
    ! [C_425,A_426,B_427] :
      ( r1_tarski(C_425,'#skF_6')
      | k3_zfmisc_1(A_426,B_427,C_425) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_426,B_427,C_425),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3186,c_4515])).

tff(c_4676,plain,
    ( r1_tarski('#skF_3','#skF_6')
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_4657])).

tff(c_4687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3187,c_4050,c_4676])).

tff(c_4688,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3172])).

tff(c_4689,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3172])).

tff(c_4706,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4689,c_3173,c_28])).

tff(c_4760,plain,(
    ! [B_437,A_438,C_439] :
      ( ~ r1_tarski(k2_zfmisc_1(B_437,A_438),k2_zfmisc_1(C_439,A_438))
      | r1_tarski(B_437,C_439)
      | k1_xboole_0 = A_438 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5227,plain,(
    ! [B_499,C_500,A_501,B_502] :
      ( ~ r1_tarski(k2_zfmisc_1(B_499,C_500),k3_zfmisc_1(A_501,B_502,C_500))
      | r1_tarski(B_499,k2_zfmisc_1(A_501,B_502))
      | k1_xboole_0 = C_500 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4760])).

tff(c_5245,plain,(
    ! [B_499] :
      ( ~ r1_tarski(k2_zfmisc_1(B_499,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
      | r1_tarski(B_499,k2_zfmisc_1('#skF_4','#skF_5'))
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_5227])).

tff(c_5261,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5245])).

tff(c_4719,plain,(
    ! [A_432,B_433,C_434] : k2_zfmisc_1(k2_zfmisc_1(A_432,B_433),C_434) = k3_zfmisc_1(A_432,B_433,C_434) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4732,plain,(
    ! [A_432,B_433] : k3_zfmisc_1(A_432,B_433,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4719,c_10])).

tff(c_5284,plain,(
    ! [A_432,B_433] : k3_zfmisc_1(A_432,B_433,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5261,c_5261,c_4732])).

tff(c_4690,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4689,c_29])).

tff(c_4707,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4706,c_4690])).

tff(c_5285,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5261,c_4707])).

tff(c_5399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5284,c_5285])).

tff(c_5402,plain,(
    ! [B_513] :
      ( ~ r1_tarski(k2_zfmisc_1(B_513,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
      | r1_tarski(B_513,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_5245])).

tff(c_5411,plain,(
    ! [A_514,B_515] :
      ( ~ r1_tarski(k3_zfmisc_1(A_514,B_515,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
      | r1_tarski(k2_zfmisc_1(A_514,B_515),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5402])).

tff(c_5436,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_5411])).

tff(c_14,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r1_tarski(k2_zfmisc_1(A_5,B_6),k2_zfmisc_1(A_5,C_7))
      | r1_tarski(B_6,C_7)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5451,plain,
    ( r1_tarski('#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5436,c_14])).

tff(c_5453,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5451])).

tff(c_4741,plain,(
    ! [B_4,C_434] : k3_zfmisc_1(k1_xboole_0,B_4,C_434) = k2_zfmisc_1(k1_xboole_0,C_434) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4719])).

tff(c_4751,plain,(
    ! [B_4,C_434] : k3_zfmisc_1(k1_xboole_0,B_4,C_434) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4741])).

tff(c_5474,plain,(
    ! [B_4,C_434] : k3_zfmisc_1('#skF_4',B_4,C_434) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5453,c_5453,c_4751])).

tff(c_4830,plain,(
    ! [C_444,B_445] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(C_444,B_445))
      | r1_tarski(k1_xboole_0,C_444)
      | k1_xboole_0 = B_445 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4760])).

tff(c_5028,plain,(
    ! [A_469,B_470,C_471] :
      ( ~ r1_tarski(k1_xboole_0,k3_zfmisc_1(A_469,B_470,C_471))
      | r1_tarski(k1_xboole_0,k2_zfmisc_1(A_469,B_470))
      | k1_xboole_0 = C_471 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4830])).

tff(c_5043,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
    | r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_5028])).

tff(c_5130,plain,(
    ~ r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5043])).

tff(c_5461,plain,(
    ~ r1_tarski('#skF_4',k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5453,c_5130])).

tff(c_5607,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5474,c_5461])).

tff(c_5613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5607])).

tff(c_5615,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5451])).

tff(c_5614,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_5451])).

tff(c_5617,plain,
    ( '#skF_5' = '#skF_2'
    | ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_5614,c_2])).

tff(c_5620,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_4688,c_5617])).

tff(c_5401,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5245])).

tff(c_5621,plain,(
    ! [A_526,B_527,C_528,C_529] :
      ( ~ r1_tarski(k3_zfmisc_1(A_526,B_527,C_528),k2_zfmisc_1(C_529,C_528))
      | r1_tarski(k2_zfmisc_1(A_526,B_527),C_529)
      | k1_xboole_0 = C_528 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4760])).

tff(c_5639,plain,(
    ! [C_529] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_529,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),C_529)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_5621])).

tff(c_5657,plain,(
    ! [C_530] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_530,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),C_530) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5401,c_5639])).

tff(c_5667,plain,(
    ! [A_531,B_532] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k3_zfmisc_1(A_531,B_532,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(A_531,B_532)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5657])).

tff(c_5692,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_5667])).

tff(c_5701,plain,
    ( r1_tarski('#skF_5','#skF_2')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5692,c_14])).

tff(c_5712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5615,c_5620,c_5701])).

tff(c_5713,plain,
    ( k1_xboole_0 = '#skF_3'
    | r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5043])).

tff(c_5724,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5713])).

tff(c_4860,plain,(
    ! [A_448,B_449,C_450] :
      ( ~ r1_tarski(k2_zfmisc_1(A_448,B_449),k2_zfmisc_1(A_448,C_450))
      | r1_tarski(B_449,C_450)
      | k1_xboole_0 = A_448 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4875,plain,(
    ! [A_3,C_450] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_3,C_450))
      | r1_tarski(k1_xboole_0,C_450)
      | k1_xboole_0 = A_3 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4860])).

tff(c_5733,plain,
    ( r1_tarski(k1_xboole_0,'#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5724,c_4875])).

tff(c_5764,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5733])).

tff(c_5781,plain,(
    ! [B_4,C_434] : k3_zfmisc_1('#skF_4',B_4,C_434) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5764,c_5764,c_4751])).

tff(c_5785,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5764,c_4707])).

tff(c_5841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5781,c_5785])).

tff(c_5843,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5733])).

tff(c_5847,plain,(
    ! [B_540,C_541,A_542,B_543] :
      ( ~ r1_tarski(k2_zfmisc_1(B_540,C_541),k3_zfmisc_1(A_542,B_543,C_541))
      | r1_tarski(B_540,k2_zfmisc_1(A_542,B_543))
      | k1_xboole_0 = C_541 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4760])).

tff(c_5865,plain,(
    ! [B_540] :
      ( ~ r1_tarski(k2_zfmisc_1(B_540,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
      | r1_tarski(B_540,k2_zfmisc_1('#skF_4','#skF_5'))
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_5847])).

tff(c_6174,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5865])).

tff(c_5714,plain,(
    r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5043])).

tff(c_4833,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ r1_tarski(k1_xboole_0,k3_zfmisc_1(A_12,B_13,C_14))
      | r1_tarski(k1_xboole_0,k2_zfmisc_1(A_12,B_13))
      | k1_xboole_0 = C_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4830])).

tff(c_5720,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5714,c_4833])).

tff(c_6035,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5720])).

tff(c_6062,plain,(
    ! [A_432,B_433] : k3_zfmisc_1(A_432,B_433,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6035,c_6035,c_4732])).

tff(c_6063,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6035,c_4707])).

tff(c_6171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6062,c_6063])).

tff(c_6173,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5720])).

tff(c_6211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6174,c_6173])).

tff(c_6278,plain,(
    ! [B_569] :
      ( ~ r1_tarski(k2_zfmisc_1(B_569,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
      | r1_tarski(B_569,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_5865])).

tff(c_6531,plain,(
    ! [A_599,B_600] :
      ( ~ r1_tarski(k3_zfmisc_1(A_599,B_600,'#skF_3'),k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
      | r1_tarski(k2_zfmisc_1(A_599,B_600),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6278])).

tff(c_6558,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_6531])).

tff(c_6567,plain,
    ( r1_tarski('#skF_2','#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6558,c_14])).

tff(c_6575,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_5843,c_6567])).

tff(c_6578,plain,
    ( '#skF_5' = '#skF_2'
    | ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_6575,c_2])).

tff(c_6581,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_4688,c_6578])).

tff(c_6576,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6558,c_2])).

tff(c_6583,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6576])).

tff(c_6213,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5865])).

tff(c_6228,plain,(
    ! [A_564,B_565,C_566,C_567] :
      ( ~ r1_tarski(k3_zfmisc_1(A_564,B_565,C_566),k2_zfmisc_1(C_567,C_566))
      | r1_tarski(k2_zfmisc_1(A_564,B_565),C_567)
      | k1_xboole_0 = C_566 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4760])).

tff(c_6246,plain,(
    ! [C_567] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_567,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),C_567)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_6228])).

tff(c_6267,plain,(
    ! [C_568] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_568,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),C_568) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6213,c_6246])).

tff(c_6615,plain,(
    ! [A_606,B_607] :
      ( ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k3_zfmisc_1(A_606,B_607,'#skF_3'))
      | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(A_606,B_607)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6267])).

tff(c_6634,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_6615])).

tff(c_6645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6583,c_6634])).

tff(c_6646,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_6576])).

tff(c_6729,plain,(
    ! [C_7] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4',C_7))
      | r1_tarski('#skF_5',C_7)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6646,c_14])).

tff(c_6945,plain,(
    ! [C_621] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4',C_621))
      | r1_tarski('#skF_5',C_621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5843,c_6729])).

tff(c_6956,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_6945])).

tff(c_6963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6581,c_6956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:16:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.08  
% 5.58/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.09  %$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.58/2.09  
% 5.58/2.09  %Foreground sorts:
% 5.58/2.09  
% 5.58/2.09  
% 5.58/2.09  %Background operators:
% 5.58/2.09  
% 5.58/2.09  
% 5.58/2.09  %Foreground operators:
% 5.58/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.58/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.58/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.58/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.58/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.58/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.58/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.58/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.58/2.09  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.58/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.58/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.58/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.58/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.58/2.09  
% 5.79/2.14  tff(f_69, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 5.79/2.14  tff(f_58, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.79/2.14  tff(f_48, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 5.79/2.14  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.79/2.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.79/2.14  tff(f_56, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.88/2.14  tff(c_24, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.88/2.14  tff(c_54, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_24])).
% 5.88/2.14  tff(c_28, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.88/2.14  tff(c_22, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.88/2.14  tff(c_176, plain, (![A_34, B_35, C_36]: (~r1_tarski(k2_zfmisc_1(A_34, B_35), k2_zfmisc_1(A_34, C_36)) | r1_tarski(B_35, C_36) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.88/2.14  tff(c_182, plain, (![A_12, B_13, B_35, C_14]: (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), B_35), k3_zfmisc_1(A_12, B_13, C_14)) | r1_tarski(B_35, C_14) | k2_zfmisc_1(A_12, B_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_176])).
% 5.88/2.14  tff(c_859, plain, (![A_113, B_114, B_115, C_116]: (~r1_tarski(k3_zfmisc_1(A_113, B_114, B_115), k3_zfmisc_1(A_113, B_114, C_116)) | r1_tarski(B_115, C_116) | k2_zfmisc_1(A_113, B_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_182])).
% 5.88/2.14  tff(c_886, plain, (![C_116]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k3_zfmisc_1('#skF_1', '#skF_2', C_116)) | r1_tarski('#skF_3', C_116) | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_859])).
% 5.88/2.14  tff(c_957, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_886])).
% 5.88/2.14  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.88/2.14  tff(c_1048, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_957, c_8])).
% 5.88/2.14  tff(c_1050, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1048])).
% 5.88/2.14  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.88/2.14  tff(c_1024, plain, (![C_14]: (k3_zfmisc_1('#skF_1', '#skF_2', C_14)=k2_zfmisc_1(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_957, c_22])).
% 5.88/2.14  tff(c_1047, plain, (![C_14]: (k3_zfmisc_1('#skF_1', '#skF_2', C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1024])).
% 5.88/2.14  tff(c_1163, plain, (![C_14]: (k3_zfmisc_1('#skF_1', '#skF_2', C_14)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1047])).
% 5.88/2.14  tff(c_1164, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_28])).
% 5.88/2.14  tff(c_26, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.88/2.14  tff(c_29, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 5.88/2.14  tff(c_1081, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_29])).
% 5.88/2.14  tff(c_1194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1164, c_1081])).
% 5.88/2.14  tff(c_1195, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1048])).
% 5.88/2.14  tff(c_1227, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_29])).
% 5.88/2.14  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.88/2.14  tff(c_77, plain, (![A_22, B_23, C_24]: (k2_zfmisc_1(k2_zfmisc_1(A_22, B_23), C_24)=k3_zfmisc_1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.88/2.14  tff(c_102, plain, (![A_3, C_24]: (k3_zfmisc_1(A_3, k1_xboole_0, C_24)=k2_zfmisc_1(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_10, c_77])).
% 5.88/2.14  tff(c_110, plain, (![A_3, C_24]: (k3_zfmisc_1(A_3, k1_xboole_0, C_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_102])).
% 5.88/2.14  tff(c_1223, plain, (![A_3, C_24]: (k3_zfmisc_1(A_3, '#skF_2', C_24)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1195, c_110])).
% 5.88/2.14  tff(c_1325, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1223, c_28])).
% 5.88/2.14  tff(c_1327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1227, c_1325])).
% 5.88/2.14  tff(c_1329, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_886])).
% 5.88/2.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.14  tff(c_389, plain, (![B_58, D_59, A_60, C_61]: (r1_tarski(B_58, D_59) | k2_zfmisc_1(A_60, B_58)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_60, B_58), k2_zfmisc_1(C_61, D_59)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.14  tff(c_392, plain, (![D_59, C_61, C_14, A_12, B_13]: (r1_tarski(C_14, D_59) | k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_12, B_13, C_14), k2_zfmisc_1(C_61, D_59)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_389])).
% 5.88/2.14  tff(c_916, plain, (![C_121, B_118, D_122, A_120, C_119]: (r1_tarski(C_121, D_122) | k3_zfmisc_1(A_120, B_118, C_121)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_120, B_118, C_121), k2_zfmisc_1(C_119, D_122)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_392])).
% 5.88/2.14  tff(c_934, plain, (![D_122, C_119]: (r1_tarski('#skF_3', D_122) | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_119, D_122)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_916])).
% 5.88/2.14  tff(c_945, plain, (![D_122, C_119]: (r1_tarski('#skF_3', D_122) | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_119, D_122)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_934])).
% 5.88/2.14  tff(c_947, plain, (![D_123, C_124]: (r1_tarski('#skF_3', D_123) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_124, D_123)))), inference(negUnitSimplification, [status(thm)], [c_29, c_945])).
% 5.88/2.14  tff(c_1340, plain, (![C_139, A_140, B_141]: (r1_tarski('#skF_3', C_139) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k3_zfmisc_1(A_140, B_141, C_139)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_947])).
% 5.88/2.14  tff(c_1362, plain, (r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_1340])).
% 5.88/2.14  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.14  tff(c_1365, plain, ('#skF_6'='#skF_3' | ~r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1362, c_2])).
% 5.88/2.14  tff(c_1366, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_1365])).
% 5.88/2.14  tff(c_665, plain, (![B_98, A_99, C_101, A_100, B_97]: (r1_tarski(B_98, C_101) | k2_zfmisc_1(A_100, B_98)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_100, B_98), k3_zfmisc_1(A_99, B_97, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_389])).
% 5.88/2.14  tff(c_680, plain, (![A_99, C_101, C_14, A_12, B_13, B_97]: (r1_tarski(C_14, C_101) | k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_12, B_13, C_14), k3_zfmisc_1(A_99, B_97, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_665])).
% 5.88/2.14  tff(c_1575, plain, (![A_171, C_173, A_169, B_168, C_172, B_170]: (r1_tarski(C_173, C_172) | k3_zfmisc_1(A_171, B_168, C_173)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_171, B_168, C_173), k3_zfmisc_1(A_169, B_170, C_172)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_680])).
% 5.88/2.14  tff(c_1619, plain, (![C_174, A_175, B_176]: (r1_tarski(C_174, '#skF_3') | k3_zfmisc_1(A_175, B_176, C_174)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_175, B_176, C_174), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1575])).
% 5.88/2.14  tff(c_1638, plain, (r1_tarski('#skF_6', '#skF_3') | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1619])).
% 5.88/2.14  tff(c_1649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_1366, c_1638])).
% 5.88/2.14  tff(c_1650, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1365])).
% 5.88/2.14  tff(c_239, plain, (![B_41, A_42, C_43]: (~r1_tarski(k2_zfmisc_1(B_41, A_42), k2_zfmisc_1(C_43, A_42)) | r1_tarski(B_41, C_43) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.88/2.14  tff(c_551, plain, (![A_82, B_83, C_84, C_85]: (~r1_tarski(k3_zfmisc_1(A_82, B_83, C_84), k2_zfmisc_1(C_85, C_84)) | r1_tarski(k2_zfmisc_1(A_82, B_83), C_85) | k1_xboole_0=C_84)), inference(superposition, [status(thm), theory('equality')], [c_22, c_239])).
% 5.88/2.14  tff(c_569, plain, (![C_85]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_85, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), C_85) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_551])).
% 5.88/2.14  tff(c_693, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_569])).
% 5.88/2.14  tff(c_767, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_693, c_29])).
% 5.88/2.14  tff(c_90, plain, (![A_22, B_23]: (k3_zfmisc_1(A_22, B_23, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 5.88/2.14  tff(c_765, plain, (![A_22, B_23]: (k3_zfmisc_1(A_22, B_23, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_693, c_90])).
% 5.88/2.14  tff(c_832, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_765, c_28])).
% 5.88/2.14  tff(c_834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_767, c_832])).
% 5.88/2.14  tff(c_836, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_569])).
% 5.88/2.14  tff(c_631, plain, (![B_93, C_94, A_95, B_96]: (~r1_tarski(k2_zfmisc_1(B_93, C_94), k3_zfmisc_1(A_95, B_96, C_94)) | r1_tarski(B_93, k2_zfmisc_1(A_95, B_96)) | k1_xboole_0=C_94)), inference(superposition, [status(thm), theory('equality')], [c_22, c_239])).
% 5.88/2.14  tff(c_649, plain, (![B_93]: (~r1_tarski(k2_zfmisc_1(B_93, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(B_93, k2_zfmisc_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_631])).
% 5.88/2.14  tff(c_907, plain, (![B_117]: (~r1_tarski(k2_zfmisc_1(B_117, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(B_117, k2_zfmisc_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_836, c_649])).
% 5.88/2.14  tff(c_911, plain, (![A_12, B_13]: (~r1_tarski(k3_zfmisc_1(A_12, B_13, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(k2_zfmisc_1(A_12, B_13), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_907])).
% 5.88/2.14  tff(c_1933, plain, (![A_209, B_210]: (~r1_tarski(k3_zfmisc_1(A_209, B_210, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')) | r1_tarski(k2_zfmisc_1(A_209, B_210), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_911])).
% 5.88/2.14  tff(c_1958, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_1933])).
% 5.88/2.14  tff(c_18, plain, (![B_9, D_11, A_8, C_10]: (r1_tarski(B_9, D_11) | k2_zfmisc_1(A_8, B_9)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.14  tff(c_1967, plain, (r1_tarski('#skF_5', '#skF_2') | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1958, c_18])).
% 5.88/2.14  tff(c_1970, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1967])).
% 5.88/2.14  tff(c_2097, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1970, c_8])).
% 5.88/2.14  tff(c_2099, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2097])).
% 5.88/2.14  tff(c_2072, plain, (![C_14]: (k3_zfmisc_1('#skF_4', '#skF_5', C_14)=k2_zfmisc_1(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_1970, c_22])).
% 5.88/2.14  tff(c_2096, plain, (![C_14]: (k3_zfmisc_1('#skF_4', '#skF_5', C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2072])).
% 5.88/2.14  tff(c_2258, plain, (![C_14]: (k3_zfmisc_1('#skF_4', '#skF_5', C_14)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2099, c_2096])).
% 5.88/2.14  tff(c_1661, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_29])).
% 5.88/2.14  tff(c_2108, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2099, c_1661])).
% 5.88/2.14  tff(c_2269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2258, c_2108])).
% 5.88/2.14  tff(c_2270, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2097])).
% 5.88/2.14  tff(c_2304, plain, (![A_3, C_24]: (k3_zfmisc_1(A_3, '#skF_5', C_24)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2270, c_2270, c_110])).
% 5.88/2.14  tff(c_2280, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2270, c_1661])).
% 5.88/2.14  tff(c_2523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2304, c_2280])).
% 5.88/2.14  tff(c_2524, plain, (r1_tarski('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_1967])).
% 5.88/2.14  tff(c_2528, plain, ('#skF_5'='#skF_2' | ~r1_tarski('#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_2524, c_2])).
% 5.88/2.14  tff(c_2529, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_2528])).
% 5.88/2.14  tff(c_837, plain, (![C_110]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_110, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), C_110))), inference(splitRight, [status(thm)], [c_569])).
% 5.88/2.14  tff(c_841, plain, (![A_12, B_13]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k3_zfmisc_1(A_12, B_13, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_837])).
% 5.88/2.14  tff(c_2538, plain, (![A_240, B_241]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'), k3_zfmisc_1(A_240, B_241, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(A_240, B_241)))), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_841])).
% 5.88/2.14  tff(c_2563, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_2538])).
% 5.88/2.14  tff(c_2566, plain, (r1_tarski('#skF_2', '#skF_5') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2563, c_18])).
% 5.88/2.14  tff(c_2575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1329, c_2529, c_2566])).
% 5.88/2.14  tff(c_2576, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_2528])).
% 5.88/2.14  tff(c_2525, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1967])).
% 5.88/2.14  tff(c_2578, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2576, c_2525])).
% 5.88/2.14  tff(c_20, plain, (![A_8, C_10, B_9, D_11]: (r1_tarski(A_8, C_10) | k2_zfmisc_1(A_8, B_9)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.14  tff(c_1968, plain, (r1_tarski('#skF_4', '#skF_1') | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1958, c_20])).
% 5.88/2.14  tff(c_2598, plain, (r1_tarski('#skF_4', '#skF_1') | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2576, c_1968])).
% 5.88/2.14  tff(c_2599, plain, (r1_tarski('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2578, c_2598])).
% 5.88/2.14  tff(c_2601, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_2599, c_2])).
% 5.88/2.14  tff(c_2604, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_2601])).
% 5.88/2.14  tff(c_1969, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1958, c_2])).
% 5.88/2.14  tff(c_2792, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_2') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2576, c_2576, c_1969])).
% 5.88/2.14  tff(c_2793, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2792])).
% 5.88/2.14  tff(c_2814, plain, (![A_256, B_257]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k3_zfmisc_1(A_256, B_257, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(A_256, B_257)))), inference(demodulation, [status(thm), theory('equality')], [c_2576, c_1650, c_841])).
% 5.88/2.14  tff(c_2833, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_2814])).
% 5.88/2.14  tff(c_2842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2793, c_2833])).
% 5.88/2.14  tff(c_2843, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_2792])).
% 5.88/2.14  tff(c_2891, plain, (![C_10, D_11]: (r1_tarski('#skF_1', C_10) | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1(C_10, D_11)))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_20])).
% 5.88/2.14  tff(c_2932, plain, (![C_10, D_11]: (r1_tarski('#skF_1', C_10) | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1(C_10, D_11)))), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_2891])).
% 5.88/2.14  tff(c_3149, plain, (![C_272, D_273]: (r1_tarski('#skF_1', C_272) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1(C_272, D_273)))), inference(negUnitSimplification, [status(thm)], [c_2578, c_2932])).
% 5.88/2.14  tff(c_3165, plain, (r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_3149])).
% 5.88/2.14  tff(c_3171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2604, c_3165])).
% 5.88/2.14  tff(c_3173, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 5.88/2.14  tff(c_3186, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3173, c_28])).
% 5.88/2.14  tff(c_3187, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3186, c_29])).
% 5.88/2.14  tff(c_3172, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 5.88/2.14  tff(c_3178, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_3172])).
% 5.88/2.14  tff(c_3512, plain, (![B_315, D_316, A_317, C_318]: (r1_tarski(B_315, D_316) | k2_zfmisc_1(A_317, B_315)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_317, B_315), k2_zfmisc_1(C_318, D_316)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.14  tff(c_3515, plain, (![D_316, C_318, C_14, A_12, B_13]: (r1_tarski(C_14, D_316) | k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_12, B_13, C_14), k2_zfmisc_1(C_318, D_316)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3512])).
% 5.88/2.14  tff(c_3935, plain, (![C_367, D_368, A_366, C_369, B_365]: (r1_tarski(C_367, D_368) | k3_zfmisc_1(A_366, B_365, C_367)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_366, B_365, C_367), k2_zfmisc_1(C_369, D_368)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3515])).
% 5.88/2.14  tff(c_3953, plain, (![D_368, C_369]: (r1_tarski('#skF_6', D_368) | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_369, D_368)))), inference(superposition, [status(thm), theory('equality')], [c_3186, c_3935])).
% 5.88/2.14  tff(c_3964, plain, (![D_368, C_369]: (r1_tarski('#skF_6', D_368) | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_369, D_368)))), inference(demodulation, [status(thm), theory('equality')], [c_3186, c_3953])).
% 5.88/2.14  tff(c_4013, plain, (![D_374, C_375]: (r1_tarski('#skF_6', D_374) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_375, D_374)))), inference(negUnitSimplification, [status(thm)], [c_3187, c_3964])).
% 5.88/2.14  tff(c_4023, plain, (![C_376, A_377, B_378]: (r1_tarski('#skF_6', C_376) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k3_zfmisc_1(A_377, B_378, C_376)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4013])).
% 5.88/2.14  tff(c_4045, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_4023])).
% 5.88/2.14  tff(c_4047, plain, ('#skF_6'='#skF_3' | ~r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_4045, c_2])).
% 5.88/2.14  tff(c_4050, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_3178, c_4047])).
% 5.88/2.14  tff(c_4515, plain, (![A_409, C_408, B_407, A_410, C_411, B_412]: (r1_tarski(C_408, C_411) | k3_zfmisc_1(A_410, B_412, C_408)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_410, B_412, C_408), k3_zfmisc_1(A_409, B_407, C_411)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3935])).
% 5.88/2.14  tff(c_4657, plain, (![C_425, A_426, B_427]: (r1_tarski(C_425, '#skF_6') | k3_zfmisc_1(A_426, B_427, C_425)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_426, B_427, C_425), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3186, c_4515])).
% 5.88/2.14  tff(c_4676, plain, (r1_tarski('#skF_3', '#skF_6') | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_4657])).
% 5.88/2.14  tff(c_4687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3187, c_4050, c_4676])).
% 5.88/2.14  tff(c_4688, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_3172])).
% 5.88/2.14  tff(c_4689, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_3172])).
% 5.88/2.14  tff(c_4706, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4689, c_3173, c_28])).
% 5.88/2.14  tff(c_4760, plain, (![B_437, A_438, C_439]: (~r1_tarski(k2_zfmisc_1(B_437, A_438), k2_zfmisc_1(C_439, A_438)) | r1_tarski(B_437, C_439) | k1_xboole_0=A_438)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.88/2.14  tff(c_5227, plain, (![B_499, C_500, A_501, B_502]: (~r1_tarski(k2_zfmisc_1(B_499, C_500), k3_zfmisc_1(A_501, B_502, C_500)) | r1_tarski(B_499, k2_zfmisc_1(A_501, B_502)) | k1_xboole_0=C_500)), inference(superposition, [status(thm), theory('equality')], [c_22, c_4760])).
% 5.88/2.14  tff(c_5245, plain, (![B_499]: (~r1_tarski(k2_zfmisc_1(B_499, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')) | r1_tarski(B_499, k2_zfmisc_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4706, c_5227])).
% 5.88/2.14  tff(c_5261, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5245])).
% 5.88/2.14  tff(c_4719, plain, (![A_432, B_433, C_434]: (k2_zfmisc_1(k2_zfmisc_1(A_432, B_433), C_434)=k3_zfmisc_1(A_432, B_433, C_434))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.88/2.14  tff(c_4732, plain, (![A_432, B_433]: (k3_zfmisc_1(A_432, B_433, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4719, c_10])).
% 5.88/2.14  tff(c_5284, plain, (![A_432, B_433]: (k3_zfmisc_1(A_432, B_433, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5261, c_5261, c_4732])).
% 5.88/2.14  tff(c_4690, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4689, c_29])).
% 5.88/2.14  tff(c_4707, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4706, c_4690])).
% 5.88/2.14  tff(c_5285, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5261, c_4707])).
% 5.88/2.14  tff(c_5399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5284, c_5285])).
% 5.88/2.14  tff(c_5402, plain, (![B_513]: (~r1_tarski(k2_zfmisc_1(B_513, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')) | r1_tarski(B_513, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_5245])).
% 5.88/2.14  tff(c_5411, plain, (![A_514, B_515]: (~r1_tarski(k3_zfmisc_1(A_514, B_515, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')) | r1_tarski(k2_zfmisc_1(A_514, B_515), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5402])).
% 5.88/2.14  tff(c_5436, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_5411])).
% 5.88/2.14  tff(c_14, plain, (![A_5, B_6, C_7]: (~r1_tarski(k2_zfmisc_1(A_5, B_6), k2_zfmisc_1(A_5, C_7)) | r1_tarski(B_6, C_7) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.88/2.14  tff(c_5451, plain, (r1_tarski('#skF_2', '#skF_5') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5436, c_14])).
% 5.88/2.14  tff(c_5453, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5451])).
% 5.88/2.14  tff(c_4741, plain, (![B_4, C_434]: (k3_zfmisc_1(k1_xboole_0, B_4, C_434)=k2_zfmisc_1(k1_xboole_0, C_434))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4719])).
% 5.88/2.14  tff(c_4751, plain, (![B_4, C_434]: (k3_zfmisc_1(k1_xboole_0, B_4, C_434)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4741])).
% 5.88/2.14  tff(c_5474, plain, (![B_4, C_434]: (k3_zfmisc_1('#skF_4', B_4, C_434)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5453, c_5453, c_4751])).
% 5.88/2.14  tff(c_4830, plain, (![C_444, B_445]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(C_444, B_445)) | r1_tarski(k1_xboole_0, C_444) | k1_xboole_0=B_445)), inference(superposition, [status(thm), theory('equality')], [c_12, c_4760])).
% 5.88/2.14  tff(c_5028, plain, (![A_469, B_470, C_471]: (~r1_tarski(k1_xboole_0, k3_zfmisc_1(A_469, B_470, C_471)) | r1_tarski(k1_xboole_0, k2_zfmisc_1(A_469, B_470)) | k1_xboole_0=C_471)), inference(superposition, [status(thm), theory('equality')], [c_22, c_4830])).
% 5.88/2.14  tff(c_5043, plain, (~r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')) | r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4706, c_5028])).
% 5.88/2.14  tff(c_5130, plain, (~r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_5043])).
% 5.88/2.14  tff(c_5461, plain, (~r1_tarski('#skF_4', k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5453, c_5130])).
% 5.88/2.14  tff(c_5607, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5474, c_5461])).
% 5.88/2.14  tff(c_5613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5607])).
% 5.88/2.14  tff(c_5615, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5451])).
% 5.88/2.14  tff(c_5614, plain, (r1_tarski('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_5451])).
% 5.88/2.14  tff(c_5617, plain, ('#skF_5'='#skF_2' | ~r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_5614, c_2])).
% 5.88/2.14  tff(c_5620, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_4688, c_5617])).
% 5.88/2.14  tff(c_5401, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5245])).
% 5.88/2.14  tff(c_5621, plain, (![A_526, B_527, C_528, C_529]: (~r1_tarski(k3_zfmisc_1(A_526, B_527, C_528), k2_zfmisc_1(C_529, C_528)) | r1_tarski(k2_zfmisc_1(A_526, B_527), C_529) | k1_xboole_0=C_528)), inference(superposition, [status(thm), theory('equality')], [c_22, c_4760])).
% 5.88/2.14  tff(c_5639, plain, (![C_529]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_529, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), C_529) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4706, c_5621])).
% 5.88/2.14  tff(c_5657, plain, (![C_530]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_530, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), C_530))), inference(negUnitSimplification, [status(thm)], [c_5401, c_5639])).
% 5.88/2.14  tff(c_5667, plain, (![A_531, B_532]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k3_zfmisc_1(A_531, B_532, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(A_531, B_532)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5657])).
% 5.88/2.14  tff(c_5692, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_5667])).
% 5.88/2.14  tff(c_5701, plain, (r1_tarski('#skF_5', '#skF_2') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5692, c_14])).
% 5.88/2.14  tff(c_5712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5615, c_5620, c_5701])).
% 5.88/2.14  tff(c_5713, plain, (k1_xboole_0='#skF_3' | r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_5043])).
% 5.88/2.14  tff(c_5724, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_5713])).
% 5.88/2.14  tff(c_4860, plain, (![A_448, B_449, C_450]: (~r1_tarski(k2_zfmisc_1(A_448, B_449), k2_zfmisc_1(A_448, C_450)) | r1_tarski(B_449, C_450) | k1_xboole_0=A_448)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.88/2.14  tff(c_4875, plain, (![A_3, C_450]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_3, C_450)) | r1_tarski(k1_xboole_0, C_450) | k1_xboole_0=A_3)), inference(superposition, [status(thm), theory('equality')], [c_10, c_4860])).
% 5.88/2.14  tff(c_5733, plain, (r1_tarski(k1_xboole_0, '#skF_5') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5724, c_4875])).
% 5.88/2.14  tff(c_5764, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5733])).
% 5.88/2.14  tff(c_5781, plain, (![B_4, C_434]: (k3_zfmisc_1('#skF_4', B_4, C_434)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5764, c_5764, c_4751])).
% 5.88/2.14  tff(c_5785, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5764, c_4707])).
% 5.88/2.14  tff(c_5841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5781, c_5785])).
% 5.88/2.14  tff(c_5843, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5733])).
% 5.88/2.14  tff(c_5847, plain, (![B_540, C_541, A_542, B_543]: (~r1_tarski(k2_zfmisc_1(B_540, C_541), k3_zfmisc_1(A_542, B_543, C_541)) | r1_tarski(B_540, k2_zfmisc_1(A_542, B_543)) | k1_xboole_0=C_541)), inference(superposition, [status(thm), theory('equality')], [c_22, c_4760])).
% 5.88/2.14  tff(c_5865, plain, (![B_540]: (~r1_tarski(k2_zfmisc_1(B_540, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')) | r1_tarski(B_540, k2_zfmisc_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4706, c_5847])).
% 5.88/2.14  tff(c_6174, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5865])).
% 5.88/2.14  tff(c_5714, plain, (r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_5043])).
% 5.88/2.14  tff(c_4833, plain, (![A_12, B_13, C_14]: (~r1_tarski(k1_xboole_0, k3_zfmisc_1(A_12, B_13, C_14)) | r1_tarski(k1_xboole_0, k2_zfmisc_1(A_12, B_13)) | k1_xboole_0=C_14)), inference(superposition, [status(thm), theory('equality')], [c_22, c_4830])).
% 5.88/2.14  tff(c_5720, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_2')) | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5714, c_4833])).
% 5.88/2.14  tff(c_6035, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5720])).
% 5.88/2.14  tff(c_6062, plain, (![A_432, B_433]: (k3_zfmisc_1(A_432, B_433, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6035, c_6035, c_4732])).
% 5.88/2.14  tff(c_6063, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6035, c_4707])).
% 5.88/2.14  tff(c_6171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6062, c_6063])).
% 5.88/2.14  tff(c_6173, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5720])).
% 5.88/2.14  tff(c_6211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6174, c_6173])).
% 5.88/2.14  tff(c_6278, plain, (![B_569]: (~r1_tarski(k2_zfmisc_1(B_569, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')) | r1_tarski(B_569, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_5865])).
% 5.88/2.14  tff(c_6531, plain, (![A_599, B_600]: (~r1_tarski(k3_zfmisc_1(A_599, B_600, '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')) | r1_tarski(k2_zfmisc_1(A_599, B_600), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6278])).
% 5.88/2.14  tff(c_6558, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_6531])).
% 5.88/2.14  tff(c_6567, plain, (r1_tarski('#skF_2', '#skF_5') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6558, c_14])).
% 5.88/2.14  tff(c_6575, plain, (r1_tarski('#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_5843, c_6567])).
% 5.88/2.14  tff(c_6578, plain, ('#skF_5'='#skF_2' | ~r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_6575, c_2])).
% 5.88/2.14  tff(c_6581, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_4688, c_6578])).
% 5.88/2.14  tff(c_6576, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6558, c_2])).
% 5.88/2.14  tff(c_6583, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6576])).
% 5.88/2.14  tff(c_6213, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5865])).
% 5.88/2.14  tff(c_6228, plain, (![A_564, B_565, C_566, C_567]: (~r1_tarski(k3_zfmisc_1(A_564, B_565, C_566), k2_zfmisc_1(C_567, C_566)) | r1_tarski(k2_zfmisc_1(A_564, B_565), C_567) | k1_xboole_0=C_566)), inference(superposition, [status(thm), theory('equality')], [c_22, c_4760])).
% 5.88/2.14  tff(c_6246, plain, (![C_567]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_567, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), C_567) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4706, c_6228])).
% 5.88/2.14  tff(c_6267, plain, (![C_568]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_568, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), C_568))), inference(negUnitSimplification, [status(thm)], [c_6213, c_6246])).
% 5.88/2.14  tff(c_6615, plain, (![A_606, B_607]: (~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k3_zfmisc_1(A_606, B_607, '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(A_606, B_607)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6267])).
% 5.88/2.14  tff(c_6634, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_6615])).
% 5.88/2.14  tff(c_6645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6583, c_6634])).
% 5.88/2.14  tff(c_6646, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_6576])).
% 5.88/2.14  tff(c_6729, plain, (![C_7]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', C_7)) | r1_tarski('#skF_5', C_7) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6646, c_14])).
% 5.88/2.14  tff(c_6945, plain, (![C_621]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', C_621)) | r1_tarski('#skF_5', C_621))), inference(negUnitSimplification, [status(thm)], [c_5843, c_6729])).
% 5.88/2.14  tff(c_6956, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_6945])).
% 5.88/2.14  tff(c_6963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6581, c_6956])).
% 5.88/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.14  
% 5.88/2.14  Inference rules
% 5.88/2.14  ----------------------
% 5.88/2.14  #Ref     : 0
% 5.88/2.14  #Sup     : 1523
% 5.88/2.14  #Fact    : 0
% 5.88/2.14  #Define  : 0
% 5.88/2.14  #Split   : 39
% 5.88/2.14  #Chain   : 0
% 5.88/2.14  #Close   : 0
% 5.88/2.14  
% 5.88/2.14  Ordering : KBO
% 5.88/2.14  
% 5.88/2.14  Simplification rules
% 5.88/2.14  ----------------------
% 5.88/2.14  #Subsume      : 435
% 5.88/2.14  #Demod        : 2035
% 5.88/2.14  #Tautology    : 683
% 5.88/2.14  #SimpNegUnit  : 137
% 5.88/2.14  #BackRed      : 511
% 5.88/2.14  
% 5.88/2.14  #Partial instantiations: 0
% 5.88/2.14  #Strategies tried      : 1
% 5.88/2.14  
% 5.88/2.14  Timing (in seconds)
% 5.88/2.14  ----------------------
% 5.88/2.14  Preprocessing        : 0.30
% 5.88/2.14  Parsing              : 0.16
% 5.88/2.14  CNF conversion       : 0.02
% 5.88/2.15  Main loop            : 1.09
% 5.88/2.15  Inferencing          : 0.35
% 5.88/2.15  Reduction            : 0.38
% 5.88/2.15  Demodulation         : 0.27
% 5.88/2.15  BG Simplification    : 0.04
% 5.88/2.15  Subsumption          : 0.24
% 5.88/2.15  Abstraction          : 0.06
% 5.88/2.15  MUC search           : 0.00
% 5.88/2.15  Cooper               : 0.00
% 5.88/2.15  Total                : 1.48
% 5.88/2.15  Index Insertion      : 0.00
% 5.88/2.15  Index Deletion       : 0.00
% 5.88/2.15  Index Matching       : 0.00
% 5.88/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
