%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:35 EST 2020

% Result     : Theorem 36.78s
% Output     : CNFRefutation 36.95s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 868 expanded)
%              Number of leaves         :   17 ( 294 expanded)
%              Depth                    :   22
%              Number of atoms          :  199 (2327 expanded)
%              Number of equality atoms :   34 ( 425 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & ! [D] :
              ( ( r1_tarski(D,B)
                & r1_tarski(D,C) )
             => r1_tarski(D,A) ) )
       => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    k3_xboole_0('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    k3_xboole_0('#skF_6','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_89,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_94,plain,(
    ! [A_26] : r1_tarski(A_26,A_26) ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_434,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_2'(A_77,B_78,C_79),A_77)
      | r2_hidden('#skF_3'(A_77,B_78,C_79),C_79)
      | k3_xboole_0(A_77,B_78) = C_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1773,plain,(
    ! [A_167,B_168,C_169,B_170] :
      ( r2_hidden('#skF_3'(A_167,B_168,C_169),B_170)
      | ~ r1_tarski(C_169,B_170)
      | r2_hidden('#skF_2'(A_167,B_168,C_169),A_167)
      | k3_xboole_0(A_167,B_168) = C_169 ) ),
    inference(resolution,[status(thm)],[c_434,c_4])).

tff(c_29952,plain,(
    ! [A_951,C_949,B_953,B_952,B_950] :
      ( r2_hidden('#skF_3'(A_951,B_952,C_949),B_953)
      | ~ r1_tarski(B_950,B_953)
      | ~ r1_tarski(C_949,B_950)
      | r2_hidden('#skF_2'(A_951,B_952,C_949),A_951)
      | k3_xboole_0(A_951,B_952) = C_949 ) ),
    inference(resolution,[status(thm)],[c_1773,c_4])).

tff(c_30564,plain,(
    ! [A_951,B_952,C_949] :
      ( r2_hidden('#skF_3'(A_951,B_952,C_949),'#skF_5')
      | ~ r1_tarski(C_949,'#skF_4')
      | r2_hidden('#skF_2'(A_951,B_952,C_949),A_951)
      | k3_xboole_0(A_951,B_952) = C_949 ) ),
    inference(resolution,[status(thm)],[c_36,c_29952])).

tff(c_270,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden('#skF_2'(A_52,B_53,C_54),B_53)
      | r2_hidden('#skF_3'(A_52,B_53,C_54),C_54)
      | k3_xboole_0(A_52,B_53) = C_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3021,plain,(
    ! [A_216,B_217,C_218,B_219] :
      ( r2_hidden('#skF_3'(A_216,B_217,C_218),B_219)
      | ~ r1_tarski(C_218,B_219)
      | r2_hidden('#skF_2'(A_216,B_217,C_218),B_217)
      | k3_xboole_0(A_216,B_217) = C_218 ) ),
    inference(resolution,[status(thm)],[c_270,c_4])).

tff(c_42900,plain,(
    ! [B_1129,C_1131,A_1132,B_1130,B_1133] :
      ( r2_hidden('#skF_3'(A_1132,B_1129,C_1131),B_1133)
      | ~ r1_tarski(B_1130,B_1133)
      | ~ r1_tarski(C_1131,B_1130)
      | r2_hidden('#skF_2'(A_1132,B_1129,C_1131),B_1129)
      | k3_xboole_0(A_1132,B_1129) = C_1131 ) ),
    inference(resolution,[status(thm)],[c_3021,c_4])).

tff(c_44061,plain,(
    ! [A_1141,B_1142,C_1143] :
      ( r2_hidden('#skF_3'(A_1141,B_1142,C_1143),'#skF_5')
      | ~ r1_tarski(C_1143,'#skF_4')
      | r2_hidden('#skF_2'(A_1141,B_1142,C_1143),B_1142)
      | k3_xboole_0(A_1141,B_1142) = C_1143 ) ),
    inference(resolution,[status(thm)],[c_36,c_42900])).

tff(c_39,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [B_20,A_21] : r1_tarski(k3_xboole_0(B_20,A_21),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_28])).

tff(c_95,plain,(
    ! [D_28] :
      ( r1_tarski(D_28,'#skF_4')
      | ~ r1_tarski(D_28,'#skF_6')
      | ~ r1_tarski(D_28,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [B_39] :
      ( r1_tarski(k3_xboole_0('#skF_5',B_39),'#skF_4')
      | ~ r1_tarski(k3_xboole_0('#skF_5',B_39),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_152,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_148])).

tff(c_162,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_202,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,k3_xboole_0(A_44,B_45))
      | ~ r2_hidden(D_43,B_45)
      | ~ r2_hidden(D_43,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_535,plain,(
    ! [D_91,B_92,A_93,B_94] :
      ( r2_hidden(D_91,B_92)
      | ~ r1_tarski(k3_xboole_0(A_93,B_94),B_92)
      | ~ r2_hidden(D_91,B_94)
      | ~ r2_hidden(D_91,A_93) ) ),
    inference(resolution,[status(thm)],[c_202,c_4])).

tff(c_549,plain,(
    ! [D_91] :
      ( r2_hidden(D_91,'#skF_4')
      | ~ r2_hidden(D_91,'#skF_5')
      | ~ r2_hidden(D_91,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_162,c_535])).

tff(c_55924,plain,(
    ! [A_1276,C_1277] :
      ( r2_hidden('#skF_2'(A_1276,'#skF_5',C_1277),'#skF_4')
      | ~ r2_hidden('#skF_2'(A_1276,'#skF_5',C_1277),'#skF_6')
      | r2_hidden('#skF_3'(A_1276,'#skF_5',C_1277),'#skF_5')
      | ~ r1_tarski(C_1277,'#skF_4')
      | k3_xboole_0(A_1276,'#skF_5') = C_1277 ) ),
    inference(resolution,[status(thm)],[c_44061,c_549])).

tff(c_57907,plain,(
    ! [C_1297] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_5',C_1297),'#skF_4')
      | r2_hidden('#skF_3'('#skF_6','#skF_5',C_1297),'#skF_5')
      | ~ r1_tarski(C_1297,'#skF_4')
      | k3_xboole_0('#skF_6','#skF_5') = C_1297 ) ),
    inference(resolution,[status(thm)],[c_30564,c_55924])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k3_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57928,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_4')
    | r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_57907,c_22])).

tff(c_57950,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_4')
    | r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_5')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_57928])).

tff(c_57951,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_4')
    | r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_57950])).

tff(c_57953,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_57951])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k3_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57971,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_57953,c_20])).

tff(c_57988,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_57971])).

tff(c_58764,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_57988])).

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30563,plain,(
    ! [A_951,B_952,C_949] :
      ( r2_hidden('#skF_3'(A_951,B_952,C_949),'#skF_6')
      | ~ r1_tarski(C_949,'#skF_4')
      | r2_hidden('#skF_2'(A_951,B_952,C_949),A_951)
      | k3_xboole_0(A_951,B_952) = C_949 ) ),
    inference(resolution,[status(thm)],[c_34,c_29952])).

tff(c_43642,plain,(
    ! [A_1134,B_1135,C_1136] :
      ( r2_hidden('#skF_3'(A_1134,B_1135,C_1136),'#skF_6')
      | ~ r1_tarski(C_1136,'#skF_4')
      | r2_hidden('#skF_2'(A_1134,B_1135,C_1136),B_1135)
      | k3_xboole_0(A_1134,B_1135) = C_1136 ) ),
    inference(resolution,[status(thm)],[c_34,c_42900])).

tff(c_69145,plain,(
    ! [A_1435,C_1436] :
      ( r2_hidden('#skF_2'(A_1435,'#skF_5',C_1436),'#skF_4')
      | ~ r2_hidden('#skF_2'(A_1435,'#skF_5',C_1436),'#skF_6')
      | r2_hidden('#skF_3'(A_1435,'#skF_5',C_1436),'#skF_6')
      | ~ r1_tarski(C_1436,'#skF_4')
      | k3_xboole_0(A_1435,'#skF_5') = C_1436 ) ),
    inference(resolution,[status(thm)],[c_43642,c_549])).

tff(c_69762,plain,(
    ! [C_1442] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_5',C_1442),'#skF_4')
      | r2_hidden('#skF_3'('#skF_6','#skF_5',C_1442),'#skF_6')
      | ~ r1_tarski(C_1442,'#skF_4')
      | k3_xboole_0('#skF_6','#skF_5') = C_1442 ) ),
    inference(resolution,[status(thm)],[c_30563,c_69145])).

tff(c_69783,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_4')
    | r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6')
    | ~ r1_tarski('#skF_4','#skF_4')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_69762,c_22])).

tff(c_69805,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_4')
    | r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_69783])).

tff(c_69806,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_58764,c_69805])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_144,plain,(
    ! [C_36,B_37,A_38] :
      ( r2_hidden(C_36,B_37)
      | ~ r2_hidden(C_36,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_225,plain,(
    ! [A_46,B_47,B_48] :
      ( r2_hidden('#skF_1'(A_46,B_47),B_48)
      | ~ r1_tarski(A_46,B_48)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_635,plain,(
    ! [A_98,B_99,B_100,B_101] :
      ( r2_hidden('#skF_1'(A_98,B_99),B_100)
      | ~ r1_tarski(B_101,B_100)
      | ~ r1_tarski(A_98,B_101)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_225,c_4])).

tff(c_654,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102,B_103),'#skF_6')
      | ~ r1_tarski(A_102,'#skF_4')
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_34,c_635])).

tff(c_668,plain,(
    ! [A_104] :
      ( ~ r1_tarski(A_104,'#skF_4')
      | r1_tarski(A_104,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_654,c_6])).

tff(c_221,plain,(
    ! [D_43,B_4,A_44,B_45] :
      ( r2_hidden(D_43,B_4)
      | ~ r1_tarski(k3_xboole_0(A_44,B_45),B_4)
      | ~ r2_hidden(D_43,B_45)
      | ~ r2_hidden(D_43,A_44) ) ),
    inference(resolution,[status(thm)],[c_202,c_4])).

tff(c_690,plain,(
    ! [D_43,B_45,A_44] :
      ( r2_hidden(D_43,'#skF_6')
      | ~ r2_hidden(D_43,B_45)
      | ~ r2_hidden(D_43,A_44)
      | ~ r1_tarski(k3_xboole_0(A_44,B_45),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_668,c_221])).

tff(c_69821,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),A_44)
      | ~ r1_tarski(k3_xboole_0(A_44,'#skF_4'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69806,c_690])).

tff(c_69836,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69821])).

tff(c_69837,plain,(
    ! [A_44] : ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),A_44) ),
    inference(negUnitSimplification,[status(thm)],[c_58764,c_69836])).

tff(c_69850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69837,c_69806])).

tff(c_69852,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_57988])).

tff(c_69851,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_57988])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k3_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69870,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_5')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_69852,c_18])).

tff(c_69887,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_5')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57953,c_69870])).

tff(c_69888,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_69887])).

tff(c_69945,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_69888,c_549])).

tff(c_69960,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_5','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69851,c_69945])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k3_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70349,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_6')
    | k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_69960,c_16])).

tff(c_70370,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69852,c_57953,c_70349])).

tff(c_70372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_70370])).

tff(c_70373,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_57951])).

tff(c_70632,plain,(
    ! [B_1452] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),B_1452)
      | ~ r1_tarski('#skF_4',B_1452) ) ),
    inference(resolution,[status(thm)],[c_70373,c_4])).

tff(c_70374,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_5','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_57951])).

tff(c_70635,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70632,c_70374])).

tff(c_70754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_70635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.78/26.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.78/26.68  
% 36.78/26.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.78/26.68  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 36.78/26.68  
% 36.78/26.68  %Foreground sorts:
% 36.78/26.68  
% 36.78/26.68  
% 36.78/26.68  %Background operators:
% 36.78/26.68  
% 36.78/26.68  
% 36.78/26.68  %Foreground operators:
% 36.78/26.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.78/26.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.78/26.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.78/26.68  tff('#skF_5', type, '#skF_5': $i).
% 36.78/26.68  tff('#skF_6', type, '#skF_6': $i).
% 36.78/26.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 36.78/26.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.78/26.68  tff('#skF_4', type, '#skF_4': $i).
% 36.78/26.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 36.78/26.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.78/26.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.78/26.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.78/26.68  
% 36.95/26.70  tff(f_59, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 36.95/26.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 36.95/26.70  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 36.95/26.70  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 36.95/26.70  tff(f_45, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 36.95/26.70  tff(c_36, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.95/26.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.95/26.70  tff(c_30, plain, (k3_xboole_0('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.95/26.70  tff(c_37, plain, (k3_xboole_0('#skF_6', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 36.95/26.70  tff(c_89, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), A_26) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.95/26.70  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.95/26.70  tff(c_94, plain, (![A_26]: (r1_tarski(A_26, A_26))), inference(resolution, [status(thm)], [c_89, c_6])).
% 36.95/26.70  tff(c_434, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_2'(A_77, B_78, C_79), A_77) | r2_hidden('#skF_3'(A_77, B_78, C_79), C_79) | k3_xboole_0(A_77, B_78)=C_79)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.95/26.70  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.95/26.70  tff(c_1773, plain, (![A_167, B_168, C_169, B_170]: (r2_hidden('#skF_3'(A_167, B_168, C_169), B_170) | ~r1_tarski(C_169, B_170) | r2_hidden('#skF_2'(A_167, B_168, C_169), A_167) | k3_xboole_0(A_167, B_168)=C_169)), inference(resolution, [status(thm)], [c_434, c_4])).
% 36.95/26.70  tff(c_29952, plain, (![A_951, C_949, B_953, B_952, B_950]: (r2_hidden('#skF_3'(A_951, B_952, C_949), B_953) | ~r1_tarski(B_950, B_953) | ~r1_tarski(C_949, B_950) | r2_hidden('#skF_2'(A_951, B_952, C_949), A_951) | k3_xboole_0(A_951, B_952)=C_949)), inference(resolution, [status(thm)], [c_1773, c_4])).
% 36.95/26.70  tff(c_30564, plain, (![A_951, B_952, C_949]: (r2_hidden('#skF_3'(A_951, B_952, C_949), '#skF_5') | ~r1_tarski(C_949, '#skF_4') | r2_hidden('#skF_2'(A_951, B_952, C_949), A_951) | k3_xboole_0(A_951, B_952)=C_949)), inference(resolution, [status(thm)], [c_36, c_29952])).
% 36.95/26.70  tff(c_270, plain, (![A_52, B_53, C_54]: (r2_hidden('#skF_2'(A_52, B_53, C_54), B_53) | r2_hidden('#skF_3'(A_52, B_53, C_54), C_54) | k3_xboole_0(A_52, B_53)=C_54)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.95/26.70  tff(c_3021, plain, (![A_216, B_217, C_218, B_219]: (r2_hidden('#skF_3'(A_216, B_217, C_218), B_219) | ~r1_tarski(C_218, B_219) | r2_hidden('#skF_2'(A_216, B_217, C_218), B_217) | k3_xboole_0(A_216, B_217)=C_218)), inference(resolution, [status(thm)], [c_270, c_4])).
% 36.95/26.70  tff(c_42900, plain, (![B_1129, C_1131, A_1132, B_1130, B_1133]: (r2_hidden('#skF_3'(A_1132, B_1129, C_1131), B_1133) | ~r1_tarski(B_1130, B_1133) | ~r1_tarski(C_1131, B_1130) | r2_hidden('#skF_2'(A_1132, B_1129, C_1131), B_1129) | k3_xboole_0(A_1132, B_1129)=C_1131)), inference(resolution, [status(thm)], [c_3021, c_4])).
% 36.95/26.70  tff(c_44061, plain, (![A_1141, B_1142, C_1143]: (r2_hidden('#skF_3'(A_1141, B_1142, C_1143), '#skF_5') | ~r1_tarski(C_1143, '#skF_4') | r2_hidden('#skF_2'(A_1141, B_1142, C_1143), B_1142) | k3_xboole_0(A_1141, B_1142)=C_1143)), inference(resolution, [status(thm)], [c_36, c_42900])).
% 36.95/26.70  tff(c_39, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.95/26.70  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.95/26.70  tff(c_54, plain, (![B_20, A_21]: (r1_tarski(k3_xboole_0(B_20, A_21), A_21))), inference(superposition, [status(thm), theory('equality')], [c_39, c_28])).
% 36.95/26.70  tff(c_95, plain, (![D_28]: (r1_tarski(D_28, '#skF_4') | ~r1_tarski(D_28, '#skF_6') | ~r1_tarski(D_28, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.95/26.70  tff(c_148, plain, (![B_39]: (r1_tarski(k3_xboole_0('#skF_5', B_39), '#skF_4') | ~r1_tarski(k3_xboole_0('#skF_5', B_39), '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_95])).
% 36.95/26.70  tff(c_152, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_54, c_148])).
% 36.95/26.70  tff(c_162, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_152])).
% 36.95/26.70  tff(c_202, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, k3_xboole_0(A_44, B_45)) | ~r2_hidden(D_43, B_45) | ~r2_hidden(D_43, A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.95/26.70  tff(c_535, plain, (![D_91, B_92, A_93, B_94]: (r2_hidden(D_91, B_92) | ~r1_tarski(k3_xboole_0(A_93, B_94), B_92) | ~r2_hidden(D_91, B_94) | ~r2_hidden(D_91, A_93))), inference(resolution, [status(thm)], [c_202, c_4])).
% 36.95/26.70  tff(c_549, plain, (![D_91]: (r2_hidden(D_91, '#skF_4') | ~r2_hidden(D_91, '#skF_5') | ~r2_hidden(D_91, '#skF_6'))), inference(resolution, [status(thm)], [c_162, c_535])).
% 36.95/26.70  tff(c_55924, plain, (![A_1276, C_1277]: (r2_hidden('#skF_2'(A_1276, '#skF_5', C_1277), '#skF_4') | ~r2_hidden('#skF_2'(A_1276, '#skF_5', C_1277), '#skF_6') | r2_hidden('#skF_3'(A_1276, '#skF_5', C_1277), '#skF_5') | ~r1_tarski(C_1277, '#skF_4') | k3_xboole_0(A_1276, '#skF_5')=C_1277)), inference(resolution, [status(thm)], [c_44061, c_549])).
% 36.95/26.70  tff(c_57907, plain, (![C_1297]: (r2_hidden('#skF_2'('#skF_6', '#skF_5', C_1297), '#skF_4') | r2_hidden('#skF_3'('#skF_6', '#skF_5', C_1297), '#skF_5') | ~r1_tarski(C_1297, '#skF_4') | k3_xboole_0('#skF_6', '#skF_5')=C_1297)), inference(resolution, [status(thm)], [c_30564, c_55924])).
% 36.95/26.70  tff(c_22, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k3_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.95/26.70  tff(c_57928, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_4') | r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_57907, c_22])).
% 36.95/26.70  tff(c_57950, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_4') | r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_5') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_57928])).
% 36.95/26.70  tff(c_57951, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_4') | r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_37, c_57950])).
% 36.95/26.70  tff(c_57953, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_57951])).
% 36.95/26.70  tff(c_20, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_2'(A_8, B_9, C_10), A_8) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), B_9) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k3_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.95/26.70  tff(c_57971, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_57953, c_20])).
% 36.95/26.70  tff(c_57988, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_37, c_57971])).
% 36.95/26.70  tff(c_58764, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_57988])).
% 36.95/26.70  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.95/26.70  tff(c_30563, plain, (![A_951, B_952, C_949]: (r2_hidden('#skF_3'(A_951, B_952, C_949), '#skF_6') | ~r1_tarski(C_949, '#skF_4') | r2_hidden('#skF_2'(A_951, B_952, C_949), A_951) | k3_xboole_0(A_951, B_952)=C_949)), inference(resolution, [status(thm)], [c_34, c_29952])).
% 36.95/26.70  tff(c_43642, plain, (![A_1134, B_1135, C_1136]: (r2_hidden('#skF_3'(A_1134, B_1135, C_1136), '#skF_6') | ~r1_tarski(C_1136, '#skF_4') | r2_hidden('#skF_2'(A_1134, B_1135, C_1136), B_1135) | k3_xboole_0(A_1134, B_1135)=C_1136)), inference(resolution, [status(thm)], [c_34, c_42900])).
% 36.95/26.70  tff(c_69145, plain, (![A_1435, C_1436]: (r2_hidden('#skF_2'(A_1435, '#skF_5', C_1436), '#skF_4') | ~r2_hidden('#skF_2'(A_1435, '#skF_5', C_1436), '#skF_6') | r2_hidden('#skF_3'(A_1435, '#skF_5', C_1436), '#skF_6') | ~r1_tarski(C_1436, '#skF_4') | k3_xboole_0(A_1435, '#skF_5')=C_1436)), inference(resolution, [status(thm)], [c_43642, c_549])).
% 36.95/26.70  tff(c_69762, plain, (![C_1442]: (r2_hidden('#skF_2'('#skF_6', '#skF_5', C_1442), '#skF_4') | r2_hidden('#skF_3'('#skF_6', '#skF_5', C_1442), '#skF_6') | ~r1_tarski(C_1442, '#skF_4') | k3_xboole_0('#skF_6', '#skF_5')=C_1442)), inference(resolution, [status(thm)], [c_30563, c_69145])).
% 36.95/26.70  tff(c_69783, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_4') | r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | ~r1_tarski('#skF_4', '#skF_4') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_69762, c_22])).
% 36.95/26.70  tff(c_69805, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_4') | r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_69783])).
% 36.95/26.70  tff(c_69806, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_37, c_58764, c_69805])).
% 36.95/26.70  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.95/26.70  tff(c_144, plain, (![C_36, B_37, A_38]: (r2_hidden(C_36, B_37) | ~r2_hidden(C_36, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.95/26.70  tff(c_225, plain, (![A_46, B_47, B_48]: (r2_hidden('#skF_1'(A_46, B_47), B_48) | ~r1_tarski(A_46, B_48) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_8, c_144])).
% 36.95/26.70  tff(c_635, plain, (![A_98, B_99, B_100, B_101]: (r2_hidden('#skF_1'(A_98, B_99), B_100) | ~r1_tarski(B_101, B_100) | ~r1_tarski(A_98, B_101) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_225, c_4])).
% 36.95/26.70  tff(c_654, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102, B_103), '#skF_6') | ~r1_tarski(A_102, '#skF_4') | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_34, c_635])).
% 36.95/26.70  tff(c_668, plain, (![A_104]: (~r1_tarski(A_104, '#skF_4') | r1_tarski(A_104, '#skF_6'))), inference(resolution, [status(thm)], [c_654, c_6])).
% 36.95/26.70  tff(c_221, plain, (![D_43, B_4, A_44, B_45]: (r2_hidden(D_43, B_4) | ~r1_tarski(k3_xboole_0(A_44, B_45), B_4) | ~r2_hidden(D_43, B_45) | ~r2_hidden(D_43, A_44))), inference(resolution, [status(thm)], [c_202, c_4])).
% 36.95/26.70  tff(c_690, plain, (![D_43, B_45, A_44]: (r2_hidden(D_43, '#skF_6') | ~r2_hidden(D_43, B_45) | ~r2_hidden(D_43, A_44) | ~r1_tarski(k3_xboole_0(A_44, B_45), '#skF_4'))), inference(resolution, [status(thm)], [c_668, c_221])).
% 36.95/26.70  tff(c_69821, plain, (![A_44]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), A_44) | ~r1_tarski(k3_xboole_0(A_44, '#skF_4'), '#skF_4'))), inference(resolution, [status(thm)], [c_69806, c_690])).
% 36.95/26.70  tff(c_69836, plain, (![A_44]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), A_44))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69821])).
% 36.95/26.70  tff(c_69837, plain, (![A_44]: (~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), A_44))), inference(negUnitSimplification, [status(thm)], [c_58764, c_69836])).
% 36.95/26.70  tff(c_69850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69837, c_69806])).
% 36.95/26.70  tff(c_69852, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_57988])).
% 36.95/26.70  tff(c_69851, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_57988])).
% 36.95/26.70  tff(c_18, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_2'(A_8, B_9, C_10), B_9) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), B_9) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k3_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.95/26.70  tff(c_69870, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_5') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_69852, c_18])).
% 36.95/26.70  tff(c_69887, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_5') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57953, c_69870])).
% 36.95/26.70  tff(c_69888, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_37, c_69887])).
% 36.95/26.70  tff(c_69945, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_69888, c_549])).
% 36.95/26.70  tff(c_69960, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69851, c_69945])).
% 36.95/26.70  tff(c_16, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), B_9) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k3_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.95/26.70  tff(c_70349, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_6') | k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_69960, c_16])).
% 36.95/26.70  tff(c_70370, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69852, c_57953, c_70349])).
% 36.95/26.70  tff(c_70372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_70370])).
% 36.95/26.70  tff(c_70373, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_57951])).
% 36.95/26.70  tff(c_70632, plain, (![B_1452]: (r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), B_1452) | ~r1_tarski('#skF_4', B_1452))), inference(resolution, [status(thm)], [c_70373, c_4])).
% 36.95/26.70  tff(c_70374, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_57951])).
% 36.95/26.70  tff(c_70635, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70632, c_70374])).
% 36.95/26.70  tff(c_70754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_70635])).
% 36.95/26.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.95/26.70  
% 36.95/26.70  Inference rules
% 36.95/26.70  ----------------------
% 36.95/26.70  #Ref     : 0
% 36.95/26.70  #Sup     : 17863
% 36.95/26.70  #Fact    : 0
% 36.95/26.70  #Define  : 0
% 36.95/26.70  #Split   : 5
% 36.95/26.70  #Chain   : 0
% 36.95/26.70  #Close   : 0
% 36.95/26.70  
% 36.95/26.70  Ordering : KBO
% 36.95/26.70  
% 36.95/26.70  Simplification rules
% 36.95/26.70  ----------------------
% 36.95/26.70  #Subsume      : 4816
% 36.95/26.70  #Demod        : 3573
% 36.95/26.70  #Tautology    : 1450
% 36.95/26.70  #SimpNegUnit  : 64
% 36.95/26.70  #BackRed      : 11
% 36.95/26.70  
% 36.95/26.70  #Partial instantiations: 0
% 36.95/26.70  #Strategies tried      : 1
% 36.95/26.70  
% 36.95/26.70  Timing (in seconds)
% 36.95/26.70  ----------------------
% 36.95/26.70  Preprocessing        : 0.27
% 36.95/26.70  Parsing              : 0.14
% 36.95/26.70  CNF conversion       : 0.02
% 36.95/26.70  Main loop            : 25.60
% 36.95/26.70  Inferencing          : 2.16
% 36.95/26.70  Reduction            : 6.55
% 36.95/26.70  Demodulation         : 5.59
% 36.95/26.70  BG Simplification    : 0.28
% 36.95/26.70  Subsumption          : 15.62
% 36.95/26.70  Abstraction          : 0.40
% 36.95/26.70  MUC search           : 0.00
% 36.95/26.70  Cooper               : 0.00
% 36.95/26.70  Total                : 25.91
% 36.95/26.70  Index Insertion      : 0.00
% 36.95/26.70  Index Deletion       : 0.00
% 36.95/26.70  Index Matching       : 0.00
% 36.95/26.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
