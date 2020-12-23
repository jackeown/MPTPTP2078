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
% DateTime   : Thu Dec  3 09:54:18 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 373 expanded)
%              Number of leaves         :   19 ( 127 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 865 expanded)
%              Number of equality atoms :   29 ( 282 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_22,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_31,plain,(
    '#skF_5' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13))
      | ~ r2_hidden(B_11,D_13)
      | ~ r2_hidden(A_10,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_67,plain,(
    ! [A_31,C_32,B_33,D_34] :
      ( r2_hidden(A_31,C_32)
      | ~ r2_hidden(k4_tarski(A_31,B_33),k2_zfmisc_1(C_32,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_43,B_44),k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_67])).

tff(c_127,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,'#skF_5')
      | ~ r2_hidden(B_11,'#skF_4')
      | ~ r2_hidden(A_10,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_122])).

tff(c_688,plain,(
    ! [B_90] : ~ r2_hidden(B_90,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_704,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_688])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_704])).

tff(c_713,plain,(
    ! [A_91] :
      ( r2_hidden(A_91,'#skF_5')
      | ~ r2_hidden(A_91,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_722,plain,(
    ! [A_92] :
      ( r1_tarski(A_92,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_92,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_713,c_4])).

tff(c_732,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_722])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_734,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_732,c_10])).

tff(c_737,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_734])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( r2_hidden(k4_tarski(A_37,B_38),k2_zfmisc_1(C_39,D_40))
      | ~ r2_hidden(B_38,D_40)
      | ~ r2_hidden(A_37,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_63,plain,(
    ! [B_27,D_28,A_29,C_30] :
      ( r2_hidden(B_27,D_28)
      | ~ r2_hidden(k4_tarski(A_29,B_27),k2_zfmisc_1(C_30,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [B_27,A_29] :
      ( r2_hidden(B_27,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_29,B_27),k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_88,plain,(
    ! [B_38,A_37] :
      ( r2_hidden(B_38,'#skF_6')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_66])).

tff(c_93,plain,(
    ! [A_41] : ~ r2_hidden(A_41,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_105,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_105])).

tff(c_113,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_6')
      | ~ r2_hidden(B_42,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_128,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_45,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_133,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_136,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_10])).

tff(c_137,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_193,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(k4_tarski(A_52,B_53),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ r2_hidden(A_52,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_72])).

tff(c_18,plain,(
    ! [B_11,D_13,A_10,C_12] :
      ( r2_hidden(B_11,D_13)
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_211,plain,(
    ! [B_53,A_52] :
      ( r2_hidden(B_53,'#skF_4')
      | ~ r2_hidden(B_53,'#skF_6')
      | ~ r2_hidden(A_52,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_193,c_18])).

tff(c_221,plain,(
    ! [A_54] : ~ r2_hidden(A_54,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_235,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_221])).

tff(c_153,plain,(
    ! [B_49] : ~ r2_hidden(B_49,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_153])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_169])).

tff(c_178,plain,(
    ! [A_50] :
      ( r2_hidden(A_50,'#skF_5')
      | ~ r2_hidden(A_50,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_187,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_51,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_178,c_4])).

tff(c_192,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_214,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_192,c_10])).

tff(c_217,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_214])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_217])).

tff(c_304,plain,(
    ! [B_62] :
      ( r2_hidden(B_62,'#skF_4')
      | ~ r2_hidden(B_62,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_617,plain,(
    ! [B_84] :
      ( r2_hidden('#skF_1'('#skF_6',B_84),'#skF_4')
      | r1_tarski('#skF_6',B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_304])).

tff(c_627,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_617,c_4])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_137,c_627])).

tff(c_635,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_87,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(k4_tarski(A_37,B_38),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_6')
      | ~ r2_hidden(A_37,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_72])).

tff(c_739,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(k4_tarski(A_93,B_94),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(B_94,'#skF_4')
      | ~ r2_hidden(A_93,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_87])).

tff(c_20,plain,(
    ! [A_10,C_12,B_11,D_13] :
      ( r2_hidden(A_10,C_12)
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_752,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(A_93,'#skF_3')
      | ~ r2_hidden(B_94,'#skF_4')
      | ~ r2_hidden(A_93,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_739,c_20])).

tff(c_797,plain,(
    ! [B_100] : ~ r2_hidden(B_100,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_817,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_797])).

tff(c_825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_817])).

tff(c_827,plain,(
    ! [A_101] :
      ( r2_hidden(A_101,'#skF_3')
      | ~ r2_hidden(A_101,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_917,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_1'('#skF_5',B_109),'#skF_3')
      | r1_tarski('#skF_5',B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_827])).

tff(c_929,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_917,c_4])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_737,c_737,c_929])).

tff(c_938,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_985,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( r2_hidden(k4_tarski(A_132,B_133),k2_zfmisc_1(C_134,D_135))
      | ~ r2_hidden(B_133,D_135)
      | ~ r2_hidden(A_132,C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_939,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_945,plain,(
    k2_zfmisc_1('#skF_3','#skF_6') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_28])).

tff(c_976,plain,(
    ! [B_122,D_123,A_124,C_125] :
      ( r2_hidden(B_122,D_123)
      | ~ r2_hidden(k4_tarski(A_124,B_122),k2_zfmisc_1(C_125,D_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_979,plain,(
    ! [B_122,A_124] :
      ( r2_hidden(B_122,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_124,B_122),k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_976])).

tff(c_1001,plain,(
    ! [B_133,A_132] :
      ( r2_hidden(B_133,'#skF_6')
      | ~ r2_hidden(B_133,'#skF_4')
      | ~ r2_hidden(A_132,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_985,c_979])).

tff(c_1006,plain,(
    ! [A_136] : ~ r2_hidden(A_136,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_1018,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_1006])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1018])).

tff(c_1026,plain,(
    ! [B_137] :
      ( r2_hidden(B_137,'#skF_6')
      | ~ r2_hidden(B_137,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_1051,plain,(
    ! [A_140] :
      ( r1_tarski(A_140,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_140,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1026,c_4])).

tff(c_1056,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_1051])).

tff(c_1058,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1056,c_10])).

tff(c_1061,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_938,c_1058])).

tff(c_1035,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(k4_tarski(A_138,B_139),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(B_139,'#skF_6')
      | ~ r2_hidden(A_138,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_985])).

tff(c_1049,plain,(
    ! [B_139,A_138] :
      ( r2_hidden(B_139,'#skF_4')
      | ~ r2_hidden(B_139,'#skF_6')
      | ~ r2_hidden(A_138,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1035,c_18])).

tff(c_1063,plain,(
    ! [A_141] : ~ r2_hidden(A_141,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_1075,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_1063])).

tff(c_1081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1075])).

tff(c_1097,plain,(
    ! [B_145] :
      ( r2_hidden(B_145,'#skF_4')
      | ~ r2_hidden(B_145,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_1145,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_1'('#skF_6',B_148),'#skF_4')
      | r1_tarski('#skF_6',B_148) ) ),
    inference(resolution,[status(thm)],[c_6,c_1097])).

tff(c_1155,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1145,c_4])).

tff(c_1162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1061,c_1061,c_1155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.14/1.50  
% 3.14/1.50  %Foreground sorts:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Background operators:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Foreground operators:
% 3.14/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.50  
% 3.14/1.52  tff(f_63, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.14/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.14/1.52  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.14/1.52  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.14/1.52  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.52  tff(c_22, plain, ('#skF_6'!='#skF_4' | '#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.52  tff(c_31, plain, ('#skF_5'!='#skF_3'), inference(splitLeft, [status(thm)], [c_22])).
% 3.14/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.52  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.52  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.14/1.52  tff(c_16, plain, (![A_10, B_11, C_12, D_13]: (r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)) | ~r2_hidden(B_11, D_13) | ~r2_hidden(A_10, C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_28, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.52  tff(c_67, plain, (![A_31, C_32, B_33, D_34]: (r2_hidden(A_31, C_32) | ~r2_hidden(k4_tarski(A_31, B_33), k2_zfmisc_1(C_32, D_34)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_122, plain, (![A_43, B_44]: (r2_hidden(A_43, '#skF_5') | ~r2_hidden(k4_tarski(A_43, B_44), k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_67])).
% 3.14/1.52  tff(c_127, plain, (![A_10, B_11]: (r2_hidden(A_10, '#skF_5') | ~r2_hidden(B_11, '#skF_4') | ~r2_hidden(A_10, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_122])).
% 3.14/1.52  tff(c_688, plain, (![B_90]: (~r2_hidden(B_90, '#skF_4'))), inference(splitLeft, [status(thm)], [c_127])).
% 3.14/1.52  tff(c_704, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_688])).
% 3.14/1.52  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_704])).
% 3.14/1.52  tff(c_713, plain, (![A_91]: (r2_hidden(A_91, '#skF_5') | ~r2_hidden(A_91, '#skF_3'))), inference(splitRight, [status(thm)], [c_127])).
% 3.14/1.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.52  tff(c_722, plain, (![A_92]: (r1_tarski(A_92, '#skF_5') | ~r2_hidden('#skF_1'(A_92, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_713, c_4])).
% 3.14/1.52  tff(c_732, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_722])).
% 3.14/1.52  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.14/1.52  tff(c_734, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_732, c_10])).
% 3.14/1.52  tff(c_737, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_31, c_734])).
% 3.14/1.52  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.52  tff(c_72, plain, (![A_37, B_38, C_39, D_40]: (r2_hidden(k4_tarski(A_37, B_38), k2_zfmisc_1(C_39, D_40)) | ~r2_hidden(B_38, D_40) | ~r2_hidden(A_37, C_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_63, plain, (![B_27, D_28, A_29, C_30]: (r2_hidden(B_27, D_28) | ~r2_hidden(k4_tarski(A_29, B_27), k2_zfmisc_1(C_30, D_28)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_66, plain, (![B_27, A_29]: (r2_hidden(B_27, '#skF_6') | ~r2_hidden(k4_tarski(A_29, B_27), k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_63])).
% 3.14/1.52  tff(c_88, plain, (![B_38, A_37]: (r2_hidden(B_38, '#skF_6') | ~r2_hidden(B_38, '#skF_4') | ~r2_hidden(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_66])).
% 3.14/1.52  tff(c_93, plain, (![A_41]: (~r2_hidden(A_41, '#skF_3'))), inference(splitLeft, [status(thm)], [c_88])).
% 3.14/1.52  tff(c_105, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_93])).
% 3.14/1.52  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_105])).
% 3.14/1.52  tff(c_113, plain, (![B_42]: (r2_hidden(B_42, '#skF_6') | ~r2_hidden(B_42, '#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 3.14/1.52  tff(c_128, plain, (![A_45]: (r1_tarski(A_45, '#skF_6') | ~r2_hidden('#skF_1'(A_45, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_113, c_4])).
% 3.14/1.52  tff(c_133, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_128])).
% 3.14/1.52  tff(c_136, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_133, c_10])).
% 3.14/1.52  tff(c_137, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_136])).
% 3.14/1.52  tff(c_193, plain, (![A_52, B_53]: (r2_hidden(k4_tarski(A_52, B_53), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(B_53, '#skF_6') | ~r2_hidden(A_52, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_72])).
% 3.14/1.52  tff(c_18, plain, (![B_11, D_13, A_10, C_12]: (r2_hidden(B_11, D_13) | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_211, plain, (![B_53, A_52]: (r2_hidden(B_53, '#skF_4') | ~r2_hidden(B_53, '#skF_6') | ~r2_hidden(A_52, '#skF_5'))), inference(resolution, [status(thm)], [c_193, c_18])).
% 3.14/1.52  tff(c_221, plain, (![A_54]: (~r2_hidden(A_54, '#skF_5'))), inference(splitLeft, [status(thm)], [c_211])).
% 3.14/1.52  tff(c_235, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_221])).
% 3.14/1.52  tff(c_153, plain, (![B_49]: (~r2_hidden(B_49, '#skF_4'))), inference(splitLeft, [status(thm)], [c_127])).
% 3.14/1.52  tff(c_169, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_153])).
% 3.14/1.52  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_169])).
% 3.14/1.52  tff(c_178, plain, (![A_50]: (r2_hidden(A_50, '#skF_5') | ~r2_hidden(A_50, '#skF_3'))), inference(splitRight, [status(thm)], [c_127])).
% 3.14/1.52  tff(c_187, plain, (![A_51]: (r1_tarski(A_51, '#skF_5') | ~r2_hidden('#skF_1'(A_51, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_178, c_4])).
% 3.14/1.52  tff(c_192, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_187])).
% 3.14/1.52  tff(c_214, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_192, c_10])).
% 3.14/1.52  tff(c_217, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_31, c_214])).
% 3.14/1.52  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_217])).
% 3.14/1.52  tff(c_304, plain, (![B_62]: (r2_hidden(B_62, '#skF_4') | ~r2_hidden(B_62, '#skF_6'))), inference(splitRight, [status(thm)], [c_211])).
% 3.14/1.52  tff(c_617, plain, (![B_84]: (r2_hidden('#skF_1'('#skF_6', B_84), '#skF_4') | r1_tarski('#skF_6', B_84))), inference(resolution, [status(thm)], [c_6, c_304])).
% 3.14/1.52  tff(c_627, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_617, c_4])).
% 3.14/1.52  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_137, c_627])).
% 3.14/1.52  tff(c_635, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_136])).
% 3.14/1.52  tff(c_87, plain, (![A_37, B_38]: (r2_hidden(k4_tarski(A_37, B_38), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_6') | ~r2_hidden(A_37, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_72])).
% 3.14/1.52  tff(c_739, plain, (![A_93, B_94]: (r2_hidden(k4_tarski(A_93, B_94), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(B_94, '#skF_4') | ~r2_hidden(A_93, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_87])).
% 3.14/1.52  tff(c_20, plain, (![A_10, C_12, B_11, D_13]: (r2_hidden(A_10, C_12) | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_752, plain, (![A_93, B_94]: (r2_hidden(A_93, '#skF_3') | ~r2_hidden(B_94, '#skF_4') | ~r2_hidden(A_93, '#skF_5'))), inference(resolution, [status(thm)], [c_739, c_20])).
% 3.14/1.52  tff(c_797, plain, (![B_100]: (~r2_hidden(B_100, '#skF_4'))), inference(splitLeft, [status(thm)], [c_752])).
% 3.14/1.52  tff(c_817, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_797])).
% 3.14/1.52  tff(c_825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_817])).
% 3.14/1.52  tff(c_827, plain, (![A_101]: (r2_hidden(A_101, '#skF_3') | ~r2_hidden(A_101, '#skF_5'))), inference(splitRight, [status(thm)], [c_752])).
% 3.14/1.52  tff(c_917, plain, (![B_109]: (r2_hidden('#skF_1'('#skF_5', B_109), '#skF_3') | r1_tarski('#skF_5', B_109))), inference(resolution, [status(thm)], [c_6, c_827])).
% 3.14/1.52  tff(c_929, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_917, c_4])).
% 3.14/1.52  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_737, c_737, c_929])).
% 3.14/1.52  tff(c_938, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_22])).
% 3.14/1.52  tff(c_985, plain, (![A_132, B_133, C_134, D_135]: (r2_hidden(k4_tarski(A_132, B_133), k2_zfmisc_1(C_134, D_135)) | ~r2_hidden(B_133, D_135) | ~r2_hidden(A_132, C_134))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_939, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 3.14/1.52  tff(c_945, plain, (k2_zfmisc_1('#skF_3', '#skF_6')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_939, c_28])).
% 3.14/1.52  tff(c_976, plain, (![B_122, D_123, A_124, C_125]: (r2_hidden(B_122, D_123) | ~r2_hidden(k4_tarski(A_124, B_122), k2_zfmisc_1(C_125, D_123)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_979, plain, (![B_122, A_124]: (r2_hidden(B_122, '#skF_6') | ~r2_hidden(k4_tarski(A_124, B_122), k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_945, c_976])).
% 3.14/1.52  tff(c_1001, plain, (![B_133, A_132]: (r2_hidden(B_133, '#skF_6') | ~r2_hidden(B_133, '#skF_4') | ~r2_hidden(A_132, '#skF_3'))), inference(resolution, [status(thm)], [c_985, c_979])).
% 3.14/1.52  tff(c_1006, plain, (![A_136]: (~r2_hidden(A_136, '#skF_3'))), inference(splitLeft, [status(thm)], [c_1001])).
% 3.14/1.52  tff(c_1018, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_1006])).
% 3.14/1.52  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1018])).
% 3.14/1.52  tff(c_1026, plain, (![B_137]: (r2_hidden(B_137, '#skF_6') | ~r2_hidden(B_137, '#skF_4'))), inference(splitRight, [status(thm)], [c_1001])).
% 3.14/1.52  tff(c_1051, plain, (![A_140]: (r1_tarski(A_140, '#skF_6') | ~r2_hidden('#skF_1'(A_140, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_1026, c_4])).
% 3.14/1.52  tff(c_1056, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_1051])).
% 3.14/1.52  tff(c_1058, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1056, c_10])).
% 3.14/1.52  tff(c_1061, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_938, c_1058])).
% 3.14/1.52  tff(c_1035, plain, (![A_138, B_139]: (r2_hidden(k4_tarski(A_138, B_139), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(B_139, '#skF_6') | ~r2_hidden(A_138, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_945, c_985])).
% 3.14/1.52  tff(c_1049, plain, (![B_139, A_138]: (r2_hidden(B_139, '#skF_4') | ~r2_hidden(B_139, '#skF_6') | ~r2_hidden(A_138, '#skF_3'))), inference(resolution, [status(thm)], [c_1035, c_18])).
% 3.14/1.52  tff(c_1063, plain, (![A_141]: (~r2_hidden(A_141, '#skF_3'))), inference(splitLeft, [status(thm)], [c_1049])).
% 3.14/1.52  tff(c_1075, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_1063])).
% 3.14/1.52  tff(c_1081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1075])).
% 3.14/1.52  tff(c_1097, plain, (![B_145]: (r2_hidden(B_145, '#skF_4') | ~r2_hidden(B_145, '#skF_6'))), inference(splitRight, [status(thm)], [c_1049])).
% 3.14/1.52  tff(c_1145, plain, (![B_148]: (r2_hidden('#skF_1'('#skF_6', B_148), '#skF_4') | r1_tarski('#skF_6', B_148))), inference(resolution, [status(thm)], [c_6, c_1097])).
% 3.14/1.52  tff(c_1155, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1145, c_4])).
% 3.14/1.52  tff(c_1162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1061, c_1061, c_1155])).
% 3.14/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.52  
% 3.14/1.52  Inference rules
% 3.14/1.52  ----------------------
% 3.14/1.52  #Ref     : 0
% 3.14/1.52  #Sup     : 228
% 3.14/1.52  #Fact    : 0
% 3.14/1.52  #Define  : 0
% 3.14/1.52  #Split   : 14
% 3.14/1.52  #Chain   : 0
% 3.14/1.52  #Close   : 0
% 3.14/1.52  
% 3.14/1.52  Ordering : KBO
% 3.14/1.52  
% 3.14/1.52  Simplification rules
% 3.14/1.52  ----------------------
% 3.14/1.52  #Subsume      : 34
% 3.14/1.52  #Demod        : 73
% 3.14/1.52  #Tautology    : 70
% 3.14/1.52  #SimpNegUnit  : 20
% 3.14/1.52  #BackRed      : 40
% 3.14/1.52  
% 3.14/1.52  #Partial instantiations: 0
% 3.14/1.52  #Strategies tried      : 1
% 3.14/1.52  
% 3.14/1.52  Timing (in seconds)
% 3.14/1.52  ----------------------
% 3.14/1.52  Preprocessing        : 0.31
% 3.14/1.52  Parsing              : 0.16
% 3.14/1.52  CNF conversion       : 0.02
% 3.14/1.52  Main loop            : 0.42
% 3.14/1.52  Inferencing          : 0.16
% 3.14/1.52  Reduction            : 0.11
% 3.14/1.52  Demodulation         : 0.07
% 3.14/1.52  BG Simplification    : 0.02
% 3.14/1.52  Subsumption          : 0.09
% 3.14/1.52  Abstraction          : 0.02
% 3.14/1.52  MUC search           : 0.00
% 3.14/1.52  Cooper               : 0.00
% 3.14/1.52  Total                : 0.77
% 3.14/1.52  Index Insertion      : 0.00
% 3.14/1.52  Index Deletion       : 0.00
% 3.14/1.52  Index Matching       : 0.00
% 3.14/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
