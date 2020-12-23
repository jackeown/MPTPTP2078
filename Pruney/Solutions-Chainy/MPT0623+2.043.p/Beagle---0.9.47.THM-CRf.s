%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:11 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 330 expanded)
%              Number of leaves         :   33 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 ( 898 expanded)
%              Number of equality atoms :   87 ( 403 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = B
      & ! [D] :
          ( r2_hidden(D,B)
         => k1_funct_1(C,D) = o_1_0_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_97,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_46,plain,(
    ! [A_21,B_22] : v1_relat_1('#skF_7'(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_21,B_22] : v1_funct_1('#skF_7'(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_21,B_22] : k1_relat_1('#skF_7'(A_21,B_22)) = B_22 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r2_hidden('#skF_3'(A_6,B_7),A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_4'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_176,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [A_102,B_103,B_104] :
      ( r2_hidden('#skF_4'(A_102,B_103),B_104)
      | ~ r1_tarski(A_102,B_104)
      | r1_xboole_0(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_20,c_176])).

tff(c_24,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_303,plain,(
    ! [A_110,A_111,B_112] :
      ( A_110 = '#skF_4'(A_111,B_112)
      | ~ r1_tarski(A_111,k1_tarski(A_110))
      | r1_xboole_0(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_275,c_24])).

tff(c_412,plain,(
    ! [XT_250,B_114] :
      ( k1_tarski(XT_250) = '#skF_4'(k1_xboole_0,B_114)
      | r1_xboole_0(k1_xboole_0,B_114) ) ),
    inference(resolution,[status(thm)],[c_22,c_303])).

tff(c_187,plain,(
    ! [A_9,B_10,B_75] :
      ( r2_hidden('#skF_4'(A_9,B_10),B_75)
      | ~ r1_tarski(A_9,B_75)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_176])).

tff(c_415,plain,(
    ! [XT_250,B_75,B_114] :
      ( r2_hidden(k1_tarski(XT_250),B_75)
      | ~ r1_tarski(k1_xboole_0,B_75)
      | r1_xboole_0(k1_xboole_0,B_114)
      | r1_xboole_0(k1_xboole_0,B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_187])).

tff(c_874,plain,(
    ! [XT_250,B_75,B_114] :
      ( r2_hidden(k1_tarski(XT_250),B_75)
      | r1_xboole_0(k1_xboole_0,B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_415])).

tff(c_902,plain,(
    ! [B_1078] : r1_xboole_0(k1_xboole_0,B_1078) ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_16,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_906,plain,(
    ! [C_1079,B_1080] :
      ( ~ r2_hidden(C_1079,B_1080)
      | ~ r2_hidden(C_1079,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_902,c_16])).

tff(c_954,plain,(
    ! [C_1083] : ~ r2_hidden(C_1083,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_906])).

tff(c_989,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_7),B_7)
      | k1_xboole_0 = B_7 ) ),
    inference(resolution,[status(thm)],[c_14,c_954])).

tff(c_50,plain,(
    ! [A_28,B_32] :
      ( k1_relat_1('#skF_8'(A_28,B_32)) = A_28
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ! [A_28,B_32] :
      ( v1_funct_1('#skF_8'(A_28,B_32))
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    ! [A_28,B_32] :
      ( v1_relat_1('#skF_8'(A_28,B_32))
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_135,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_205,plain,(
    ! [A_85,B_86] :
      ( '#skF_1'(k1_tarski(A_85),B_86) = A_85
      | r1_tarski(k1_tarski(A_85),B_86) ) ),
    inference(resolution,[status(thm)],[c_135,c_24])).

tff(c_163,plain,(
    ! [A_69,B_70] :
      ( k2_relat_1('#skF_8'(A_69,B_70)) = k1_tarski(B_70)
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    ! [C_35] :
      ( ~ r1_tarski(k2_relat_1(C_35),'#skF_9')
      | k1_relat_1(C_35) != '#skF_10'
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_169,plain,(
    ! [B_70,A_69] :
      ( ~ r1_tarski(k1_tarski(B_70),'#skF_9')
      | k1_relat_1('#skF_8'(A_69,B_70)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_69,B_70))
      | ~ v1_relat_1('#skF_8'(A_69,B_70))
      | k1_xboole_0 = A_69 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_56])).

tff(c_298,plain,(
    ! [A_108,A_109] :
      ( k1_relat_1('#skF_8'(A_108,A_109)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_108,A_109))
      | ~ v1_relat_1('#skF_8'(A_108,A_109))
      | k1_xboole_0 = A_108
      | '#skF_1'(k1_tarski(A_109),'#skF_9') = A_109 ) ),
    inference(resolution,[status(thm)],[c_205,c_169])).

tff(c_1063,plain,(
    ! [A_1096,B_1097] :
      ( k1_relat_1('#skF_8'(A_1096,B_1097)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_1096,B_1097))
      | '#skF_1'(k1_tarski(B_1097),'#skF_9') = B_1097
      | k1_xboole_0 = A_1096 ) ),
    inference(resolution,[status(thm)],[c_54,c_298])).

tff(c_1308,plain,(
    ! [A_1113,B_1114] :
      ( k1_relat_1('#skF_8'(A_1113,B_1114)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_1114),'#skF_9') = B_1114
      | k1_xboole_0 = A_1113 ) ),
    inference(resolution,[status(thm)],[c_52,c_1063])).

tff(c_1311,plain,(
    ! [A_28,B_32] :
      ( A_28 != '#skF_10'
      | '#skF_1'(k1_tarski(B_32),'#skF_9') = B_32
      | k1_xboole_0 = A_28
      | k1_xboole_0 = A_28 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1308])).

tff(c_1429,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1311])).

tff(c_105,plain,(
    ! [A_59] :
      ( k2_relat_1(A_59) = k1_xboole_0
      | k1_relat_1(A_59) != k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    ! [A_21,B_22] :
      ( k2_relat_1('#skF_7'(A_21,B_22)) = k1_xboole_0
      | k1_relat_1('#skF_7'(A_21,B_22)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_116,plain,(
    ! [A_60,B_61] :
      ( k2_relat_1('#skF_7'(A_60,B_61)) = k1_xboole_0
      | k1_xboole_0 != B_61 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_111])).

tff(c_122,plain,(
    ! [A_60,B_61] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_9')
      | k1_relat_1('#skF_7'(A_60,B_61)) != '#skF_10'
      | ~ v1_funct_1('#skF_7'(A_60,B_61))
      | ~ v1_relat_1('#skF_7'(A_60,B_61))
      | k1_xboole_0 != B_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_56])).

tff(c_128,plain,(
    ! [B_61] :
      ( B_61 != '#skF_10'
      | k1_xboole_0 != B_61 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_22,c_122])).

tff(c_133,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_128])).

tff(c_1462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1429,c_133])).

tff(c_1465,plain,(
    ! [B_1128] : '#skF_1'(k1_tarski(B_1128),'#skF_9') = B_1128 ),
    inference(splitRight,[status(thm)],[c_1311])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1493,plain,(
    ! [B_1129] :
      ( ~ r2_hidden(B_1129,'#skF_9')
      | r1_tarski(k1_tarski(B_1129),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_4])).

tff(c_1513,plain,(
    ! [A_1132,B_1133] :
      ( k1_relat_1('#skF_8'(A_1132,B_1133)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_1132,B_1133))
      | ~ v1_relat_1('#skF_8'(A_1132,B_1133))
      | k1_xboole_0 = A_1132
      | ~ r2_hidden(B_1133,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1493,c_169])).

tff(c_1570,plain,(
    ! [A_1137,B_1138] :
      ( k1_relat_1('#skF_8'(A_1137,B_1138)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_1137,B_1138))
      | ~ r2_hidden(B_1138,'#skF_9')
      | k1_xboole_0 = A_1137 ) ),
    inference(resolution,[status(thm)],[c_54,c_1513])).

tff(c_1607,plain,(
    ! [A_1141,B_1142] :
      ( k1_relat_1('#skF_8'(A_1141,B_1142)) != '#skF_10'
      | ~ r2_hidden(B_1142,'#skF_9')
      | k1_xboole_0 = A_1141 ) ),
    inference(resolution,[status(thm)],[c_52,c_1570])).

tff(c_1610,plain,(
    ! [A_28,B_32] :
      ( A_28 != '#skF_10'
      | ~ r2_hidden(B_32,'#skF_9')
      | k1_xboole_0 = A_28
      | k1_xboole_0 = A_28 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1607])).

tff(c_1612,plain,(
    ! [B_1143] : ~ r2_hidden(B_1143,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1610])).

tff(c_1628,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_989,c_1612])).

tff(c_1669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1628])).

tff(c_1671,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_1610])).

tff(c_1706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_133])).

tff(c_1708,plain,(
    ! [XT_1144,B_1145] : r2_hidden(k1_tarski(XT_1144),B_1145) ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_1738,plain,(
    ! [XT_1168] : k1_tarski(XT_1168) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1708,c_24])).

tff(c_1719,plain,(
    ! [XT_1144,A_15] : k1_tarski(XT_1144) = A_15 ),
    inference(resolution,[status(thm)],[c_1708,c_24])).

tff(c_2187,plain,(
    ! [A_2030] : A_2030 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_1738,c_1719])).

tff(c_2273,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2187,c_133])).

tff(c_2275,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2274,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2281,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2275,c_2274])).

tff(c_2276,plain,(
    ! [A_14] : r1_tarski('#skF_10',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_22])).

tff(c_2292,plain,(
    ! [A_14] : r1_tarski('#skF_9',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2276])).

tff(c_38,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = k1_xboole_0
      | k1_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2330,plain,(
    ! [A_2931] :
      ( k2_relat_1(A_2931) = '#skF_9'
      | k1_relat_1(A_2931) != '#skF_9'
      | ~ v1_relat_1(A_2931) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2275,c_2275,c_38])).

tff(c_2336,plain,(
    ! [A_21,B_22] :
      ( k2_relat_1('#skF_7'(A_21,B_22)) = '#skF_9'
      | k1_relat_1('#skF_7'(A_21,B_22)) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_46,c_2330])).

tff(c_2341,plain,(
    ! [A_2932,B_2933] :
      ( k2_relat_1('#skF_7'(A_2932,B_2933)) = '#skF_9'
      | B_2933 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2336])).

tff(c_2287,plain,(
    ! [C_35] :
      ( ~ r1_tarski(k2_relat_1(C_35),'#skF_9')
      | k1_relat_1(C_35) != '#skF_9'
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_56])).

tff(c_2347,plain,(
    ! [A_2932,B_2933] :
      ( ~ r1_tarski('#skF_9','#skF_9')
      | k1_relat_1('#skF_7'(A_2932,B_2933)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_2932,B_2933))
      | ~ v1_relat_1('#skF_7'(A_2932,B_2933))
      | B_2933 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2341,c_2287])).

tff(c_2353,plain,(
    ! [B_2933] : B_2933 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2292,c_2347])).

tff(c_2362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2353,c_2281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:49:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.69  
% 3.88/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 3.88/1.69  
% 3.88/1.69  %Foreground sorts:
% 3.88/1.69  
% 3.88/1.69  
% 3.88/1.69  %Background operators:
% 3.88/1.69  
% 3.88/1.69  
% 3.88/1.69  %Foreground operators:
% 3.88/1.69  tff(o_1_0_funct_1, type, o_1_0_funct_1: $i > $i).
% 3.88/1.69  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.88/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.88/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.88/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.69  tff('#skF_10', type, '#skF_10': $i).
% 3.88/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.88/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.88/1.69  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.88/1.69  tff('#skF_9', type, '#skF_9': $i).
% 3.88/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.88/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.88/1.69  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.88/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.88/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.88/1.69  
% 3.88/1.71  tff(f_84, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = B)) & (![D]: (r2_hidden(D, B) => (k1_funct_1(C, D) = o_1_0_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e1_27_1__funct_1)).
% 3.88/1.71  tff(f_115, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.88/1.71  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.88/1.71  tff(f_66, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.88/1.71  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.88/1.71  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.88/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.88/1.71  tff(f_97, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.88/1.71  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.88/1.71  tff(c_46, plain, (![A_21, B_22]: (v1_relat_1('#skF_7'(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.88/1.71  tff(c_44, plain, (![A_21, B_22]: (v1_funct_1('#skF_7'(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.88/1.71  tff(c_42, plain, (![A_21, B_22]: (k1_relat_1('#skF_7'(A_21, B_22))=B_22)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.88/1.71  tff(c_58, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.88/1.71  tff(c_60, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_58])).
% 3.88/1.71  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r2_hidden('#skF_3'(A_6, B_7), A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.71  tff(c_26, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.88/1.71  tff(c_22, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.88/1.71  tff(c_20, plain, (![A_9, B_10]: (r2_hidden('#skF_4'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.88/1.71  tff(c_176, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.71  tff(c_275, plain, (![A_102, B_103, B_104]: (r2_hidden('#skF_4'(A_102, B_103), B_104) | ~r1_tarski(A_102, B_104) | r1_xboole_0(A_102, B_103))), inference(resolution, [status(thm)], [c_20, c_176])).
% 3.88/1.71  tff(c_24, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.88/1.71  tff(c_303, plain, (![A_110, A_111, B_112]: (A_110='#skF_4'(A_111, B_112) | ~r1_tarski(A_111, k1_tarski(A_110)) | r1_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_275, c_24])).
% 3.88/1.71  tff(c_412, plain, (![XT_250, B_114]: (k1_tarski(XT_250)='#skF_4'(k1_xboole_0, B_114) | r1_xboole_0(k1_xboole_0, B_114))), inference(resolution, [status(thm)], [c_22, c_303])).
% 3.88/1.71  tff(c_187, plain, (![A_9, B_10, B_75]: (r2_hidden('#skF_4'(A_9, B_10), B_75) | ~r1_tarski(A_9, B_75) | r1_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_20, c_176])).
% 3.88/1.71  tff(c_415, plain, (![XT_250, B_75, B_114]: (r2_hidden(k1_tarski(XT_250), B_75) | ~r1_tarski(k1_xboole_0, B_75) | r1_xboole_0(k1_xboole_0, B_114) | r1_xboole_0(k1_xboole_0, B_114))), inference(superposition, [status(thm), theory('equality')], [c_412, c_187])).
% 3.88/1.71  tff(c_874, plain, (![XT_250, B_75, B_114]: (r2_hidden(k1_tarski(XT_250), B_75) | r1_xboole_0(k1_xboole_0, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_415])).
% 3.88/1.71  tff(c_902, plain, (![B_1078]: (r1_xboole_0(k1_xboole_0, B_1078))), inference(splitLeft, [status(thm)], [c_874])).
% 3.88/1.71  tff(c_16, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, B_10) | ~r2_hidden(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.88/1.71  tff(c_906, plain, (![C_1079, B_1080]: (~r2_hidden(C_1079, B_1080) | ~r2_hidden(C_1079, k1_xboole_0))), inference(resolution, [status(thm)], [c_902, c_16])).
% 3.88/1.71  tff(c_954, plain, (![C_1083]: (~r2_hidden(C_1083, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_906])).
% 3.88/1.71  tff(c_989, plain, (![B_7]: (r2_hidden('#skF_2'(k1_xboole_0, B_7), B_7) | k1_xboole_0=B_7)), inference(resolution, [status(thm)], [c_14, c_954])).
% 3.88/1.71  tff(c_50, plain, (![A_28, B_32]: (k1_relat_1('#skF_8'(A_28, B_32))=A_28 | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.88/1.71  tff(c_52, plain, (![A_28, B_32]: (v1_funct_1('#skF_8'(A_28, B_32)) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.88/1.71  tff(c_54, plain, (![A_28, B_32]: (v1_relat_1('#skF_8'(A_28, B_32)) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.88/1.71  tff(c_135, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.71  tff(c_205, plain, (![A_85, B_86]: ('#skF_1'(k1_tarski(A_85), B_86)=A_85 | r1_tarski(k1_tarski(A_85), B_86))), inference(resolution, [status(thm)], [c_135, c_24])).
% 3.88/1.71  tff(c_163, plain, (![A_69, B_70]: (k2_relat_1('#skF_8'(A_69, B_70))=k1_tarski(B_70) | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.88/1.71  tff(c_56, plain, (![C_35]: (~r1_tarski(k2_relat_1(C_35), '#skF_9') | k1_relat_1(C_35)!='#skF_10' | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.88/1.71  tff(c_169, plain, (![B_70, A_69]: (~r1_tarski(k1_tarski(B_70), '#skF_9') | k1_relat_1('#skF_8'(A_69, B_70))!='#skF_10' | ~v1_funct_1('#skF_8'(A_69, B_70)) | ~v1_relat_1('#skF_8'(A_69, B_70)) | k1_xboole_0=A_69)), inference(superposition, [status(thm), theory('equality')], [c_163, c_56])).
% 3.88/1.71  tff(c_298, plain, (![A_108, A_109]: (k1_relat_1('#skF_8'(A_108, A_109))!='#skF_10' | ~v1_funct_1('#skF_8'(A_108, A_109)) | ~v1_relat_1('#skF_8'(A_108, A_109)) | k1_xboole_0=A_108 | '#skF_1'(k1_tarski(A_109), '#skF_9')=A_109)), inference(resolution, [status(thm)], [c_205, c_169])).
% 3.88/1.71  tff(c_1063, plain, (![A_1096, B_1097]: (k1_relat_1('#skF_8'(A_1096, B_1097))!='#skF_10' | ~v1_funct_1('#skF_8'(A_1096, B_1097)) | '#skF_1'(k1_tarski(B_1097), '#skF_9')=B_1097 | k1_xboole_0=A_1096)), inference(resolution, [status(thm)], [c_54, c_298])).
% 3.88/1.71  tff(c_1308, plain, (![A_1113, B_1114]: (k1_relat_1('#skF_8'(A_1113, B_1114))!='#skF_10' | '#skF_1'(k1_tarski(B_1114), '#skF_9')=B_1114 | k1_xboole_0=A_1113)), inference(resolution, [status(thm)], [c_52, c_1063])).
% 3.88/1.71  tff(c_1311, plain, (![A_28, B_32]: (A_28!='#skF_10' | '#skF_1'(k1_tarski(B_32), '#skF_9')=B_32 | k1_xboole_0=A_28 | k1_xboole_0=A_28)), inference(superposition, [status(thm), theory('equality')], [c_50, c_1308])).
% 3.88/1.71  tff(c_1429, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_1311])).
% 3.88/1.71  tff(c_105, plain, (![A_59]: (k2_relat_1(A_59)=k1_xboole_0 | k1_relat_1(A_59)!=k1_xboole_0 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.88/1.71  tff(c_111, plain, (![A_21, B_22]: (k2_relat_1('#skF_7'(A_21, B_22))=k1_xboole_0 | k1_relat_1('#skF_7'(A_21, B_22))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_105])).
% 3.88/1.71  tff(c_116, plain, (![A_60, B_61]: (k2_relat_1('#skF_7'(A_60, B_61))=k1_xboole_0 | k1_xboole_0!=B_61)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_111])).
% 3.88/1.71  tff(c_122, plain, (![A_60, B_61]: (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1('#skF_7'(A_60, B_61))!='#skF_10' | ~v1_funct_1('#skF_7'(A_60, B_61)) | ~v1_relat_1('#skF_7'(A_60, B_61)) | k1_xboole_0!=B_61)), inference(superposition, [status(thm), theory('equality')], [c_116, c_56])).
% 3.88/1.71  tff(c_128, plain, (![B_61]: (B_61!='#skF_10' | k1_xboole_0!=B_61)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_22, c_122])).
% 3.88/1.71  tff(c_133, plain, (k1_xboole_0!='#skF_10'), inference(reflexivity, [status(thm), theory('equality')], [c_128])).
% 3.88/1.71  tff(c_1462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1429, c_133])).
% 3.88/1.71  tff(c_1465, plain, (![B_1128]: ('#skF_1'(k1_tarski(B_1128), '#skF_9')=B_1128)), inference(splitRight, [status(thm)], [c_1311])).
% 3.88/1.71  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.71  tff(c_1493, plain, (![B_1129]: (~r2_hidden(B_1129, '#skF_9') | r1_tarski(k1_tarski(B_1129), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1465, c_4])).
% 3.88/1.71  tff(c_1513, plain, (![A_1132, B_1133]: (k1_relat_1('#skF_8'(A_1132, B_1133))!='#skF_10' | ~v1_funct_1('#skF_8'(A_1132, B_1133)) | ~v1_relat_1('#skF_8'(A_1132, B_1133)) | k1_xboole_0=A_1132 | ~r2_hidden(B_1133, '#skF_9'))), inference(resolution, [status(thm)], [c_1493, c_169])).
% 3.88/1.71  tff(c_1570, plain, (![A_1137, B_1138]: (k1_relat_1('#skF_8'(A_1137, B_1138))!='#skF_10' | ~v1_funct_1('#skF_8'(A_1137, B_1138)) | ~r2_hidden(B_1138, '#skF_9') | k1_xboole_0=A_1137)), inference(resolution, [status(thm)], [c_54, c_1513])).
% 3.88/1.71  tff(c_1607, plain, (![A_1141, B_1142]: (k1_relat_1('#skF_8'(A_1141, B_1142))!='#skF_10' | ~r2_hidden(B_1142, '#skF_9') | k1_xboole_0=A_1141)), inference(resolution, [status(thm)], [c_52, c_1570])).
% 3.88/1.71  tff(c_1610, plain, (![A_28, B_32]: (A_28!='#skF_10' | ~r2_hidden(B_32, '#skF_9') | k1_xboole_0=A_28 | k1_xboole_0=A_28)), inference(superposition, [status(thm), theory('equality')], [c_50, c_1607])).
% 3.88/1.71  tff(c_1612, plain, (![B_1143]: (~r2_hidden(B_1143, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1610])).
% 3.88/1.71  tff(c_1628, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_989, c_1612])).
% 3.88/1.71  tff(c_1669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1628])).
% 3.88/1.71  tff(c_1671, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_1610])).
% 3.88/1.71  tff(c_1706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1671, c_133])).
% 3.88/1.71  tff(c_1708, plain, (![XT_1144, B_1145]: (r2_hidden(k1_tarski(XT_1144), B_1145))), inference(splitRight, [status(thm)], [c_874])).
% 3.88/1.71  tff(c_1738, plain, (![XT_1168]: (k1_tarski(XT_1168)='#skF_10')), inference(resolution, [status(thm)], [c_1708, c_24])).
% 3.88/1.71  tff(c_1719, plain, (![XT_1144, A_15]: (k1_tarski(XT_1144)=A_15)), inference(resolution, [status(thm)], [c_1708, c_24])).
% 3.88/1.71  tff(c_2187, plain, (![A_2030]: (A_2030='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1738, c_1719])).
% 3.88/1.71  tff(c_2273, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2187, c_133])).
% 3.88/1.71  tff(c_2275, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 3.88/1.71  tff(c_2274, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_58])).
% 3.88/1.71  tff(c_2281, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2275, c_2274])).
% 3.88/1.71  tff(c_2276, plain, (![A_14]: (r1_tarski('#skF_10', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_22])).
% 3.88/1.71  tff(c_2292, plain, (![A_14]: (r1_tarski('#skF_9', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_2276])).
% 3.88/1.71  tff(c_38, plain, (![A_20]: (k2_relat_1(A_20)=k1_xboole_0 | k1_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.88/1.71  tff(c_2330, plain, (![A_2931]: (k2_relat_1(A_2931)='#skF_9' | k1_relat_1(A_2931)!='#skF_9' | ~v1_relat_1(A_2931))), inference(demodulation, [status(thm), theory('equality')], [c_2275, c_2275, c_38])).
% 3.88/1.71  tff(c_2336, plain, (![A_21, B_22]: (k2_relat_1('#skF_7'(A_21, B_22))='#skF_9' | k1_relat_1('#skF_7'(A_21, B_22))!='#skF_9')), inference(resolution, [status(thm)], [c_46, c_2330])).
% 3.88/1.71  tff(c_2341, plain, (![A_2932, B_2933]: (k2_relat_1('#skF_7'(A_2932, B_2933))='#skF_9' | B_2933!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2336])).
% 3.88/1.71  tff(c_2287, plain, (![C_35]: (~r1_tarski(k2_relat_1(C_35), '#skF_9') | k1_relat_1(C_35)!='#skF_9' | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_56])).
% 3.88/1.71  tff(c_2347, plain, (![A_2932, B_2933]: (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_7'(A_2932, B_2933))!='#skF_9' | ~v1_funct_1('#skF_7'(A_2932, B_2933)) | ~v1_relat_1('#skF_7'(A_2932, B_2933)) | B_2933!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2341, c_2287])).
% 3.88/1.71  tff(c_2353, plain, (![B_2933]: (B_2933!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_2292, c_2347])).
% 3.88/1.71  tff(c_2362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2353, c_2281])).
% 3.88/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.71  
% 3.88/1.71  Inference rules
% 3.88/1.71  ----------------------
% 3.88/1.71  #Ref     : 1
% 3.88/1.71  #Sup     : 505
% 3.88/1.71  #Fact    : 0
% 3.88/1.71  #Define  : 0
% 3.88/1.71  #Split   : 4
% 3.88/1.71  #Chain   : 0
% 3.88/1.71  #Close   : 0
% 3.88/1.71  
% 3.88/1.71  Ordering : KBO
% 3.88/1.71  
% 3.88/1.71  Simplification rules
% 3.88/1.71  ----------------------
% 3.88/1.71  #Subsume      : 73
% 3.88/1.71  #Demod        : 244
% 3.88/1.71  #Tautology    : 143
% 3.88/1.71  #SimpNegUnit  : 18
% 3.88/1.71  #BackRed      : 79
% 3.88/1.71  
% 3.88/1.71  #Partial instantiations: 1382
% 3.88/1.71  #Strategies tried      : 1
% 3.88/1.71  
% 3.88/1.71  Timing (in seconds)
% 3.88/1.71  ----------------------
% 3.88/1.71  Preprocessing        : 0.33
% 3.88/1.71  Parsing              : 0.18
% 3.88/1.71  CNF conversion       : 0.03
% 3.88/1.71  Main loop            : 0.56
% 3.88/1.71  Inferencing          : 0.23
% 3.88/1.71  Reduction            : 0.15
% 3.88/1.71  Demodulation         : 0.10
% 3.88/1.71  BG Simplification    : 0.03
% 3.88/1.71  Subsumption          : 0.09
% 3.88/1.71  Abstraction          : 0.03
% 3.88/1.71  MUC search           : 0.00
% 3.88/1.71  Cooper               : 0.00
% 3.88/1.71  Total                : 0.93
% 3.88/1.72  Index Insertion      : 0.00
% 3.88/1.72  Index Deletion       : 0.00
% 3.88/1.72  Index Matching       : 0.00
% 3.88/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
