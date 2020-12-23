%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:18 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 407 expanded)
%              Number of leaves         :   25 ( 142 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 892 expanded)
%              Number of equality atoms :   38 ( 314 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_47,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_223,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r2_hidden('#skF_3'(A_67,B_68),A_67)
      | B_68 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [C_23,B_24] : ~ r2_hidden(C_23,k4_xboole_0(B_24,k1_tarski(C_23))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_67,plain,(
    ! [C_23] : ~ r2_hidden(C_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_64])).

tff(c_247,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_68),B_68)
      | k1_xboole_0 = B_68 ) ),
    inference(resolution,[status(thm)],[c_223,c_67])).

tff(c_318,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_hidden(k4_tarski(A_76,B_77),k2_zfmisc_1(C_78,D_79))
      | ~ r2_hidden(B_77,D_79)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_129,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r2_hidden(A_44,C_45)
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1(C_45,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_132,plain,(
    ! [A_44,B_46] :
      ( r2_hidden(A_44,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_129])).

tff(c_338,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,'#skF_6')
      | ~ r2_hidden(B_77,'#skF_5')
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_318,c_132])).

tff(c_344,plain,(
    ! [B_80] : ~ r2_hidden(B_80,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_352,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_247,c_344])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_352])).

tff(c_397,plain,(
    ! [A_83] :
      ( r2_hidden(A_83,'#skF_6')
      | ~ r2_hidden(A_83,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_415,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_84,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_397,c_4])).

tff(c_425,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_415])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_427,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_425,c_16])).

tff(c_430,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_427])).

tff(c_377,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(k4_tarski(A_81,B_82),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_82,'#skF_7')
      | ~ r2_hidden(A_81,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_318])).

tff(c_30,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_394,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(A_81,'#skF_4')
      | ~ r2_hidden(B_82,'#skF_7')
      | ~ r2_hidden(A_81,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_377,c_30])).

tff(c_446,plain,(
    ! [B_87] : ~ r2_hidden(B_87,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_474,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_247,c_446])).

tff(c_487,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_40])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_488,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_42])).

tff(c_444,plain,(
    ! [B_82] : ~ r2_hidden(B_82,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_125,plain,(
    ! [B_40,D_41,A_42,C_43] :
      ( r2_hidden(B_40,D_41)
      | ~ r2_hidden(k4_tarski(A_42,B_40),k2_zfmisc_1(C_43,D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [B_40,A_42] :
      ( r2_hidden(B_40,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_42,B_40),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_125])).

tff(c_339,plain,(
    ! [B_77,A_76] :
      ( r2_hidden(B_77,'#skF_7')
      | ~ r2_hidden(B_77,'#skF_5')
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_318,c_128])).

tff(c_509,plain,(
    ! [B_77,A_76] :
      ( ~ r2_hidden(B_77,'#skF_5')
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_339])).

tff(c_511,plain,(
    ! [A_91] : ~ r2_hidden(A_91,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_533,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_511])).

tff(c_74,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_1'(A_28,B_29),A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [B_29] : r1_tarski(k1_xboole_0,B_29) ),
    inference(resolution,[status(thm)],[c_74,c_67])).

tff(c_87,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [B_29] :
      ( k1_xboole_0 = B_29
      | ~ r1_tarski(B_29,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_85,c_87])).

tff(c_569,plain,(
    ! [B_94] :
      ( B_94 = '#skF_7'
      | ~ r1_tarski(B_94,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_474,c_92])).

tff(c_573,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_533,c_569])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_573])).

tff(c_611,plain,(
    ! [B_98] : ~ r2_hidden(B_98,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_638,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_611])).

tff(c_680,plain,(
    ! [B_101] :
      ( B_101 = '#skF_7'
      | ~ r1_tarski(B_101,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_474,c_92])).

tff(c_684,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_638,c_680])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_684])).

tff(c_698,plain,(
    ! [A_102] :
      ( r2_hidden(A_102,'#skF_4')
      | ~ r2_hidden(A_102,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_859,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_1'('#skF_6',B_111),'#skF_4')
      | r1_tarski('#skF_6',B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_698])).

tff(c_869,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_859,c_4])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_430,c_869])).

tff(c_877,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1058,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_2'(A_156,B_157),B_157)
      | r2_hidden('#skF_3'(A_156,B_157),A_156)
      | B_157 = A_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_904,plain,(
    ! [C_114,B_115] : ~ r2_hidden(C_114,k4_xboole_0(B_115,k1_tarski(C_114))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_907,plain,(
    ! [C_114] : ~ r2_hidden(C_114,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_904])).

tff(c_1082,plain,(
    ! [B_157] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_157),B_157)
      | k1_xboole_0 = B_157 ) ),
    inference(resolution,[status(thm)],[c_1058,c_907])).

tff(c_1153,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( r2_hidden(k4_tarski(A_165,B_166),k2_zfmisc_1(C_167,D_168))
      | ~ r2_hidden(B_166,D_168)
      | ~ r2_hidden(A_165,C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_878,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_899,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_44])).

tff(c_965,plain,(
    ! [B_135,D_136,A_137,C_138] :
      ( r2_hidden(B_135,D_136)
      | ~ r2_hidden(k4_tarski(A_137,B_135),k2_zfmisc_1(C_138,D_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_968,plain,(
    ! [B_135,A_137] :
      ( r2_hidden(B_135,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_137,B_135),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_965])).

tff(c_1169,plain,(
    ! [B_166,A_165] :
      ( r2_hidden(B_166,'#skF_7')
      | ~ r2_hidden(B_166,'#skF_5')
      | ~ r2_hidden(A_165,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1153,c_968])).

tff(c_1190,plain,(
    ! [A_171] : ~ r2_hidden(A_171,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1169])).

tff(c_1198,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1082,c_1190])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1198])).

tff(c_1223,plain,(
    ! [B_172] :
      ( r2_hidden(B_172,'#skF_7')
      | ~ r2_hidden(B_172,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1169])).

tff(c_1241,plain,(
    ! [A_173] :
      ( r1_tarski(A_173,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_173,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1223,c_4])).

tff(c_1251,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_1241])).

tff(c_1269,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1251,c_16])).

tff(c_1272,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_877,c_1269])).

tff(c_1252,plain,(
    ! [A_174,B_175] :
      ( r2_hidden(k4_tarski(A_174,B_175),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_175,'#skF_7')
      | ~ r2_hidden(A_174,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_1153])).

tff(c_28,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1265,plain,(
    ! [B_175,A_174] :
      ( r2_hidden(B_175,'#skF_5')
      | ~ r2_hidden(B_175,'#skF_7')
      | ~ r2_hidden(A_174,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1252,c_28])).

tff(c_1301,plain,(
    ! [A_182] : ~ r2_hidden(A_182,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1265])).

tff(c_1309,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1082,c_1301])).

tff(c_1332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1309])).

tff(c_1334,plain,(
    ! [B_183] :
      ( r2_hidden(B_183,'#skF_5')
      | ~ r2_hidden(B_183,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1265])).

tff(c_1451,plain,(
    ! [B_191] :
      ( r2_hidden('#skF_1'('#skF_7',B_191),'#skF_5')
      | r1_tarski('#skF_7',B_191) ) ),
    inference(resolution,[status(thm)],[c_6,c_1334])).

tff(c_1461,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1451,c_4])).

tff(c_1468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1272,c_1272,c_1461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.50  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.19/1.50  
% 3.19/1.50  %Foreground sorts:
% 3.19/1.50  
% 3.19/1.50  
% 3.19/1.50  %Background operators:
% 3.19/1.50  
% 3.19/1.50  
% 3.19/1.50  %Foreground operators:
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.19/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.50  
% 3.19/1.52  tff(f_73, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.19/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.19/1.52  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.19/1.52  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.19/1.52  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.19/1.52  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.19/1.52  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.52  tff(c_38, plain, ('#skF_7'!='#skF_5' | '#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.19/1.52  tff(c_47, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 3.19/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.52  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.19/1.52  tff(c_223, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67, B_68), B_68) | r2_hidden('#skF_3'(A_67, B_68), A_67) | B_68=A_67)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.52  tff(c_22, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.52  tff(c_64, plain, (![C_23, B_24]: (~r2_hidden(C_23, k4_xboole_0(B_24, k1_tarski(C_23))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.52  tff(c_67, plain, (![C_23]: (~r2_hidden(C_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_64])).
% 3.19/1.52  tff(c_247, plain, (![B_68]: (r2_hidden('#skF_2'(k1_xboole_0, B_68), B_68) | k1_xboole_0=B_68)), inference(resolution, [status(thm)], [c_223, c_67])).
% 3.19/1.52  tff(c_318, plain, (![A_76, B_77, C_78, D_79]: (r2_hidden(k4_tarski(A_76, B_77), k2_zfmisc_1(C_78, D_79)) | ~r2_hidden(B_77, D_79) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_44, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.19/1.52  tff(c_129, plain, (![A_44, C_45, B_46, D_47]: (r2_hidden(A_44, C_45) | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1(C_45, D_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_132, plain, (![A_44, B_46]: (r2_hidden(A_44, '#skF_6') | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_129])).
% 3.19/1.52  tff(c_338, plain, (![A_76, B_77]: (r2_hidden(A_76, '#skF_6') | ~r2_hidden(B_77, '#skF_5') | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_318, c_132])).
% 3.19/1.52  tff(c_344, plain, (![B_80]: (~r2_hidden(B_80, '#skF_5'))), inference(splitLeft, [status(thm)], [c_338])).
% 3.19/1.52  tff(c_352, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_247, c_344])).
% 3.19/1.52  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_352])).
% 3.19/1.52  tff(c_397, plain, (![A_83]: (r2_hidden(A_83, '#skF_6') | ~r2_hidden(A_83, '#skF_4'))), inference(splitRight, [status(thm)], [c_338])).
% 3.19/1.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.52  tff(c_415, plain, (![A_84]: (r1_tarski(A_84, '#skF_6') | ~r2_hidden('#skF_1'(A_84, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_397, c_4])).
% 3.19/1.52  tff(c_425, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_415])).
% 3.19/1.52  tff(c_16, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.52  tff(c_427, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_425, c_16])).
% 3.19/1.52  tff(c_430, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_47, c_427])).
% 3.19/1.52  tff(c_377, plain, (![A_81, B_82]: (r2_hidden(k4_tarski(A_81, B_82), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_82, '#skF_7') | ~r2_hidden(A_81, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_318])).
% 3.19/1.52  tff(c_30, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_394, plain, (![A_81, B_82]: (r2_hidden(A_81, '#skF_4') | ~r2_hidden(B_82, '#skF_7') | ~r2_hidden(A_81, '#skF_6'))), inference(resolution, [status(thm)], [c_377, c_30])).
% 3.19/1.52  tff(c_446, plain, (![B_87]: (~r2_hidden(B_87, '#skF_7'))), inference(splitLeft, [status(thm)], [c_394])).
% 3.19/1.52  tff(c_474, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_247, c_446])).
% 3.19/1.52  tff(c_487, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_474, c_40])).
% 3.19/1.52  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.19/1.52  tff(c_488, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_474, c_42])).
% 3.19/1.52  tff(c_444, plain, (![B_82]: (~r2_hidden(B_82, '#skF_7'))), inference(splitLeft, [status(thm)], [c_394])).
% 3.19/1.52  tff(c_125, plain, (![B_40, D_41, A_42, C_43]: (r2_hidden(B_40, D_41) | ~r2_hidden(k4_tarski(A_42, B_40), k2_zfmisc_1(C_43, D_41)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_128, plain, (![B_40, A_42]: (r2_hidden(B_40, '#skF_7') | ~r2_hidden(k4_tarski(A_42, B_40), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_125])).
% 3.19/1.52  tff(c_339, plain, (![B_77, A_76]: (r2_hidden(B_77, '#skF_7') | ~r2_hidden(B_77, '#skF_5') | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_318, c_128])).
% 3.19/1.52  tff(c_509, plain, (![B_77, A_76]: (~r2_hidden(B_77, '#skF_5') | ~r2_hidden(A_76, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_444, c_339])).
% 3.19/1.52  tff(c_511, plain, (![A_91]: (~r2_hidden(A_91, '#skF_4'))), inference(splitLeft, [status(thm)], [c_509])).
% 3.19/1.52  tff(c_533, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_511])).
% 3.19/1.52  tff(c_74, plain, (![A_28, B_29]: (r2_hidden('#skF_1'(A_28, B_29), A_28) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.52  tff(c_85, plain, (![B_29]: (r1_tarski(k1_xboole_0, B_29))), inference(resolution, [status(thm)], [c_74, c_67])).
% 3.19/1.52  tff(c_87, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.52  tff(c_92, plain, (![B_29]: (k1_xboole_0=B_29 | ~r1_tarski(B_29, k1_xboole_0))), inference(resolution, [status(thm)], [c_85, c_87])).
% 3.19/1.52  tff(c_569, plain, (![B_94]: (B_94='#skF_7' | ~r1_tarski(B_94, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_474, c_92])).
% 3.19/1.52  tff(c_573, plain, ('#skF_7'='#skF_4'), inference(resolution, [status(thm)], [c_533, c_569])).
% 3.19/1.52  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_573])).
% 3.19/1.52  tff(c_611, plain, (![B_98]: (~r2_hidden(B_98, '#skF_5'))), inference(splitRight, [status(thm)], [c_509])).
% 3.19/1.52  tff(c_638, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_611])).
% 3.19/1.52  tff(c_680, plain, (![B_101]: (B_101='#skF_7' | ~r1_tarski(B_101, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_474, c_92])).
% 3.19/1.52  tff(c_684, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_638, c_680])).
% 3.19/1.52  tff(c_696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_684])).
% 3.19/1.52  tff(c_698, plain, (![A_102]: (r2_hidden(A_102, '#skF_4') | ~r2_hidden(A_102, '#skF_6'))), inference(splitRight, [status(thm)], [c_394])).
% 3.19/1.52  tff(c_859, plain, (![B_111]: (r2_hidden('#skF_1'('#skF_6', B_111), '#skF_4') | r1_tarski('#skF_6', B_111))), inference(resolution, [status(thm)], [c_6, c_698])).
% 3.19/1.52  tff(c_869, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_859, c_4])).
% 3.19/1.52  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_430, c_869])).
% 3.19/1.52  tff(c_877, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 3.19/1.52  tff(c_1058, plain, (![A_156, B_157]: (r2_hidden('#skF_2'(A_156, B_157), B_157) | r2_hidden('#skF_3'(A_156, B_157), A_156) | B_157=A_156)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.52  tff(c_904, plain, (![C_114, B_115]: (~r2_hidden(C_114, k4_xboole_0(B_115, k1_tarski(C_114))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.52  tff(c_907, plain, (![C_114]: (~r2_hidden(C_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_904])).
% 3.19/1.52  tff(c_1082, plain, (![B_157]: (r2_hidden('#skF_2'(k1_xboole_0, B_157), B_157) | k1_xboole_0=B_157)), inference(resolution, [status(thm)], [c_1058, c_907])).
% 3.19/1.52  tff(c_1153, plain, (![A_165, B_166, C_167, D_168]: (r2_hidden(k4_tarski(A_165, B_166), k2_zfmisc_1(C_167, D_168)) | ~r2_hidden(B_166, D_168) | ~r2_hidden(A_165, C_167))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_878, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 3.19/1.52  tff(c_899, plain, (k2_zfmisc_1('#skF_4', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_878, c_44])).
% 3.19/1.52  tff(c_965, plain, (![B_135, D_136, A_137, C_138]: (r2_hidden(B_135, D_136) | ~r2_hidden(k4_tarski(A_137, B_135), k2_zfmisc_1(C_138, D_136)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_968, plain, (![B_135, A_137]: (r2_hidden(B_135, '#skF_7') | ~r2_hidden(k4_tarski(A_137, B_135), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_899, c_965])).
% 3.19/1.52  tff(c_1169, plain, (![B_166, A_165]: (r2_hidden(B_166, '#skF_7') | ~r2_hidden(B_166, '#skF_5') | ~r2_hidden(A_165, '#skF_4'))), inference(resolution, [status(thm)], [c_1153, c_968])).
% 3.19/1.52  tff(c_1190, plain, (![A_171]: (~r2_hidden(A_171, '#skF_4'))), inference(splitLeft, [status(thm)], [c_1169])).
% 3.19/1.52  tff(c_1198, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1082, c_1190])).
% 3.19/1.52  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1198])).
% 3.19/1.52  tff(c_1223, plain, (![B_172]: (r2_hidden(B_172, '#skF_7') | ~r2_hidden(B_172, '#skF_5'))), inference(splitRight, [status(thm)], [c_1169])).
% 3.19/1.52  tff(c_1241, plain, (![A_173]: (r1_tarski(A_173, '#skF_7') | ~r2_hidden('#skF_1'(A_173, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_1223, c_4])).
% 3.19/1.52  tff(c_1251, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_1241])).
% 3.19/1.52  tff(c_1269, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1251, c_16])).
% 3.19/1.52  tff(c_1272, plain, (~r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_877, c_1269])).
% 3.19/1.52  tff(c_1252, plain, (![A_174, B_175]: (r2_hidden(k4_tarski(A_174, B_175), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_175, '#skF_7') | ~r2_hidden(A_174, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_899, c_1153])).
% 3.19/1.52  tff(c_28, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_1265, plain, (![B_175, A_174]: (r2_hidden(B_175, '#skF_5') | ~r2_hidden(B_175, '#skF_7') | ~r2_hidden(A_174, '#skF_4'))), inference(resolution, [status(thm)], [c_1252, c_28])).
% 3.19/1.52  tff(c_1301, plain, (![A_182]: (~r2_hidden(A_182, '#skF_4'))), inference(splitLeft, [status(thm)], [c_1265])).
% 3.19/1.52  tff(c_1309, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1082, c_1301])).
% 3.19/1.52  tff(c_1332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1309])).
% 3.19/1.52  tff(c_1334, plain, (![B_183]: (r2_hidden(B_183, '#skF_5') | ~r2_hidden(B_183, '#skF_7'))), inference(splitRight, [status(thm)], [c_1265])).
% 3.19/1.52  tff(c_1451, plain, (![B_191]: (r2_hidden('#skF_1'('#skF_7', B_191), '#skF_5') | r1_tarski('#skF_7', B_191))), inference(resolution, [status(thm)], [c_6, c_1334])).
% 3.19/1.52  tff(c_1461, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1451, c_4])).
% 3.19/1.52  tff(c_1468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1272, c_1272, c_1461])).
% 3.19/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.52  
% 3.19/1.52  Inference rules
% 3.19/1.52  ----------------------
% 3.19/1.52  #Ref     : 0
% 3.19/1.52  #Sup     : 280
% 3.19/1.52  #Fact    : 0
% 3.19/1.52  #Define  : 0
% 3.19/1.52  #Split   : 8
% 3.19/1.52  #Chain   : 0
% 3.19/1.52  #Close   : 0
% 3.19/1.52  
% 3.19/1.52  Ordering : KBO
% 3.19/1.52  
% 3.19/1.52  Simplification rules
% 3.19/1.52  ----------------------
% 3.19/1.52  #Subsume      : 51
% 3.19/1.52  #Demod        : 76
% 3.19/1.52  #Tautology    : 77
% 3.19/1.52  #SimpNegUnit  : 23
% 3.19/1.52  #BackRed      : 37
% 3.19/1.52  
% 3.19/1.52  #Partial instantiations: 0
% 3.19/1.52  #Strategies tried      : 1
% 3.19/1.52  
% 3.19/1.52  Timing (in seconds)
% 3.19/1.52  ----------------------
% 3.19/1.52  Preprocessing        : 0.31
% 3.19/1.52  Parsing              : 0.16
% 3.19/1.52  CNF conversion       : 0.02
% 3.19/1.52  Main loop            : 0.44
% 3.19/1.52  Inferencing          : 0.17
% 3.19/1.52  Reduction            : 0.12
% 3.19/1.52  Demodulation         : 0.08
% 3.19/1.52  BG Simplification    : 0.02
% 3.19/1.52  Subsumption          : 0.09
% 3.19/1.52  Abstraction          : 0.02
% 3.19/1.52  MUC search           : 0.00
% 3.19/1.52  Cooper               : 0.00
% 3.19/1.52  Total                : 0.79
% 3.19/1.52  Index Insertion      : 0.00
% 3.19/1.52  Index Deletion       : 0.00
% 3.19/1.52  Index Matching       : 0.00
% 3.19/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
