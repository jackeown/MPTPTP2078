%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:19 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 439 expanded)
%              Number of leaves         :   22 ( 149 expanded)
%              Depth                    :   13
%              Number of atoms          :  182 (1028 expanded)
%              Number of equality atoms :   37 ( 311 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_26,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r2_hidden(k4_tarski(A_62,B_63),k2_zfmisc_1(C_64,D_65))
      | ~ r2_hidden(B_63,D_65)
      | ~ r2_hidden(A_62,C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_77,plain,(
    ! [A_35,C_36,B_37,D_38] :
      ( r2_hidden(A_35,C_36)
      | ~ r2_hidden(k4_tarski(A_35,B_37),k2_zfmisc_1(C_36,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_35,B_37] :
      ( r2_hidden(A_35,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_35,B_37),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_77])).

tff(c_146,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,'#skF_6')
      | ~ r2_hidden(B_63,'#skF_5')
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125,c_80])).

tff(c_1470,plain,(
    ! [B_185] : ~ r2_hidden(B_185,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_1494,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_18,c_1470])).

tff(c_1503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1494])).

tff(c_1508,plain,(
    ! [A_186] :
      ( r2_hidden(A_186,'#skF_6')
      | ~ r2_hidden(A_186,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1543,plain,(
    ! [A_193] :
      ( r1_tarski(A_193,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_193,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1508,c_4])).

tff(c_1553,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_1543])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_52,B_53,B_54] :
      ( r2_hidden('#skF_2'(A_52,B_53),B_54)
      | ~ r1_tarski(B_53,B_54)
      | ~ r2_xboole_0(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109,plain,(
    ! [B_55,B_56] :
      ( ~ r1_tarski(B_55,B_56)
      | ~ r2_xboole_0(B_56,B_55) ) ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_113,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_1557,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1553,c_113])).

tff(c_1561,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1557])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_85,plain,(
    ! [B_41,D_42,A_43,C_44] :
      ( r2_hidden(B_41,D_42)
      | ~ r2_hidden(k4_tarski(A_43,B_41),k2_zfmisc_1(C_44,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,(
    ! [B_41,A_43] :
      ( r2_hidden(B_41,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_43,B_41),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_85])).

tff(c_145,plain,(
    ! [B_63,A_62] :
      ( r2_hidden(B_63,'#skF_7')
      | ~ r2_hidden(B_63,'#skF_5')
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125,c_88])).

tff(c_151,plain,(
    ! [A_66] : ~ r2_hidden(A_66,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_175,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_175])).

tff(c_186,plain,(
    ! [B_67] :
      ( r2_hidden(B_67,'#skF_7')
      | ~ r2_hidden(B_67,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_220,plain,(
    ! [B_70] :
      ( ~ r2_xboole_0('#skF_7',B_70)
      | ~ r2_hidden('#skF_2'('#skF_7',B_70),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_186,c_14])).

tff(c_230,plain,(
    ~ r2_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_220])).

tff(c_234,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_230])).

tff(c_235,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_200,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(k4_tarski(A_68,B_69),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_69,'#skF_7')
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_22,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,(
    ! [B_69,A_68] :
      ( r2_hidden(B_69,'#skF_5')
      | ~ r2_hidden(B_69,'#skF_7')
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_200,c_22])).

tff(c_312,plain,(
    ! [A_83] : ~ r2_hidden(A_83,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18,c_312])).

tff(c_346,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_28])).

tff(c_310,plain,(
    ! [A_68] : ~ r2_hidden(A_68,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_372,plain,(
    ! [B_63,A_62] :
      ( ~ r2_hidden(B_63,'#skF_5')
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_310,c_146])).

tff(c_374,plain,(
    ! [A_88] : ~ r2_hidden(A_88,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_393,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_374])).

tff(c_76,plain,(
    ! [A_11,B_33] :
      ( r2_hidden('#skF_3'(A_11),B_33)
      | ~ r1_tarski(A_11,B_33)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_339,plain,(
    ! [A_11] :
      ( ~ r1_tarski(A_11,'#skF_6')
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_76,c_312])).

tff(c_410,plain,(
    ! [A_91] :
      ( ~ r1_tarski(A_91,'#skF_6')
      | A_91 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_339])).

tff(c_414,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_393,c_410])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_414])).

tff(c_428,plain,(
    ! [B_92] : ~ r2_hidden(B_92,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_447,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_428])).

tff(c_465,plain,(
    ! [A_95] :
      ( ~ r1_tarski(A_95,'#skF_6')
      | A_95 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_339])).

tff(c_469,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_447,c_465])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_469])).

tff(c_538,plain,(
    ! [B_98] :
      ( r2_hidden(B_98,'#skF_5')
      | ~ r2_hidden(B_98,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_1123,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_1'('#skF_7',B_146),'#skF_5')
      | r1_tarski('#skF_7',B_146) ) ),
    inference(resolution,[status(thm)],[c_6,c_538])).

tff(c_1133,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1123,c_4])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_235,c_1133])).

tff(c_1141,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_24,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_218,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(A_68,'#skF_4')
      | ~ r2_hidden(B_69,'#skF_7')
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_200,c_24])).

tff(c_1170,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(A_68,'#skF_4')
      | ~ r2_hidden(B_69,'#skF_5')
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_218])).

tff(c_1179,plain,(
    ! [B_152] : ~ r2_hidden(B_152,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1170])).

tff(c_1203,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_18,c_1179])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1203])).

tff(c_1214,plain,(
    ! [A_153] :
      ( r2_hidden(A_153,'#skF_4')
      | ~ r2_hidden(A_153,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_1614,plain,(
    ! [B_202] :
      ( r2_hidden('#skF_1'('#skF_6',B_202),'#skF_4')
      | r1_tarski('#skF_6',B_202) ) ),
    inference(resolution,[status(thm)],[c_6,c_1214])).

tff(c_1624,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1614,c_4])).

tff(c_1631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1561,c_1561,c_1624])).

tff(c_1632,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1700,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( r2_hidden(k4_tarski(A_232,B_233),k2_zfmisc_1(C_234,D_235))
      | ~ r2_hidden(B_233,D_235)
      | ~ r2_hidden(A_232,C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1633,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1638,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_32])).

tff(c_1695,plain,(
    ! [B_226,D_227,A_228,C_229] :
      ( r2_hidden(B_226,D_227)
      | ~ r2_hidden(k4_tarski(A_228,B_226),k2_zfmisc_1(C_229,D_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1698,plain,(
    ! [B_226,A_228] :
      ( r2_hidden(B_226,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_228,B_226),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_1695])).

tff(c_1716,plain,(
    ! [B_233,A_232] :
      ( r2_hidden(B_233,'#skF_7')
      | ~ r2_hidden(B_233,'#skF_5')
      | ~ r2_hidden(A_232,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1700,c_1698])).

tff(c_1721,plain,(
    ! [A_236] : ~ r2_hidden(A_236,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1716])).

tff(c_1737,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_1721])).

tff(c_1744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1737])).

tff(c_1746,plain,(
    ! [B_237] :
      ( r2_hidden(B_237,'#skF_7')
      | ~ r2_hidden(B_237,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1716])).

tff(c_1788,plain,(
    ! [A_241] :
      ( r1_tarski(A_241,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_241,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1746,c_4])).

tff(c_1793,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_1788])).

tff(c_1760,plain,(
    ! [A_238,B_239] :
      ( r2_hidden(k4_tarski(A_238,B_239),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_239,'#skF_7')
      | ~ r2_hidden(A_238,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_1700])).

tff(c_1773,plain,(
    ! [B_239,A_238] :
      ( r2_hidden(B_239,'#skF_5')
      | ~ r2_hidden(B_239,'#skF_7')
      | ~ r2_hidden(A_238,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1760,c_22])).

tff(c_1831,plain,(
    ! [A_250] : ~ r2_hidden(A_250,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1773])).

tff(c_1851,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_1831])).

tff(c_1859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1851])).

tff(c_1861,plain,(
    ! [B_251] :
      ( r2_hidden(B_251,'#skF_5')
      | ~ r2_hidden(B_251,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1773])).

tff(c_1933,plain,(
    ! [A_257] :
      ( r2_hidden('#skF_2'(A_257,'#skF_7'),'#skF_5')
      | ~ r2_xboole_0(A_257,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16,c_1861])).

tff(c_1946,plain,(
    ~ r2_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_1933,c_14])).

tff(c_1975,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_1946])).

tff(c_1978,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1793,c_1975])).

tff(c_1980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1632,c_1978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:12:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.59  
% 3.52/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.59  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.52/1.59  
% 3.52/1.59  %Foreground sorts:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Background operators:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Foreground operators:
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.52/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.52/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.59  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.59  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.52/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.59  
% 3.52/1.61  tff(f_74, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.52/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.52/1.61  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.52/1.61  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.52/1.61  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.52/1.61  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.52/1.61  tff(c_26, plain, ('#skF_7'!='#skF_5' | '#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.61  tff(c_34, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 3.52/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.61  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.61  tff(c_18, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.61  tff(c_125, plain, (![A_62, B_63, C_64, D_65]: (r2_hidden(k4_tarski(A_62, B_63), k2_zfmisc_1(C_64, D_65)) | ~r2_hidden(B_63, D_65) | ~r2_hidden(A_62, C_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.61  tff(c_32, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.61  tff(c_77, plain, (![A_35, C_36, B_37, D_38]: (r2_hidden(A_35, C_36) | ~r2_hidden(k4_tarski(A_35, B_37), k2_zfmisc_1(C_36, D_38)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.61  tff(c_80, plain, (![A_35, B_37]: (r2_hidden(A_35, '#skF_6') | ~r2_hidden(k4_tarski(A_35, B_37), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_77])).
% 3.52/1.61  tff(c_146, plain, (![A_62, B_63]: (r2_hidden(A_62, '#skF_6') | ~r2_hidden(B_63, '#skF_5') | ~r2_hidden(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_125, c_80])).
% 3.52/1.61  tff(c_1470, plain, (![B_185]: (~r2_hidden(B_185, '#skF_5'))), inference(splitLeft, [status(thm)], [c_146])).
% 3.52/1.61  tff(c_1494, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_18, c_1470])).
% 3.52/1.61  tff(c_1503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1494])).
% 3.52/1.61  tff(c_1508, plain, (![A_186]: (r2_hidden(A_186, '#skF_6') | ~r2_hidden(A_186, '#skF_4'))), inference(splitRight, [status(thm)], [c_146])).
% 3.52/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.61  tff(c_1543, plain, (![A_193]: (r1_tarski(A_193, '#skF_6') | ~r2_hidden('#skF_1'(A_193, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_1508, c_4])).
% 3.52/1.61  tff(c_1553, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_1543])).
% 3.52/1.61  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.61  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.61  tff(c_67, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.61  tff(c_100, plain, (![A_52, B_53, B_54]: (r2_hidden('#skF_2'(A_52, B_53), B_54) | ~r1_tarski(B_53, B_54) | ~r2_xboole_0(A_52, B_53))), inference(resolution, [status(thm)], [c_16, c_67])).
% 3.52/1.61  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.61  tff(c_109, plain, (![B_55, B_56]: (~r1_tarski(B_55, B_56) | ~r2_xboole_0(B_56, B_55))), inference(resolution, [status(thm)], [c_100, c_14])).
% 3.52/1.61  tff(c_113, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_109])).
% 3.52/1.61  tff(c_1557, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1553, c_113])).
% 3.52/1.61  tff(c_1561, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_1557])).
% 3.52/1.61  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.61  tff(c_85, plain, (![B_41, D_42, A_43, C_44]: (r2_hidden(B_41, D_42) | ~r2_hidden(k4_tarski(A_43, B_41), k2_zfmisc_1(C_44, D_42)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.61  tff(c_88, plain, (![B_41, A_43]: (r2_hidden(B_41, '#skF_7') | ~r2_hidden(k4_tarski(A_43, B_41), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_85])).
% 3.52/1.61  tff(c_145, plain, (![B_63, A_62]: (r2_hidden(B_63, '#skF_7') | ~r2_hidden(B_63, '#skF_5') | ~r2_hidden(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_125, c_88])).
% 3.52/1.61  tff(c_151, plain, (![A_66]: (~r2_hidden(A_66, '#skF_4'))), inference(splitLeft, [status(thm)], [c_145])).
% 3.52/1.61  tff(c_175, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_151])).
% 3.52/1.61  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_175])).
% 3.52/1.61  tff(c_186, plain, (![B_67]: (r2_hidden(B_67, '#skF_7') | ~r2_hidden(B_67, '#skF_5'))), inference(splitRight, [status(thm)], [c_145])).
% 3.52/1.61  tff(c_220, plain, (![B_70]: (~r2_xboole_0('#skF_7', B_70) | ~r2_hidden('#skF_2'('#skF_7', B_70), '#skF_5'))), inference(resolution, [status(thm)], [c_186, c_14])).
% 3.52/1.61  tff(c_230, plain, (~r2_xboole_0('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_220])).
% 3.52/1.61  tff(c_234, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_230])).
% 3.52/1.61  tff(c_235, plain, (~r1_tarski('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_234])).
% 3.52/1.61  tff(c_200, plain, (![A_68, B_69]: (r2_hidden(k4_tarski(A_68, B_69), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_69, '#skF_7') | ~r2_hidden(A_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_125])).
% 3.52/1.61  tff(c_22, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.61  tff(c_217, plain, (![B_69, A_68]: (r2_hidden(B_69, '#skF_5') | ~r2_hidden(B_69, '#skF_7') | ~r2_hidden(A_68, '#skF_6'))), inference(resolution, [status(thm)], [c_200, c_22])).
% 3.52/1.61  tff(c_312, plain, (![A_83]: (~r2_hidden(A_83, '#skF_6'))), inference(splitLeft, [status(thm)], [c_217])).
% 3.52/1.61  tff(c_342, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_18, c_312])).
% 3.52/1.61  tff(c_346, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_28])).
% 3.52/1.61  tff(c_310, plain, (![A_68]: (~r2_hidden(A_68, '#skF_6'))), inference(splitLeft, [status(thm)], [c_217])).
% 3.52/1.61  tff(c_372, plain, (![B_63, A_62]: (~r2_hidden(B_63, '#skF_5') | ~r2_hidden(A_62, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_310, c_146])).
% 3.52/1.61  tff(c_374, plain, (![A_88]: (~r2_hidden(A_88, '#skF_4'))), inference(splitLeft, [status(thm)], [c_372])).
% 3.52/1.61  tff(c_393, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_374])).
% 3.52/1.61  tff(c_76, plain, (![A_11, B_33]: (r2_hidden('#skF_3'(A_11), B_33) | ~r1_tarski(A_11, B_33) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_18, c_67])).
% 3.52/1.61  tff(c_339, plain, (![A_11]: (~r1_tarski(A_11, '#skF_6') | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_76, c_312])).
% 3.52/1.61  tff(c_410, plain, (![A_91]: (~r1_tarski(A_91, '#skF_6') | A_91='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_339])).
% 3.52/1.61  tff(c_414, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_393, c_410])).
% 3.52/1.61  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_414])).
% 3.52/1.61  tff(c_428, plain, (![B_92]: (~r2_hidden(B_92, '#skF_5'))), inference(splitRight, [status(thm)], [c_372])).
% 3.52/1.61  tff(c_447, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_428])).
% 3.52/1.61  tff(c_465, plain, (![A_95]: (~r1_tarski(A_95, '#skF_6') | A_95='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_339])).
% 3.52/1.61  tff(c_469, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_447, c_465])).
% 3.52/1.61  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_346, c_469])).
% 3.52/1.61  tff(c_538, plain, (![B_98]: (r2_hidden(B_98, '#skF_5') | ~r2_hidden(B_98, '#skF_7'))), inference(splitRight, [status(thm)], [c_217])).
% 3.52/1.61  tff(c_1123, plain, (![B_146]: (r2_hidden('#skF_1'('#skF_7', B_146), '#skF_5') | r1_tarski('#skF_7', B_146))), inference(resolution, [status(thm)], [c_6, c_538])).
% 3.52/1.61  tff(c_1133, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1123, c_4])).
% 3.52/1.61  tff(c_1140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_235, c_1133])).
% 3.52/1.61  tff(c_1141, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_234])).
% 3.52/1.61  tff(c_24, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.61  tff(c_218, plain, (![A_68, B_69]: (r2_hidden(A_68, '#skF_4') | ~r2_hidden(B_69, '#skF_7') | ~r2_hidden(A_68, '#skF_6'))), inference(resolution, [status(thm)], [c_200, c_24])).
% 3.52/1.61  tff(c_1170, plain, (![A_68, B_69]: (r2_hidden(A_68, '#skF_4') | ~r2_hidden(B_69, '#skF_5') | ~r2_hidden(A_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_218])).
% 3.52/1.61  tff(c_1179, plain, (![B_152]: (~r2_hidden(B_152, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1170])).
% 3.52/1.61  tff(c_1203, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_18, c_1179])).
% 3.52/1.61  tff(c_1212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1203])).
% 3.52/1.61  tff(c_1214, plain, (![A_153]: (r2_hidden(A_153, '#skF_4') | ~r2_hidden(A_153, '#skF_6'))), inference(splitRight, [status(thm)], [c_1170])).
% 3.52/1.61  tff(c_1614, plain, (![B_202]: (r2_hidden('#skF_1'('#skF_6', B_202), '#skF_4') | r1_tarski('#skF_6', B_202))), inference(resolution, [status(thm)], [c_6, c_1214])).
% 3.52/1.61  tff(c_1624, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1614, c_4])).
% 3.52/1.61  tff(c_1631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1561, c_1561, c_1624])).
% 3.52/1.61  tff(c_1632, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_26])).
% 3.52/1.61  tff(c_1700, plain, (![A_232, B_233, C_234, D_235]: (r2_hidden(k4_tarski(A_232, B_233), k2_zfmisc_1(C_234, D_235)) | ~r2_hidden(B_233, D_235) | ~r2_hidden(A_232, C_234))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.61  tff(c_1633, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 3.52/1.61  tff(c_1638, plain, (k2_zfmisc_1('#skF_4', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_32])).
% 3.52/1.61  tff(c_1695, plain, (![B_226, D_227, A_228, C_229]: (r2_hidden(B_226, D_227) | ~r2_hidden(k4_tarski(A_228, B_226), k2_zfmisc_1(C_229, D_227)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.61  tff(c_1698, plain, (![B_226, A_228]: (r2_hidden(B_226, '#skF_7') | ~r2_hidden(k4_tarski(A_228, B_226), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1638, c_1695])).
% 3.52/1.61  tff(c_1716, plain, (![B_233, A_232]: (r2_hidden(B_233, '#skF_7') | ~r2_hidden(B_233, '#skF_5') | ~r2_hidden(A_232, '#skF_4'))), inference(resolution, [status(thm)], [c_1700, c_1698])).
% 3.52/1.61  tff(c_1721, plain, (![A_236]: (~r2_hidden(A_236, '#skF_4'))), inference(splitLeft, [status(thm)], [c_1716])).
% 3.52/1.61  tff(c_1737, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_1721])).
% 3.52/1.61  tff(c_1744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1737])).
% 3.52/1.61  tff(c_1746, plain, (![B_237]: (r2_hidden(B_237, '#skF_7') | ~r2_hidden(B_237, '#skF_5'))), inference(splitRight, [status(thm)], [c_1716])).
% 3.52/1.61  tff(c_1788, plain, (![A_241]: (r1_tarski(A_241, '#skF_7') | ~r2_hidden('#skF_1'(A_241, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_1746, c_4])).
% 3.52/1.61  tff(c_1793, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_1788])).
% 3.52/1.61  tff(c_1760, plain, (![A_238, B_239]: (r2_hidden(k4_tarski(A_238, B_239), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_239, '#skF_7') | ~r2_hidden(A_238, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1638, c_1700])).
% 3.52/1.61  tff(c_1773, plain, (![B_239, A_238]: (r2_hidden(B_239, '#skF_5') | ~r2_hidden(B_239, '#skF_7') | ~r2_hidden(A_238, '#skF_4'))), inference(resolution, [status(thm)], [c_1760, c_22])).
% 3.52/1.61  tff(c_1831, plain, (![A_250]: (~r2_hidden(A_250, '#skF_4'))), inference(splitLeft, [status(thm)], [c_1773])).
% 3.52/1.61  tff(c_1851, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_1831])).
% 3.52/1.61  tff(c_1859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1851])).
% 3.52/1.61  tff(c_1861, plain, (![B_251]: (r2_hidden(B_251, '#skF_5') | ~r2_hidden(B_251, '#skF_7'))), inference(splitRight, [status(thm)], [c_1773])).
% 3.52/1.61  tff(c_1933, plain, (![A_257]: (r2_hidden('#skF_2'(A_257, '#skF_7'), '#skF_5') | ~r2_xboole_0(A_257, '#skF_7'))), inference(resolution, [status(thm)], [c_16, c_1861])).
% 3.52/1.61  tff(c_1946, plain, (~r2_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_1933, c_14])).
% 3.52/1.61  tff(c_1975, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_8, c_1946])).
% 3.52/1.61  tff(c_1978, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1793, c_1975])).
% 3.52/1.61  tff(c_1980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1632, c_1978])).
% 3.52/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.61  
% 3.52/1.61  Inference rules
% 3.52/1.61  ----------------------
% 3.52/1.61  #Ref     : 0
% 3.52/1.61  #Sup     : 395
% 3.52/1.61  #Fact    : 0
% 3.52/1.61  #Define  : 0
% 3.52/1.61  #Split   : 17
% 3.52/1.61  #Chain   : 0
% 3.52/1.61  #Close   : 0
% 3.52/1.61  
% 3.52/1.61  Ordering : KBO
% 3.52/1.61  
% 3.52/1.61  Simplification rules
% 3.52/1.61  ----------------------
% 3.52/1.61  #Subsume      : 74
% 3.52/1.61  #Demod        : 91
% 3.52/1.61  #Tautology    : 77
% 3.52/1.61  #SimpNegUnit  : 32
% 3.52/1.61  #BackRed      : 53
% 3.52/1.61  
% 3.52/1.61  #Partial instantiations: 0
% 3.52/1.61  #Strategies tried      : 1
% 3.52/1.61  
% 3.52/1.61  Timing (in seconds)
% 3.52/1.61  ----------------------
% 3.52/1.61  Preprocessing        : 0.28
% 3.52/1.62  Parsing              : 0.15
% 3.52/1.62  CNF conversion       : 0.02
% 3.52/1.62  Main loop            : 0.55
% 3.52/1.62  Inferencing          : 0.21
% 3.52/1.62  Reduction            : 0.14
% 3.52/1.62  Demodulation         : 0.09
% 3.52/1.62  BG Simplification    : 0.03
% 3.52/1.62  Subsumption          : 0.13
% 3.52/1.62  Abstraction          : 0.02
% 3.52/1.62  MUC search           : 0.00
% 3.52/1.62  Cooper               : 0.00
% 3.52/1.62  Total                : 0.88
% 3.52/1.62  Index Insertion      : 0.00
% 3.52/1.62  Index Deletion       : 0.00
% 3.52/1.62  Index Matching       : 0.00
% 3.52/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
