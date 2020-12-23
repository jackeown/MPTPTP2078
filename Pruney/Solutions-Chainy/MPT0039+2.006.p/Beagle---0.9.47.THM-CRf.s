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
% DateTime   : Thu Dec  3 09:42:43 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 836 expanded)
%              Number of leaves         :   14 ( 286 expanded)
%              Depth                    :   18
%              Number of atoms          :  140 (2208 expanded)
%              Number of equality atoms :   44 ( 657 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_22,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_732,plain,(
    ! [A_60,B_61,C_62] :
      ( r2_hidden('#skF_1'(A_60,B_61,C_62),A_60)
      | r2_hidden('#skF_2'(A_60,B_61,C_62),C_62)
      | k4_xboole_0(A_60,B_61) = C_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_778,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_2'(A_60,B_61,A_60),A_60)
      | k4_xboole_0(A_60,B_61) = A_60 ) ),
    inference(resolution,[status(thm)],[c_732,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1130,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r2_hidden('#skF_1'(A_89,B_90,C_91),C_91)
      | r2_hidden('#skF_2'(A_89,B_90,C_91),B_90)
      | ~ r2_hidden('#skF_2'(A_89,B_90,C_91),A_89)
      | k4_xboole_0(A_89,B_90) = C_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1915,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_2'(A_125,B_126,A_125),B_126)
      | ~ r2_hidden('#skF_2'(A_125,B_126,A_125),A_125)
      | k4_xboole_0(A_125,B_126) = A_125 ) ),
    inference(resolution,[status(thm)],[c_12,c_1130])).

tff(c_1984,plain,(
    ! [A_130,B_131] :
      ( r2_hidden('#skF_2'(A_130,B_131,A_130),B_131)
      | k4_xboole_0(A_130,B_131) = A_130 ) ),
    inference(resolution,[status(thm)],[c_778,c_1915])).

tff(c_837,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70,A_69),A_69)
      | k4_xboole_0(A_69,B_70) = A_69 ) ),
    inference(resolution,[status(thm)],[c_732,c_14])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [D_10,A_11,B_12] :
      ( r2_hidden(D_10,A_11)
      | ~ r2_hidden(D_10,k4_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_488,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_42,B_43)),A_42)
      | k4_xboole_0(A_42,B_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_39,plain,(
    ! [D_13,B_14,A_15] :
      ( ~ r2_hidden(D_13,B_14)
      | ~ r2_hidden(D_13,k4_xboole_0(A_15,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_15,B_14] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_15,B_14)),B_14)
      | k4_xboole_0(A_15,B_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_39])).

tff(c_532,plain,(
    ! [A_47] : k4_xboole_0(A_47,A_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_488,c_47])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_546,plain,(
    ! [D_6,A_47] :
      ( ~ r2_hidden(D_6,A_47)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_4])).

tff(c_870,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden('#skF_2'(A_69,B_70,A_69),k1_xboole_0)
      | k4_xboole_0(A_69,B_70) = A_69 ) ),
    inference(resolution,[status(thm)],[c_837,c_546])).

tff(c_2031,plain,(
    ! [A_130] : k4_xboole_0(A_130,k1_xboole_0) = A_130 ),
    inference(resolution,[status(thm)],[c_1984,c_870])).

tff(c_24,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    ! [D_16,A_17,B_18] :
      ( r2_hidden(D_16,k4_xboole_0(A_17,B_18))
      | r2_hidden(D_16,B_18)
      | ~ r2_hidden(D_16,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,k4_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(D_22,'#skF_4')
      | ~ r2_hidden(D_22,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_98,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,'#skF_4')
      | ~ r2_hidden(D_22,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_83,c_4])).

tff(c_5218,plain,(
    ! [B_211,C_212] :
      ( r2_hidden('#skF_1'('#skF_5',B_211,C_212),'#skF_4')
      | r2_hidden('#skF_2'('#skF_5',B_211,C_212),C_212)
      | k4_xboole_0('#skF_5',B_211) = C_212 ) ),
    inference(resolution,[status(thm)],[c_732,c_98])).

tff(c_5275,plain,(
    ! [B_211] :
      ( r2_hidden('#skF_2'('#skF_5',B_211,'#skF_4'),'#skF_4')
      | k4_xboole_0('#skF_5',B_211) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_5218,c_14])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,'#skF_5')
      | ~ r2_hidden(D_19,k4_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_69,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,'#skF_5')
      | ~ r2_hidden(D_6,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1179,plain,(
    ! [A_95,B_96,B_97] :
      ( r2_hidden('#skF_3'(k4_xboole_0(k4_xboole_0(A_95,B_96),B_97)),A_95)
      | k4_xboole_0(k4_xboole_0(A_95,B_96),B_97) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_488,c_6])).

tff(c_1507,plain,(
    ! [B_105,B_106] :
      ( r2_hidden('#skF_3'(k4_xboole_0(k4_xboole_0('#skF_5',B_105),B_106)),'#skF_4')
      | k4_xboole_0(k4_xboole_0('#skF_5',B_105),B_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1179,c_98])).

tff(c_1548,plain,(
    ! [B_105] : k4_xboole_0(k4_xboole_0('#skF_5',B_105),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1507,c_47])).

tff(c_871,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_2'('#skF_5',B_70,'#skF_5'),'#skF_4')
      | k4_xboole_0('#skF_5',B_70) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_837,c_98])).

tff(c_3040,plain,(
    ! [A_163,A_164,B_165] :
      ( ~ r2_hidden('#skF_2'(A_163,k4_xboole_0(A_164,B_165),A_163),B_165)
      | k4_xboole_0(A_163,k4_xboole_0(A_164,B_165)) = A_163 ) ),
    inference(resolution,[status(thm)],[c_1984,c_4])).

tff(c_3112,plain,(
    ! [A_164] : k4_xboole_0('#skF_5',k4_xboole_0(A_164,'#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_871,c_3040])).

tff(c_7091,plain,(
    ! [B_271] :
      ( r2_hidden('#skF_2'('#skF_5',B_271,'#skF_4'),'#skF_4')
      | k4_xboole_0('#skF_5',B_271) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_5218,c_14])).

tff(c_904,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_1'(A_73,B_74,C_75),A_73)
      | r2_hidden('#skF_2'(A_73,B_74,C_75),B_74)
      | ~ r2_hidden('#skF_2'(A_73,B_74,C_75),A_73)
      | k4_xboole_0(A_73,B_74) = C_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_964,plain,(
    ! [A_73,A_1,B_2,C_75] :
      ( ~ r2_hidden('#skF_2'(A_73,k4_xboole_0(A_1,B_2),C_75),B_2)
      | r2_hidden('#skF_1'(A_73,k4_xboole_0(A_1,B_2),C_75),A_73)
      | ~ r2_hidden('#skF_2'(A_73,k4_xboole_0(A_1,B_2),C_75),A_73)
      | k4_xboole_0(A_73,k4_xboole_0(A_1,B_2)) = C_75 ) ),
    inference(resolution,[status(thm)],[c_904,c_4])).

tff(c_7094,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'('#skF_5',k4_xboole_0(A_1,'#skF_4'),'#skF_4'),'#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k4_xboole_0(A_1,'#skF_4'),'#skF_4'),'#skF_5')
      | k4_xboole_0('#skF_5',k4_xboole_0(A_1,'#skF_4')) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_7091,c_964])).

tff(c_7096,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'('#skF_5',k4_xboole_0(A_1,'#skF_4'),'#skF_4'),'#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k4_xboole_0(A_1,'#skF_4'),'#skF_4'),'#skF_5')
      | '#skF_5' = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3112,c_7094])).

tff(c_7614,plain,(
    ! [A_291] :
      ( r2_hidden('#skF_1'('#skF_5',k4_xboole_0(A_291,'#skF_4'),'#skF_4'),'#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k4_xboole_0(A_291,'#skF_4'),'#skF_4'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_7096])).

tff(c_7630,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_1'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k4_xboole_0(k4_xboole_0('#skF_5',B_105),'#skF_4'),'#skF_4'),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1548,c_7614])).

tff(c_7652,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1548,c_7630])).

tff(c_8199,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7652])).

tff(c_8248,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_8199])).

tff(c_8254,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5275,c_8248])).

tff(c_3113,plain,(
    ! [A_60,A_164] : k4_xboole_0(A_60,k4_xboole_0(A_164,A_60)) = A_60 ),
    inference(resolution,[status(thm)],[c_778,c_3040])).

tff(c_3434,plain,(
    ! [A_171,A_172] : k4_xboole_0(A_171,k4_xboole_0(A_172,A_171)) = A_171 ),
    inference(resolution,[status(thm)],[c_778,c_3040])).

tff(c_3555,plain,(
    ! [A_164,A_60] : k4_xboole_0(k4_xboole_0(A_164,A_60),A_60) = k4_xboole_0(A_164,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_3113,c_3434])).

tff(c_8326,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8254,c_3555])).

tff(c_8439,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_2031,c_8326])).

tff(c_8441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_8439])).

tff(c_8443,plain,(
    r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_7652])).

tff(c_8442,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_7652])).

tff(c_8447,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8442,c_98])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8568,plain,
    ( r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_5')
    | k4_xboole_0('#skF_5',k1_xboole_0) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8447,c_8])).

tff(c_8574,plain,
    ( r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),k1_xboole_0)
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_8443,c_8568])).

tff(c_8575,plain,(
    r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_8574])).

tff(c_549,plain,(
    ! [D_6,A_47] :
      ( r2_hidden(D_6,A_47)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_6])).

tff(c_8584,plain,(
    ! [A_47] : r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),A_47) ),
    inference(resolution,[status(thm)],[c_8575,c_549])).

tff(c_8589,plain,(
    ! [A_312] : r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),A_312) ),
    inference(resolution,[status(thm)],[c_8575,c_549])).

tff(c_3659,plain,(
    ! [A_175,A_176] :
      ( k4_xboole_0(A_175,k4_xboole_0(A_176,'#skF_5')) = A_175
      | ~ r2_hidden('#skF_2'(A_175,k4_xboole_0(A_176,'#skF_5'),A_175),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_3040])).

tff(c_3712,plain,(
    ! [A_176] : k4_xboole_0('#skF_4',k4_xboole_0(A_176,'#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_778,c_3659])).

tff(c_4438,plain,(
    ! [D_196,A_197,A_198] :
      ( ~ r2_hidden(D_196,k4_xboole_0(A_197,A_198))
      | ~ r2_hidden(D_196,A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3434,c_4])).

tff(c_4452,plain,(
    ! [D_196,A_176] :
      ( ~ r2_hidden(D_196,'#skF_4')
      | ~ r2_hidden(D_196,k4_xboole_0(A_176,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3712,c_4438])).

tff(c_8593,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k1_xboole_0,'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8589,c_4452])).

tff(c_8627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8584,c_8593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.56  
% 7.38/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.56  %$ r2_hidden > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 7.38/2.56  
% 7.38/2.56  %Foreground sorts:
% 7.38/2.56  
% 7.38/2.56  
% 7.38/2.56  %Background operators:
% 7.38/2.56  
% 7.38/2.56  
% 7.38/2.56  %Foreground operators:
% 7.38/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.38/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.38/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.38/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.38/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.38/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.38/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.38/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.38/2.56  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.38/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.38/2.56  
% 7.38/2.57  tff(f_48, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 7.38/2.57  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.38/2.57  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.38/2.57  tff(c_22, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.38/2.57  tff(c_732, plain, (![A_60, B_61, C_62]: (r2_hidden('#skF_1'(A_60, B_61, C_62), A_60) | r2_hidden('#skF_2'(A_60, B_61, C_62), C_62) | k4_xboole_0(A_60, B_61)=C_62)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.57  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_778, plain, (![A_60, B_61]: (r2_hidden('#skF_2'(A_60, B_61, A_60), A_60) | k4_xboole_0(A_60, B_61)=A_60)), inference(resolution, [status(thm)], [c_732, c_14])).
% 7.38/2.58  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_1130, plain, (![A_89, B_90, C_91]: (~r2_hidden('#skF_1'(A_89, B_90, C_91), C_91) | r2_hidden('#skF_2'(A_89, B_90, C_91), B_90) | ~r2_hidden('#skF_2'(A_89, B_90, C_91), A_89) | k4_xboole_0(A_89, B_90)=C_91)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_1915, plain, (![A_125, B_126]: (r2_hidden('#skF_2'(A_125, B_126, A_125), B_126) | ~r2_hidden('#skF_2'(A_125, B_126, A_125), A_125) | k4_xboole_0(A_125, B_126)=A_125)), inference(resolution, [status(thm)], [c_12, c_1130])).
% 7.38/2.58  tff(c_1984, plain, (![A_130, B_131]: (r2_hidden('#skF_2'(A_130, B_131, A_130), B_131) | k4_xboole_0(A_130, B_131)=A_130)), inference(resolution, [status(thm)], [c_778, c_1915])).
% 7.38/2.58  tff(c_837, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70, A_69), A_69) | k4_xboole_0(A_69, B_70)=A_69)), inference(resolution, [status(thm)], [c_732, c_14])).
% 7.38/2.58  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.38/2.58  tff(c_30, plain, (![D_10, A_11, B_12]: (r2_hidden(D_10, A_11) | ~r2_hidden(D_10, k4_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_488, plain, (![A_42, B_43]: (r2_hidden('#skF_3'(k4_xboole_0(A_42, B_43)), A_42) | k4_xboole_0(A_42, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_30])).
% 7.38/2.58  tff(c_39, plain, (![D_13, B_14, A_15]: (~r2_hidden(D_13, B_14) | ~r2_hidden(D_13, k4_xboole_0(A_15, B_14)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_47, plain, (![A_15, B_14]: (~r2_hidden('#skF_3'(k4_xboole_0(A_15, B_14)), B_14) | k4_xboole_0(A_15, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_39])).
% 7.38/2.58  tff(c_532, plain, (![A_47]: (k4_xboole_0(A_47, A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_488, c_47])).
% 7.38/2.58  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_546, plain, (![D_6, A_47]: (~r2_hidden(D_6, A_47) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_532, c_4])).
% 7.38/2.58  tff(c_870, plain, (![A_69, B_70]: (~r2_hidden('#skF_2'(A_69, B_70, A_69), k1_xboole_0) | k4_xboole_0(A_69, B_70)=A_69)), inference(resolution, [status(thm)], [c_837, c_546])).
% 7.38/2.58  tff(c_2031, plain, (![A_130]: (k4_xboole_0(A_130, k1_xboole_0)=A_130)), inference(resolution, [status(thm)], [c_1984, c_870])).
% 7.38/2.58  tff(c_24, plain, (k4_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.38/2.58  tff(c_48, plain, (![D_16, A_17, B_18]: (r2_hidden(D_16, k4_xboole_0(A_17, B_18)) | r2_hidden(D_16, B_18) | ~r2_hidden(D_16, A_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_83, plain, (![D_22]: (r2_hidden(D_22, k4_xboole_0('#skF_4', '#skF_5')) | r2_hidden(D_22, '#skF_4') | ~r2_hidden(D_22, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_48])).
% 7.38/2.58  tff(c_98, plain, (![D_22]: (r2_hidden(D_22, '#skF_4') | ~r2_hidden(D_22, '#skF_5'))), inference(resolution, [status(thm)], [c_83, c_4])).
% 7.38/2.58  tff(c_5218, plain, (![B_211, C_212]: (r2_hidden('#skF_1'('#skF_5', B_211, C_212), '#skF_4') | r2_hidden('#skF_2'('#skF_5', B_211, C_212), C_212) | k4_xboole_0('#skF_5', B_211)=C_212)), inference(resolution, [status(thm)], [c_732, c_98])).
% 7.38/2.58  tff(c_5275, plain, (![B_211]: (r2_hidden('#skF_2'('#skF_5', B_211, '#skF_4'), '#skF_4') | k4_xboole_0('#skF_5', B_211)='#skF_4')), inference(resolution, [status(thm)], [c_5218, c_14])).
% 7.38/2.58  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_60, plain, (![D_19]: (r2_hidden(D_19, '#skF_5') | ~r2_hidden(D_19, k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_30])).
% 7.38/2.58  tff(c_69, plain, (![D_6]: (r2_hidden(D_6, '#skF_5') | ~r2_hidden(D_6, '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_60])).
% 7.38/2.58  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_1179, plain, (![A_95, B_96, B_97]: (r2_hidden('#skF_3'(k4_xboole_0(k4_xboole_0(A_95, B_96), B_97)), A_95) | k4_xboole_0(k4_xboole_0(A_95, B_96), B_97)=k1_xboole_0)), inference(resolution, [status(thm)], [c_488, c_6])).
% 7.38/2.58  tff(c_1507, plain, (![B_105, B_106]: (r2_hidden('#skF_3'(k4_xboole_0(k4_xboole_0('#skF_5', B_105), B_106)), '#skF_4') | k4_xboole_0(k4_xboole_0('#skF_5', B_105), B_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1179, c_98])).
% 7.38/2.58  tff(c_1548, plain, (![B_105]: (k4_xboole_0(k4_xboole_0('#skF_5', B_105), '#skF_4')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1507, c_47])).
% 7.38/2.58  tff(c_871, plain, (![B_70]: (r2_hidden('#skF_2'('#skF_5', B_70, '#skF_5'), '#skF_4') | k4_xboole_0('#skF_5', B_70)='#skF_5')), inference(resolution, [status(thm)], [c_837, c_98])).
% 7.38/2.58  tff(c_3040, plain, (![A_163, A_164, B_165]: (~r2_hidden('#skF_2'(A_163, k4_xboole_0(A_164, B_165), A_163), B_165) | k4_xboole_0(A_163, k4_xboole_0(A_164, B_165))=A_163)), inference(resolution, [status(thm)], [c_1984, c_4])).
% 7.38/2.58  tff(c_3112, plain, (![A_164]: (k4_xboole_0('#skF_5', k4_xboole_0(A_164, '#skF_4'))='#skF_5')), inference(resolution, [status(thm)], [c_871, c_3040])).
% 7.38/2.58  tff(c_7091, plain, (![B_271]: (r2_hidden('#skF_2'('#skF_5', B_271, '#skF_4'), '#skF_4') | k4_xboole_0('#skF_5', B_271)='#skF_4')), inference(resolution, [status(thm)], [c_5218, c_14])).
% 7.38/2.58  tff(c_904, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_1'(A_73, B_74, C_75), A_73) | r2_hidden('#skF_2'(A_73, B_74, C_75), B_74) | ~r2_hidden('#skF_2'(A_73, B_74, C_75), A_73) | k4_xboole_0(A_73, B_74)=C_75)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_964, plain, (![A_73, A_1, B_2, C_75]: (~r2_hidden('#skF_2'(A_73, k4_xboole_0(A_1, B_2), C_75), B_2) | r2_hidden('#skF_1'(A_73, k4_xboole_0(A_1, B_2), C_75), A_73) | ~r2_hidden('#skF_2'(A_73, k4_xboole_0(A_1, B_2), C_75), A_73) | k4_xboole_0(A_73, k4_xboole_0(A_1, B_2))=C_75)), inference(resolution, [status(thm)], [c_904, c_4])).
% 7.38/2.58  tff(c_7094, plain, (![A_1]: (r2_hidden('#skF_1'('#skF_5', k4_xboole_0(A_1, '#skF_4'), '#skF_4'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k4_xboole_0(A_1, '#skF_4'), '#skF_4'), '#skF_5') | k4_xboole_0('#skF_5', k4_xboole_0(A_1, '#skF_4'))='#skF_4')), inference(resolution, [status(thm)], [c_7091, c_964])).
% 7.38/2.58  tff(c_7096, plain, (![A_1]: (r2_hidden('#skF_1'('#skF_5', k4_xboole_0(A_1, '#skF_4'), '#skF_4'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k4_xboole_0(A_1, '#skF_4'), '#skF_4'), '#skF_5') | '#skF_5'='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3112, c_7094])).
% 7.38/2.58  tff(c_7614, plain, (![A_291]: (r2_hidden('#skF_1'('#skF_5', k4_xboole_0(A_291, '#skF_4'), '#skF_4'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k4_xboole_0(A_291, '#skF_4'), '#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_22, c_7096])).
% 7.38/2.58  tff(c_7630, plain, (![B_105]: (r2_hidden('#skF_1'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k4_xboole_0(k4_xboole_0('#skF_5', B_105), '#skF_4'), '#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1548, c_7614])).
% 7.38/2.58  tff(c_7652, plain, (r2_hidden('#skF_1'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1548, c_7630])).
% 7.38/2.58  tff(c_8199, plain, (~r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_7652])).
% 7.38/2.58  tff(c_8248, plain, (~r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_69, c_8199])).
% 7.38/2.58  tff(c_8254, plain, (k4_xboole_0('#skF_5', k1_xboole_0)='#skF_4'), inference(resolution, [status(thm)], [c_5275, c_8248])).
% 7.38/2.58  tff(c_3113, plain, (![A_60, A_164]: (k4_xboole_0(A_60, k4_xboole_0(A_164, A_60))=A_60)), inference(resolution, [status(thm)], [c_778, c_3040])).
% 7.38/2.58  tff(c_3434, plain, (![A_171, A_172]: (k4_xboole_0(A_171, k4_xboole_0(A_172, A_171))=A_171)), inference(resolution, [status(thm)], [c_778, c_3040])).
% 7.38/2.58  tff(c_3555, plain, (![A_164, A_60]: (k4_xboole_0(k4_xboole_0(A_164, A_60), A_60)=k4_xboole_0(A_164, A_60))), inference(superposition, [status(thm), theory('equality')], [c_3113, c_3434])).
% 7.38/2.58  tff(c_8326, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8254, c_3555])).
% 7.38/2.58  tff(c_8439, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_2031, c_8326])).
% 7.38/2.58  tff(c_8441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_8439])).
% 7.38/2.58  tff(c_8443, plain, (r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_7652])).
% 7.38/2.58  tff(c_8442, plain, (r2_hidden('#skF_1'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_7652])).
% 7.38/2.58  tff(c_8447, plain, (r2_hidden('#skF_1'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_8442, c_98])).
% 7.38/2.58  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.38/2.58  tff(c_8568, plain, (r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_5') | k4_xboole_0('#skF_5', k1_xboole_0)='#skF_4'), inference(resolution, [status(thm)], [c_8447, c_8])).
% 7.38/2.58  tff(c_8574, plain, (r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), k1_xboole_0) | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_8443, c_8568])).
% 7.38/2.58  tff(c_8575, plain, (r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_22, c_8574])).
% 7.38/2.58  tff(c_549, plain, (![D_6, A_47]: (r2_hidden(D_6, A_47) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_532, c_6])).
% 7.38/2.58  tff(c_8584, plain, (![A_47]: (r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), A_47))), inference(resolution, [status(thm)], [c_8575, c_549])).
% 7.38/2.58  tff(c_8589, plain, (![A_312]: (r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), A_312))), inference(resolution, [status(thm)], [c_8575, c_549])).
% 7.38/2.58  tff(c_3659, plain, (![A_175, A_176]: (k4_xboole_0(A_175, k4_xboole_0(A_176, '#skF_5'))=A_175 | ~r2_hidden('#skF_2'(A_175, k4_xboole_0(A_176, '#skF_5'), A_175), '#skF_4'))), inference(resolution, [status(thm)], [c_69, c_3040])).
% 7.38/2.58  tff(c_3712, plain, (![A_176]: (k4_xboole_0('#skF_4', k4_xboole_0(A_176, '#skF_5'))='#skF_4')), inference(resolution, [status(thm)], [c_778, c_3659])).
% 7.38/2.58  tff(c_4438, plain, (![D_196, A_197, A_198]: (~r2_hidden(D_196, k4_xboole_0(A_197, A_198)) | ~r2_hidden(D_196, A_198))), inference(superposition, [status(thm), theory('equality')], [c_3434, c_4])).
% 7.38/2.58  tff(c_4452, plain, (![D_196, A_176]: (~r2_hidden(D_196, '#skF_4') | ~r2_hidden(D_196, k4_xboole_0(A_176, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_3712, c_4438])).
% 7.38/2.58  tff(c_8593, plain, (~r2_hidden('#skF_2'('#skF_5', k1_xboole_0, '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_8589, c_4452])).
% 7.38/2.58  tff(c_8627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8584, c_8593])).
% 7.38/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.58  
% 7.38/2.58  Inference rules
% 7.38/2.58  ----------------------
% 7.38/2.58  #Ref     : 0
% 7.38/2.58  #Sup     : 1946
% 7.38/2.58  #Fact    : 0
% 7.38/2.58  #Define  : 0
% 7.38/2.58  #Split   : 6
% 7.38/2.58  #Chain   : 0
% 7.38/2.58  #Close   : 0
% 7.38/2.58  
% 7.38/2.58  Ordering : KBO
% 7.38/2.58  
% 7.38/2.58  Simplification rules
% 7.38/2.58  ----------------------
% 7.38/2.58  #Subsume      : 737
% 7.38/2.58  #Demod        : 2067
% 7.38/2.58  #Tautology    : 602
% 7.38/2.58  #SimpNegUnit  : 102
% 7.38/2.58  #BackRed      : 51
% 7.38/2.58  
% 7.38/2.58  #Partial instantiations: 0
% 7.38/2.58  #Strategies tried      : 1
% 7.38/2.58  
% 7.38/2.58  Timing (in seconds)
% 7.38/2.58  ----------------------
% 7.38/2.58  Preprocessing        : 0.26
% 7.38/2.58  Parsing              : 0.13
% 7.38/2.58  CNF conversion       : 0.02
% 7.38/2.58  Main loop            : 1.55
% 7.38/2.58  Inferencing          : 0.48
% 7.38/2.58  Reduction            : 0.58
% 7.38/2.58  Demodulation         : 0.42
% 7.38/2.58  BG Simplification    : 0.04
% 7.38/2.58  Subsumption          : 0.37
% 7.38/2.58  Abstraction          : 0.07
% 7.38/2.58  MUC search           : 0.00
% 7.38/2.58  Cooper               : 0.00
% 7.38/2.58  Total                : 1.84
% 7.38/2.58  Index Insertion      : 0.00
% 7.38/2.58  Index Deletion       : 0.00
% 7.38/2.58  Index Matching       : 0.00
% 7.38/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
