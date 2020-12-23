%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:21 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 918 expanded)
%              Number of leaves         :   26 ( 300 expanded)
%              Depth                    :   16
%              Number of atoms          :  315 (1902 expanded)
%              Number of equality atoms :   90 ( 569 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_60,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,
    ( ~ r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_128,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1709,plain,(
    ! [A_139,C_140,B_141,D_142] : k3_xboole_0(k2_zfmisc_1(A_139,C_140),k2_zfmisc_1(B_141,D_142)) = k2_zfmisc_1(k3_xboole_0(A_139,B_141),k3_xboole_0(C_140,D_142)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_232,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_232])).

tff(c_1724,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1709,c_242])).

tff(c_243,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_232])).

tff(c_56,plain,(
    ! [A_30,C_32,B_31,D_33] : k3_xboole_0(k2_zfmisc_1(A_30,C_32),k2_zfmisc_1(B_31,D_33)) = k2_zfmisc_1(k3_xboole_0(A_30,B_31),k3_xboole_0(C_32,D_33)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_364,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,A_65)
      | ~ r2_hidden(D_64,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2279,plain,(
    ! [A_168,B_169,B_170] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_168,B_169),B_170),A_168)
      | r1_tarski(k3_xboole_0(A_168,B_169),B_170) ) ),
    inference(resolution,[status(thm)],[c_8,c_364])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2342,plain,(
    ! [A_171,B_172] : r1_tarski(k3_xboole_0(A_171,B_172),A_171) ),
    inference(resolution,[status(thm)],[c_2279,c_6])).

tff(c_2834,plain,(
    ! [A_190,B_191,C_192,D_193] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_190,B_191),k3_xboole_0(C_192,D_193)),k2_zfmisc_1(A_190,C_192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2342])).

tff(c_2930,plain,(
    ! [B_194,C_195,D_196] : r1_tarski(k2_zfmisc_1(B_194,k3_xboole_0(C_195,D_196)),k2_zfmisc_1(B_194,C_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_2834])).

tff(c_2957,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_2930])).

tff(c_50,plain,(
    ! [B_25,A_24,C_26] :
      ( ~ r1_tarski(k2_zfmisc_1(B_25,A_24),k2_zfmisc_1(C_26,A_24))
      | r1_tarski(B_25,C_26)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3130,plain,
    ( r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2957,c_50])).

tff(c_3136,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3130])).

tff(c_44,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_461,plain,(
    ! [C_77,A_78,B_79] :
      ( r1_tarski(k2_zfmisc_1(C_77,A_78),k2_zfmisc_1(C_77,B_79))
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_475,plain,(
    ! [A_22,A_78] :
      ( r1_tarski(k2_zfmisc_1(A_22,A_78),k1_xboole_0)
      | ~ r1_tarski(A_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_461])).

tff(c_386,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_913,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(A_100,B_102)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_8,c_386])).

tff(c_40,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_244,plain,(
    ! [A_21] : k3_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_232])).

tff(c_332,plain,(
    ! [D_55,B_56,A_57] :
      ( r2_hidden(D_55,B_56)
      | ~ r2_hidden(D_55,k3_xboole_0(A_57,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_338,plain,(
    ! [D_55,A_21] :
      ( r2_hidden(D_55,A_21)
      | ~ r2_hidden(D_55,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_332])).

tff(c_936,plain,(
    ! [A_103,B_104,A_105] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_105)
      | ~ r1_tarski(A_103,k1_xboole_0)
      | r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_913,c_338])).

tff(c_959,plain,(
    ! [A_106,A_107] :
      ( ~ r1_tarski(A_106,k1_xboole_0)
      | r1_tarski(A_106,A_107) ) ),
    inference(resolution,[status(thm)],[c_936,c_6])).

tff(c_970,plain,(
    ! [A_22,A_78,A_107] :
      ( r1_tarski(k2_zfmisc_1(A_22,A_78),A_107)
      | ~ r1_tarski(A_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_475,c_959])).

tff(c_1833,plain,(
    ! [A_107] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),A_107)
      | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_7'),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_970])).

tff(c_1894,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_7'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1833])).

tff(c_1437,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ r1_tarski(k2_zfmisc_1(A_128,B_129),k2_zfmisc_1(A_128,C_130))
      | r1_tarski(B_129,C_130)
      | k1_xboole_0 = A_128 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1482,plain,(
    ! [A_22,B_129] :
      ( ~ r1_tarski(k2_zfmisc_1(A_22,B_129),k1_xboole_0)
      | r1_tarski(B_129,k1_xboole_0)
      | k1_xboole_0 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1437])).

tff(c_1803,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0)
    | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_1482])).

tff(c_2682,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1894,c_1803])).

tff(c_2683,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2682])).

tff(c_2691,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_970,c_2683])).

tff(c_3137,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3136,c_2691])).

tff(c_3178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3137])).

tff(c_3179,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3130])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2398,plain,(
    ! [A_171,B_172] :
      ( k3_xboole_0(A_171,B_172) = A_171
      | ~ r1_tarski(A_171,k3_xboole_0(A_171,B_172)) ) ),
    inference(resolution,[status(thm)],[c_2342,c_28])).

tff(c_3214,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3179,c_2398])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3286,plain,(
    ! [D_203] :
      ( r2_hidden(D_203,'#skF_6')
      | ~ r2_hidden(D_203,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3214,c_12])).

tff(c_3433,plain,(
    ! [A_207] :
      ( r1_tarski(A_207,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_207,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3286,c_6])).

tff(c_3445,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_3433])).

tff(c_3451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_128,c_3445])).

tff(c_3452,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2682])).

tff(c_46,plain,(
    ! [B_23] : k2_zfmisc_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_390,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(k2_zfmisc_1(A_70,C_71),k2_zfmisc_1(B_72,C_71))
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_410,plain,(
    ! [A_70,B_23] :
      ( r1_tarski(k2_zfmisc_1(A_70,B_23),k1_xboole_0)
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_390])).

tff(c_971,plain,(
    ! [A_70,B_23,A_107] :
      ( r1_tarski(k2_zfmisc_1(A_70,B_23),A_107)
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_410,c_959])).

tff(c_1824,plain,(
    ! [A_107] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),A_107)
      | ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_971])).

tff(c_1893,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1824])).

tff(c_3455,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3452,c_1893])).

tff(c_3460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3455])).

tff(c_3464,plain,(
    ! [A_208] : r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),A_208) ),
    inference(splitRight,[status(thm)],[c_1833])).

tff(c_306,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_318,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_306])).

tff(c_3493,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3464,c_318])).

tff(c_3513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3493])).

tff(c_3518,plain,(
    ! [A_209] : r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),A_209) ),
    inference(splitRight,[status(thm)],[c_1824])).

tff(c_3547,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3518,c_318])).

tff(c_3567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3547])).

tff(c_3568,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3569,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3802,plain,(
    ! [B_230,A_231] :
      ( B_230 = A_231
      | ~ r1_tarski(B_230,A_231)
      | ~ r1_tarski(A_231,B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3812,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_3569,c_3802])).

tff(c_3818,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3812])).

tff(c_3570,plain,(
    ! [A_210,B_211] :
      ( k3_xboole_0(A_210,B_211) = A_210
      | ~ r1_tarski(A_210,B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3580,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3569,c_3570])).

tff(c_5110,plain,(
    ! [A_308,C_309,B_310,D_311] : k3_xboole_0(k2_zfmisc_1(A_308,C_309),k2_zfmisc_1(B_310,D_311)) = k2_zfmisc_1(k3_xboole_0(A_308,B_310),k3_xboole_0(C_309,D_311)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3590,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_36])).

tff(c_5125,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5110,c_3590])).

tff(c_5177,plain,(
    k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3580,c_5125])).

tff(c_3581,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_3570])).

tff(c_3819,plain,(
    ! [D_232,B_233,A_234] :
      ( r2_hidden(D_232,B_233)
      | ~ r2_hidden(D_232,k3_xboole_0(A_234,B_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7062,plain,(
    ! [A_393,B_394,B_395] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_393,B_394),B_395),B_394)
      | r1_tarski(k3_xboole_0(A_393,B_394),B_395) ) ),
    inference(resolution,[status(thm)],[c_8,c_3819])).

tff(c_7151,plain,(
    ! [A_396,B_397] : r1_tarski(k3_xboole_0(A_396,B_397),B_397) ),
    inference(resolution,[status(thm)],[c_7062,c_6])).

tff(c_8753,plain,(
    ! [A_430,B_431,C_432,D_433] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_430,B_431),k3_xboole_0(C_432,D_433)),k2_zfmisc_1(B_431,D_433)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_7151])).

tff(c_9102,plain,(
    ! [B_437,C_438,D_439] : r1_tarski(k2_zfmisc_1(B_437,k3_xboole_0(C_438,D_439)),k2_zfmisc_1(B_437,D_439)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3581,c_8753])).

tff(c_9157,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5177,c_9102])).

tff(c_48,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_tarski(k2_zfmisc_1(A_24,B_25),k2_zfmisc_1(A_24,C_26))
      | r1_tarski(B_25,C_26)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9226,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9157,c_48])).

tff(c_9237,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3568,c_9226])).

tff(c_3907,plain,(
    ! [A_246,C_247,B_248] :
      ( r1_tarski(k2_zfmisc_1(A_246,C_247),k2_zfmisc_1(B_248,C_247))
      | ~ r1_tarski(A_246,B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3927,plain,(
    ! [A_246,B_23] :
      ( r1_tarski(k2_zfmisc_1(A_246,B_23),k1_xboole_0)
      | ~ r1_tarski(A_246,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3907])).

tff(c_3879,plain,(
    ! [C_243,A_244,B_245] :
      ( r1_tarski(k2_zfmisc_1(C_243,A_244),k2_zfmisc_1(C_243,B_245))
      | ~ r1_tarski(A_244,B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3893,plain,(
    ! [A_22,A_244] :
      ( r1_tarski(k2_zfmisc_1(A_22,A_244),k1_xboole_0)
      | ~ r1_tarski(A_244,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3879])).

tff(c_3935,plain,(
    ! [A_249,A_250] :
      ( r1_tarski(k2_zfmisc_1(A_249,A_250),k1_xboole_0)
      | ~ r1_tarski(A_250,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3879])).

tff(c_3817,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_3802])).

tff(c_3964,plain,(
    ! [A_251,A_252] :
      ( k2_zfmisc_1(A_251,A_252) = k1_xboole_0
      | ~ r1_tarski(A_252,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3935,c_3817])).

tff(c_3973,plain,(
    ! [A_251,A_22,A_244] :
      ( k2_zfmisc_1(A_251,k2_zfmisc_1(A_22,A_244)) = k1_xboole_0
      | ~ r1_tarski(A_244,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3893,c_3964])).

tff(c_4473,plain,(
    ! [A_279,B_280,C_281] :
      ( ~ r1_tarski(k2_zfmisc_1(A_279,B_280),k2_zfmisc_1(A_279,C_281))
      | r1_tarski(B_280,C_281)
      | k1_xboole_0 = A_279 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4482,plain,(
    ! [A_251,C_281,A_22,A_244] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_251,C_281))
      | r1_tarski(k2_zfmisc_1(A_22,A_244),C_281)
      | k1_xboole_0 = A_251
      | ~ r1_tarski(A_244,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3973,c_4473])).

tff(c_4524,plain,(
    ! [A_22,A_244,C_281,A_251] :
      ( r1_tarski(k2_zfmisc_1(A_22,A_244),C_281)
      | k1_xboole_0 = A_251
      | ~ r1_tarski(A_244,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4482])).

tff(c_4631,plain,(
    ! [A_288,A_289,C_290] :
      ( r1_tarski(k2_zfmisc_1(A_288,A_289),C_290)
      | ~ r1_tarski(A_289,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_4524])).

tff(c_4694,plain,(
    ! [A_289,C_26,A_288] :
      ( r1_tarski(A_289,C_26)
      | k1_xboole_0 = A_288
      | ~ r1_tarski(A_289,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4631,c_48])).

tff(c_4786,plain,(
    ! [A_294,C_295] :
      ( r1_tarski(A_294,C_295)
      | ~ r1_tarski(A_294,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_4694])).

tff(c_4799,plain,(
    ! [A_246,B_23,C_295] :
      ( r1_tarski(k2_zfmisc_1(A_246,B_23),C_295)
      | ~ r1_tarski(A_246,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3927,c_4786])).

tff(c_4711,plain,(
    ! [B_291,A_292,C_293] :
      ( ~ r1_tarski(k2_zfmisc_1(B_291,A_292),k2_zfmisc_1(C_293,A_292))
      | r1_tarski(B_291,C_293)
      | k1_xboole_0 = A_292 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5516,plain,(
    ! [B_323,B_324] :
      ( ~ r1_tarski(k2_zfmisc_1(B_323,B_324),k1_xboole_0)
      | r1_tarski(B_323,k1_xboole_0)
      | k1_xboole_0 = B_324 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4711])).

tff(c_5519,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0)
    | r1_tarski('#skF_4',k1_xboole_0)
    | k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5177,c_5516])).

tff(c_8744,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5519])).

tff(c_8751,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4799,c_8744])).

tff(c_9241,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9237,c_8751])).

tff(c_9281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9241])).

tff(c_9283,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5519])).

tff(c_9350,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9283,c_3817])).

tff(c_9367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_9350])).

tff(c_9369,plain,(
    ! [A_441] : k1_xboole_0 = A_441 ),
    inference(splitRight,[status(thm)],[c_4694])).

tff(c_3811,plain,
    ( k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5')
    | ~ r1_tarski(k2_zfmisc_1('#skF_6','#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_3802])).

tff(c_3859,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_6','#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3811])).

tff(c_9424,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9369,c_3859])).

tff(c_9526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9424])).

tff(c_9528,plain,(
    ! [A_1099] : k1_xboole_0 = A_1099 ),
    inference(splitRight,[status(thm)],[c_4524])).

tff(c_9594,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9528,c_3859])).

tff(c_9696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9594])).

tff(c_9697,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3811])).

tff(c_9732,plain,(
    ! [A_1722,C_1723,B_1724] :
      ( r1_tarski(k2_zfmisc_1(A_1722,C_1723),k2_zfmisc_1(B_1724,C_1723))
      | ~ r1_tarski(A_1722,B_1724) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9746,plain,(
    ! [A_1722] :
      ( r1_tarski(k2_zfmisc_1(A_1722,'#skF_7'),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_1722,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9697,c_9732])).

tff(c_10435,plain,(
    ! [A_1758,B_1759,C_1760] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1758,B_1759),k2_zfmisc_1(A_1758,C_1760))
      | r1_tarski(B_1759,C_1760)
      | k1_xboole_0 = A_1758 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10439,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_9746,c_10435])).

tff(c_10499,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3569,c_10439])).

tff(c_10524,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10499])).

tff(c_10545,plain,(
    ! [B_23] : k2_zfmisc_1('#skF_4',B_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10524,c_10524,c_46])).

tff(c_10543,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10524,c_60])).

tff(c_10571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10545,c_10543])).

tff(c_10572,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_10499])).

tff(c_10584,plain,(
    k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_10572,c_36])).

tff(c_9813,plain,(
    ! [C_1729,A_1730,B_1731] :
      ( r1_tarski(k2_zfmisc_1(C_1729,A_1730),k2_zfmisc_1(C_1729,B_1731))
      | ~ r1_tarski(A_1730,B_1731) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10369,plain,(
    ! [A_1754] :
      ( r1_tarski(k2_zfmisc_1('#skF_6',A_1754),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_1754,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9697,c_9813])).

tff(c_10396,plain,(
    ! [A_1754] :
      ( k3_xboole_0(k2_zfmisc_1('#skF_6',A_1754),k2_zfmisc_1('#skF_4','#skF_5')) = k2_zfmisc_1('#skF_6',A_1754)
      | ~ r1_tarski(A_1754,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10369,c_36])).

tff(c_12756,plain,(
    ! [A_1847] :
      ( k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_4'),k3_xboole_0(A_1847,'#skF_5')) = k2_zfmisc_1('#skF_6',A_1847)
      | ~ r1_tarski(A_1847,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10396])).

tff(c_12834,plain,
    ( k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_4'),'#skF_7') = k2_zfmisc_1('#skF_6','#skF_7')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10584,c_12756])).

tff(c_12848,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_4'),'#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9697,c_12834])).

tff(c_10601,plain,(
    ! [B_1762,A_1763,C_1764] :
      ( ~ r1_tarski(k2_zfmisc_1(B_1762,A_1763),k2_zfmisc_1(C_1764,A_1763))
      | r1_tarski(B_1762,C_1764)
      | k1_xboole_0 = A_1763 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10646,plain,(
    ! [B_1762] :
      ( ~ r1_tarski(k2_zfmisc_1(B_1762,'#skF_7'),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_1762,'#skF_6')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9697,c_10601])).

tff(c_10873,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_10646])).

tff(c_9847,plain,(
    ! [A_1732,A_1733] :
      ( r1_tarski(k2_zfmisc_1(A_1732,A_1733),k1_xboole_0)
      | ~ r1_tarski(A_1733,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_9813])).

tff(c_9863,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0)
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9697,c_9847])).

tff(c_9899,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_9863])).

tff(c_10883,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10873,c_9899])).

tff(c_10901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10883])).

tff(c_10902,plain,(
    ! [B_1762] :
      ( ~ r1_tarski(k2_zfmisc_1(B_1762,'#skF_7'),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_1762,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_10646])).

tff(c_12875,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_5'))
    | r1_tarski(k3_xboole_0('#skF_6','#skF_4'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12848,c_10902])).

tff(c_12940,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12875])).

tff(c_10903,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10646])).

tff(c_10643,plain,(
    ! [C_1764] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(C_1764,'#skF_7'))
      | r1_tarski('#skF_6',C_1764)
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9697,c_10601])).

tff(c_10986,plain,(
    ! [C_1764] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(C_1764,'#skF_7'))
      | r1_tarski('#skF_6',C_1764) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10903,c_10643])).

tff(c_12881,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_5'))
    | r1_tarski('#skF_6',k3_xboole_0('#skF_6','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12848,c_10986])).

tff(c_12943,plain,(
    r1_tarski('#skF_6',k3_xboole_0('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12881])).

tff(c_12967,plain,
    ( k3_xboole_0('#skF_6','#skF_4') = '#skF_6'
    | ~ r1_tarski(k3_xboole_0('#skF_6','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_12943,c_28])).

tff(c_12977,plain,(
    k3_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12940,c_12967])).

tff(c_13401,plain,(
    ! [A_1860,B_1861,B_1862] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_1860,B_1861),B_1862),B_1861)
      | r1_tarski(k3_xboole_0(A_1860,B_1861),B_1862) ) ),
    inference(resolution,[status(thm)],[c_8,c_3819])).

tff(c_13467,plain,(
    ! [A_1863,B_1864] : r1_tarski(k3_xboole_0(A_1863,B_1864),B_1864) ),
    inference(resolution,[status(thm)],[c_13401,c_6])).

tff(c_13499,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12977,c_13467])).

tff(c_13532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3818,c_13499])).

tff(c_13534,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9863])).

tff(c_13552,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13534,c_3817])).

tff(c_13571,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13552,c_60])).

tff(c_13572,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13552,c_13552,c_44])).

tff(c_13617,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13572,c_9697])).

tff(c_13619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13571,c_13617])).

tff(c_13620,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3812])).

tff(c_13646,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13620,c_62])).

tff(c_14220,plain,(
    ! [A_1903,B_1904,C_1905] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1903,B_1904),k2_zfmisc_1(A_1903,C_1905))
      | r1_tarski(B_1904,C_1905)
      | k1_xboole_0 = A_1903 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14254,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13646,c_14220])).

tff(c_14285,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3568,c_14254])).

tff(c_14314,plain,(
    ! [B_23] : k2_zfmisc_1('#skF_4',B_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14285,c_14285,c_46])).

tff(c_14312,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14285,c_60])).

tff(c_14418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14314,c_14312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/2.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.94  
% 8.87/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.94  %$ r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 8.87/2.94  
% 8.87/2.94  %Foreground sorts:
% 8.87/2.94  
% 8.87/2.94  
% 8.87/2.94  %Background operators:
% 8.87/2.94  
% 8.87/2.94  
% 8.87/2.94  %Foreground operators:
% 8.87/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.87/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.87/2.94  tff('#skF_7', type, '#skF_7': $i).
% 8.87/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.87/2.94  tff('#skF_5', type, '#skF_5': $i).
% 8.87/2.94  tff('#skF_6', type, '#skF_6': $i).
% 8.87/2.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.87/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/2.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.87/2.94  tff('#skF_4', type, '#skF_4': $i).
% 8.87/2.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.87/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.87/2.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.87/2.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.87/2.94  
% 8.87/2.97  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 8.87/2.97  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.87/2.97  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.87/2.97  tff(f_86, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 8.87/2.97  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.87/2.97  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.87/2.97  tff(f_78, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 8.87/2.97  tff(f_67, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.87/2.97  tff(f_84, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 8.87/2.97  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.87/2.97  tff(c_60, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.87/2.97  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.87/2.97  tff(c_58, plain, (~r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.87/2.97  tff(c_128, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 8.87/2.97  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.87/2.97  tff(c_1709, plain, (![A_139, C_140, B_141, D_142]: (k3_xboole_0(k2_zfmisc_1(A_139, C_140), k2_zfmisc_1(B_141, D_142))=k2_zfmisc_1(k3_xboole_0(A_139, B_141), k3_xboole_0(C_140, D_142)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.87/2.97  tff(c_62, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.87/2.97  tff(c_232, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.87/2.97  tff(c_242, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_232])).
% 8.87/2.97  tff(c_1724, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1709, c_242])).
% 8.87/2.97  tff(c_243, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_232])).
% 8.87/2.97  tff(c_56, plain, (![A_30, C_32, B_31, D_33]: (k3_xboole_0(k2_zfmisc_1(A_30, C_32), k2_zfmisc_1(B_31, D_33))=k2_zfmisc_1(k3_xboole_0(A_30, B_31), k3_xboole_0(C_32, D_33)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.87/2.97  tff(c_364, plain, (![D_64, A_65, B_66]: (r2_hidden(D_64, A_65) | ~r2_hidden(D_64, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.87/2.97  tff(c_2279, plain, (![A_168, B_169, B_170]: (r2_hidden('#skF_1'(k3_xboole_0(A_168, B_169), B_170), A_168) | r1_tarski(k3_xboole_0(A_168, B_169), B_170))), inference(resolution, [status(thm)], [c_8, c_364])).
% 8.87/2.97  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.87/2.97  tff(c_2342, plain, (![A_171, B_172]: (r1_tarski(k3_xboole_0(A_171, B_172), A_171))), inference(resolution, [status(thm)], [c_2279, c_6])).
% 8.87/2.97  tff(c_2834, plain, (![A_190, B_191, C_192, D_193]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_190, B_191), k3_xboole_0(C_192, D_193)), k2_zfmisc_1(A_190, C_192)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2342])).
% 8.87/2.97  tff(c_2930, plain, (![B_194, C_195, D_196]: (r1_tarski(k2_zfmisc_1(B_194, k3_xboole_0(C_195, D_196)), k2_zfmisc_1(B_194, C_195)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_2834])).
% 8.87/2.97  tff(c_2957, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1724, c_2930])).
% 8.87/2.97  tff(c_50, plain, (![B_25, A_24, C_26]: (~r1_tarski(k2_zfmisc_1(B_25, A_24), k2_zfmisc_1(C_26, A_24)) | r1_tarski(B_25, C_26) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_3130, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2957, c_50])).
% 8.87/2.97  tff(c_3136, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3130])).
% 8.87/2.97  tff(c_44, plain, (![A_22]: (k2_zfmisc_1(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.87/2.97  tff(c_461, plain, (![C_77, A_78, B_79]: (r1_tarski(k2_zfmisc_1(C_77, A_78), k2_zfmisc_1(C_77, B_79)) | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.87/2.97  tff(c_475, plain, (![A_22, A_78]: (r1_tarski(k2_zfmisc_1(A_22, A_78), k1_xboole_0) | ~r1_tarski(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_461])).
% 8.87/2.97  tff(c_386, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.87/2.97  tff(c_913, plain, (![A_100, B_101, B_102]: (r2_hidden('#skF_1'(A_100, B_101), B_102) | ~r1_tarski(A_100, B_102) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_8, c_386])).
% 8.87/2.97  tff(c_40, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.87/2.97  tff(c_244, plain, (![A_21]: (k3_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_232])).
% 8.87/2.97  tff(c_332, plain, (![D_55, B_56, A_57]: (r2_hidden(D_55, B_56) | ~r2_hidden(D_55, k3_xboole_0(A_57, B_56)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.87/2.97  tff(c_338, plain, (![D_55, A_21]: (r2_hidden(D_55, A_21) | ~r2_hidden(D_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_332])).
% 8.87/2.97  tff(c_936, plain, (![A_103, B_104, A_105]: (r2_hidden('#skF_1'(A_103, B_104), A_105) | ~r1_tarski(A_103, k1_xboole_0) | r1_tarski(A_103, B_104))), inference(resolution, [status(thm)], [c_913, c_338])).
% 8.87/2.97  tff(c_959, plain, (![A_106, A_107]: (~r1_tarski(A_106, k1_xboole_0) | r1_tarski(A_106, A_107))), inference(resolution, [status(thm)], [c_936, c_6])).
% 8.87/2.97  tff(c_970, plain, (![A_22, A_78, A_107]: (r1_tarski(k2_zfmisc_1(A_22, A_78), A_107) | ~r1_tarski(A_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_475, c_959])).
% 8.87/2.97  tff(c_1833, plain, (![A_107]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), A_107) | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1724, c_970])).
% 8.87/2.97  tff(c_1894, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1833])).
% 8.87/2.97  tff(c_1437, plain, (![A_128, B_129, C_130]: (~r1_tarski(k2_zfmisc_1(A_128, B_129), k2_zfmisc_1(A_128, C_130)) | r1_tarski(B_129, C_130) | k1_xboole_0=A_128)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_1482, plain, (![A_22, B_129]: (~r1_tarski(k2_zfmisc_1(A_22, B_129), k1_xboole_0) | r1_tarski(B_129, k1_xboole_0) | k1_xboole_0=A_22)), inference(superposition, [status(thm), theory('equality')], [c_44, c_1437])).
% 8.87/2.97  tff(c_1803, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1724, c_1482])).
% 8.87/2.97  tff(c_2682, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1894, c_1803])).
% 8.87/2.97  tff(c_2683, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2682])).
% 8.87/2.97  tff(c_2691, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_970, c_2683])).
% 8.87/2.97  tff(c_3137, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3136, c_2691])).
% 8.87/2.97  tff(c_3178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3137])).
% 8.87/2.97  tff(c_3179, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_3130])).
% 8.87/2.97  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.87/2.97  tff(c_2398, plain, (![A_171, B_172]: (k3_xboole_0(A_171, B_172)=A_171 | ~r1_tarski(A_171, k3_xboole_0(A_171, B_172)))), inference(resolution, [status(thm)], [c_2342, c_28])).
% 8.87/2.97  tff(c_3214, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_3179, c_2398])).
% 8.87/2.97  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.87/2.97  tff(c_3286, plain, (![D_203]: (r2_hidden(D_203, '#skF_6') | ~r2_hidden(D_203, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3214, c_12])).
% 8.87/2.97  tff(c_3433, plain, (![A_207]: (r1_tarski(A_207, '#skF_6') | ~r2_hidden('#skF_1'(A_207, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_3286, c_6])).
% 8.87/2.97  tff(c_3445, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_8, c_3433])).
% 8.87/2.97  tff(c_3451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_128, c_3445])).
% 8.87/2.97  tff(c_3452, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2682])).
% 8.87/2.97  tff(c_46, plain, (![B_23]: (k2_zfmisc_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.87/2.97  tff(c_390, plain, (![A_70, C_71, B_72]: (r1_tarski(k2_zfmisc_1(A_70, C_71), k2_zfmisc_1(B_72, C_71)) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.87/2.97  tff(c_410, plain, (![A_70, B_23]: (r1_tarski(k2_zfmisc_1(A_70, B_23), k1_xboole_0) | ~r1_tarski(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_390])).
% 8.87/2.97  tff(c_971, plain, (![A_70, B_23, A_107]: (r1_tarski(k2_zfmisc_1(A_70, B_23), A_107) | ~r1_tarski(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_410, c_959])).
% 8.87/2.97  tff(c_1824, plain, (![A_107]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), A_107) | ~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1724, c_971])).
% 8.87/2.97  tff(c_1893, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1824])).
% 8.87/2.97  tff(c_3455, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3452, c_1893])).
% 8.87/2.97  tff(c_3460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3455])).
% 8.87/2.97  tff(c_3464, plain, (![A_208]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), A_208))), inference(splitRight, [status(thm)], [c_1833])).
% 8.87/2.97  tff(c_306, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.87/2.97  tff(c_318, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_306])).
% 8.87/2.97  tff(c_3493, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3464, c_318])).
% 8.87/2.97  tff(c_3513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3493])).
% 8.87/2.97  tff(c_3518, plain, (![A_209]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), A_209))), inference(splitRight, [status(thm)], [c_1824])).
% 8.87/2.97  tff(c_3547, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3518, c_318])).
% 8.87/2.97  tff(c_3567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3547])).
% 8.87/2.97  tff(c_3568, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 8.87/2.97  tff(c_3569, plain, (r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 8.87/2.97  tff(c_3802, plain, (![B_230, A_231]: (B_230=A_231 | ~r1_tarski(B_230, A_231) | ~r1_tarski(A_231, B_230))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.87/2.97  tff(c_3812, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_3569, c_3802])).
% 8.87/2.97  tff(c_3818, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_3812])).
% 8.87/2.97  tff(c_3570, plain, (![A_210, B_211]: (k3_xboole_0(A_210, B_211)=A_210 | ~r1_tarski(A_210, B_211))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.87/2.97  tff(c_3580, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_3569, c_3570])).
% 8.87/2.97  tff(c_5110, plain, (![A_308, C_309, B_310, D_311]: (k3_xboole_0(k2_zfmisc_1(A_308, C_309), k2_zfmisc_1(B_310, D_311))=k2_zfmisc_1(k3_xboole_0(A_308, B_310), k3_xboole_0(C_309, D_311)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.87/2.97  tff(c_36, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.87/2.97  tff(c_3590, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_36])).
% 8.87/2.97  tff(c_5125, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5110, c_3590])).
% 8.87/2.97  tff(c_5177, plain, (k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3580, c_5125])).
% 8.87/2.97  tff(c_3581, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_3570])).
% 8.87/2.97  tff(c_3819, plain, (![D_232, B_233, A_234]: (r2_hidden(D_232, B_233) | ~r2_hidden(D_232, k3_xboole_0(A_234, B_233)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.87/2.97  tff(c_7062, plain, (![A_393, B_394, B_395]: (r2_hidden('#skF_1'(k3_xboole_0(A_393, B_394), B_395), B_394) | r1_tarski(k3_xboole_0(A_393, B_394), B_395))), inference(resolution, [status(thm)], [c_8, c_3819])).
% 8.87/2.97  tff(c_7151, plain, (![A_396, B_397]: (r1_tarski(k3_xboole_0(A_396, B_397), B_397))), inference(resolution, [status(thm)], [c_7062, c_6])).
% 8.87/2.97  tff(c_8753, plain, (![A_430, B_431, C_432, D_433]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_430, B_431), k3_xboole_0(C_432, D_433)), k2_zfmisc_1(B_431, D_433)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_7151])).
% 8.87/2.97  tff(c_9102, plain, (![B_437, C_438, D_439]: (r1_tarski(k2_zfmisc_1(B_437, k3_xboole_0(C_438, D_439)), k2_zfmisc_1(B_437, D_439)))), inference(superposition, [status(thm), theory('equality')], [c_3581, c_8753])).
% 8.87/2.97  tff(c_9157, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5177, c_9102])).
% 8.87/2.97  tff(c_48, plain, (![A_24, B_25, C_26]: (~r1_tarski(k2_zfmisc_1(A_24, B_25), k2_zfmisc_1(A_24, C_26)) | r1_tarski(B_25, C_26) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_9226, plain, (r1_tarski('#skF_5', '#skF_7') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_9157, c_48])).
% 8.87/2.97  tff(c_9237, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3568, c_9226])).
% 8.87/2.97  tff(c_3907, plain, (![A_246, C_247, B_248]: (r1_tarski(k2_zfmisc_1(A_246, C_247), k2_zfmisc_1(B_248, C_247)) | ~r1_tarski(A_246, B_248))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.87/2.97  tff(c_3927, plain, (![A_246, B_23]: (r1_tarski(k2_zfmisc_1(A_246, B_23), k1_xboole_0) | ~r1_tarski(A_246, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3907])).
% 8.87/2.97  tff(c_3879, plain, (![C_243, A_244, B_245]: (r1_tarski(k2_zfmisc_1(C_243, A_244), k2_zfmisc_1(C_243, B_245)) | ~r1_tarski(A_244, B_245))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.87/2.97  tff(c_3893, plain, (![A_22, A_244]: (r1_tarski(k2_zfmisc_1(A_22, A_244), k1_xboole_0) | ~r1_tarski(A_244, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_3879])).
% 8.87/2.97  tff(c_3935, plain, (![A_249, A_250]: (r1_tarski(k2_zfmisc_1(A_249, A_250), k1_xboole_0) | ~r1_tarski(A_250, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_3879])).
% 8.87/2.97  tff(c_3817, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_3802])).
% 8.87/2.97  tff(c_3964, plain, (![A_251, A_252]: (k2_zfmisc_1(A_251, A_252)=k1_xboole_0 | ~r1_tarski(A_252, k1_xboole_0))), inference(resolution, [status(thm)], [c_3935, c_3817])).
% 8.87/2.97  tff(c_3973, plain, (![A_251, A_22, A_244]: (k2_zfmisc_1(A_251, k2_zfmisc_1(A_22, A_244))=k1_xboole_0 | ~r1_tarski(A_244, k1_xboole_0))), inference(resolution, [status(thm)], [c_3893, c_3964])).
% 8.87/2.97  tff(c_4473, plain, (![A_279, B_280, C_281]: (~r1_tarski(k2_zfmisc_1(A_279, B_280), k2_zfmisc_1(A_279, C_281)) | r1_tarski(B_280, C_281) | k1_xboole_0=A_279)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_4482, plain, (![A_251, C_281, A_22, A_244]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_251, C_281)) | r1_tarski(k2_zfmisc_1(A_22, A_244), C_281) | k1_xboole_0=A_251 | ~r1_tarski(A_244, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3973, c_4473])).
% 8.87/2.97  tff(c_4524, plain, (![A_22, A_244, C_281, A_251]: (r1_tarski(k2_zfmisc_1(A_22, A_244), C_281) | k1_xboole_0=A_251 | ~r1_tarski(A_244, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4482])).
% 8.87/2.97  tff(c_4631, plain, (![A_288, A_289, C_290]: (r1_tarski(k2_zfmisc_1(A_288, A_289), C_290) | ~r1_tarski(A_289, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_4524])).
% 8.87/2.97  tff(c_4694, plain, (![A_289, C_26, A_288]: (r1_tarski(A_289, C_26) | k1_xboole_0=A_288 | ~r1_tarski(A_289, k1_xboole_0))), inference(resolution, [status(thm)], [c_4631, c_48])).
% 8.87/2.97  tff(c_4786, plain, (![A_294, C_295]: (r1_tarski(A_294, C_295) | ~r1_tarski(A_294, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_4694])).
% 8.87/2.97  tff(c_4799, plain, (![A_246, B_23, C_295]: (r1_tarski(k2_zfmisc_1(A_246, B_23), C_295) | ~r1_tarski(A_246, k1_xboole_0))), inference(resolution, [status(thm)], [c_3927, c_4786])).
% 8.87/2.97  tff(c_4711, plain, (![B_291, A_292, C_293]: (~r1_tarski(k2_zfmisc_1(B_291, A_292), k2_zfmisc_1(C_293, A_292)) | r1_tarski(B_291, C_293) | k1_xboole_0=A_292)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_5516, plain, (![B_323, B_324]: (~r1_tarski(k2_zfmisc_1(B_323, B_324), k1_xboole_0) | r1_tarski(B_323, k1_xboole_0) | k1_xboole_0=B_324)), inference(superposition, [status(thm), theory('equality')], [c_46, c_4711])).
% 8.87/2.97  tff(c_5519, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0) | r1_tarski('#skF_4', k1_xboole_0) | k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5177, c_5516])).
% 8.87/2.97  tff(c_8744, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5519])).
% 8.87/2.97  tff(c_8751, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4799, c_8744])).
% 8.87/2.97  tff(c_9241, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9237, c_8751])).
% 8.87/2.97  tff(c_9281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_9241])).
% 8.87/2.97  tff(c_9283, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_5519])).
% 8.87/2.97  tff(c_9350, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_9283, c_3817])).
% 8.87/2.97  tff(c_9367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_9350])).
% 8.87/2.97  tff(c_9369, plain, (![A_441]: (k1_xboole_0=A_441)), inference(splitRight, [status(thm)], [c_4694])).
% 8.87/2.97  tff(c_3811, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5') | ~r1_tarski(k2_zfmisc_1('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_3802])).
% 8.87/2.97  tff(c_3859, plain, (~r1_tarski(k2_zfmisc_1('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_3811])).
% 8.87/2.97  tff(c_9424, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9369, c_3859])).
% 8.87/2.97  tff(c_9526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_9424])).
% 8.87/2.97  tff(c_9528, plain, (![A_1099]: (k1_xboole_0=A_1099)), inference(splitRight, [status(thm)], [c_4524])).
% 8.87/2.97  tff(c_9594, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9528, c_3859])).
% 8.87/2.97  tff(c_9696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_9594])).
% 8.87/2.97  tff(c_9697, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_3811])).
% 8.87/2.97  tff(c_9732, plain, (![A_1722, C_1723, B_1724]: (r1_tarski(k2_zfmisc_1(A_1722, C_1723), k2_zfmisc_1(B_1724, C_1723)) | ~r1_tarski(A_1722, B_1724))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.87/2.97  tff(c_9746, plain, (![A_1722]: (r1_tarski(k2_zfmisc_1(A_1722, '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_1722, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9697, c_9732])).
% 8.87/2.97  tff(c_10435, plain, (![A_1758, B_1759, C_1760]: (~r1_tarski(k2_zfmisc_1(A_1758, B_1759), k2_zfmisc_1(A_1758, C_1760)) | r1_tarski(B_1759, C_1760) | k1_xboole_0=A_1758)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_10439, plain, (r1_tarski('#skF_7', '#skF_5') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_9746, c_10435])).
% 8.87/2.97  tff(c_10499, plain, (r1_tarski('#skF_7', '#skF_5') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3569, c_10439])).
% 8.87/2.97  tff(c_10524, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_10499])).
% 8.87/2.97  tff(c_10545, plain, (![B_23]: (k2_zfmisc_1('#skF_4', B_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10524, c_10524, c_46])).
% 8.87/2.97  tff(c_10543, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10524, c_60])).
% 8.87/2.97  tff(c_10571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10545, c_10543])).
% 8.87/2.97  tff(c_10572, plain, (r1_tarski('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_10499])).
% 8.87/2.97  tff(c_10584, plain, (k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_10572, c_36])).
% 8.87/2.97  tff(c_9813, plain, (![C_1729, A_1730, B_1731]: (r1_tarski(k2_zfmisc_1(C_1729, A_1730), k2_zfmisc_1(C_1729, B_1731)) | ~r1_tarski(A_1730, B_1731))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.87/2.97  tff(c_10369, plain, (![A_1754]: (r1_tarski(k2_zfmisc_1('#skF_6', A_1754), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_1754, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_9697, c_9813])).
% 8.87/2.97  tff(c_10396, plain, (![A_1754]: (k3_xboole_0(k2_zfmisc_1('#skF_6', A_1754), k2_zfmisc_1('#skF_4', '#skF_5'))=k2_zfmisc_1('#skF_6', A_1754) | ~r1_tarski(A_1754, '#skF_7'))), inference(resolution, [status(thm)], [c_10369, c_36])).
% 8.87/2.97  tff(c_12756, plain, (![A_1847]: (k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_4'), k3_xboole_0(A_1847, '#skF_5'))=k2_zfmisc_1('#skF_6', A_1847) | ~r1_tarski(A_1847, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10396])).
% 8.87/2.97  tff(c_12834, plain, (k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_4'), '#skF_7')=k2_zfmisc_1('#skF_6', '#skF_7') | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10584, c_12756])).
% 8.87/2.97  tff(c_12848, plain, (k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_4'), '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9697, c_12834])).
% 8.87/2.97  tff(c_10601, plain, (![B_1762, A_1763, C_1764]: (~r1_tarski(k2_zfmisc_1(B_1762, A_1763), k2_zfmisc_1(C_1764, A_1763)) | r1_tarski(B_1762, C_1764) | k1_xboole_0=A_1763)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_10646, plain, (![B_1762]: (~r1_tarski(k2_zfmisc_1(B_1762, '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_1762, '#skF_6') | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9697, c_10601])).
% 8.87/2.97  tff(c_10873, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_10646])).
% 8.87/2.97  tff(c_9847, plain, (![A_1732, A_1733]: (r1_tarski(k2_zfmisc_1(A_1732, A_1733), k1_xboole_0) | ~r1_tarski(A_1733, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_9813])).
% 8.87/2.97  tff(c_9863, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0) | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9697, c_9847])).
% 8.87/2.97  tff(c_9899, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_9863])).
% 8.87/2.97  tff(c_10883, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10873, c_9899])).
% 8.87/2.97  tff(c_10901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_10883])).
% 8.87/2.97  tff(c_10902, plain, (![B_1762]: (~r1_tarski(k2_zfmisc_1(B_1762, '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_1762, '#skF_6'))), inference(splitRight, [status(thm)], [c_10646])).
% 8.87/2.97  tff(c_12875, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(k3_xboole_0('#skF_6', '#skF_4'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12848, c_10902])).
% 8.87/2.97  tff(c_12940, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12875])).
% 8.87/2.97  tff(c_10903, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_10646])).
% 8.87/2.97  tff(c_10643, plain, (![C_1764]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(C_1764, '#skF_7')) | r1_tarski('#skF_6', C_1764) | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9697, c_10601])).
% 8.87/2.97  tff(c_10986, plain, (![C_1764]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(C_1764, '#skF_7')) | r1_tarski('#skF_6', C_1764))), inference(negUnitSimplification, [status(thm)], [c_10903, c_10643])).
% 8.87/2.97  tff(c_12881, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski('#skF_6', k3_xboole_0('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12848, c_10986])).
% 8.87/2.97  tff(c_12943, plain, (r1_tarski('#skF_6', k3_xboole_0('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12881])).
% 8.87/2.97  tff(c_12967, plain, (k3_xboole_0('#skF_6', '#skF_4')='#skF_6' | ~r1_tarski(k3_xboole_0('#skF_6', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_12943, c_28])).
% 8.87/2.97  tff(c_12977, plain, (k3_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12940, c_12967])).
% 8.87/2.97  tff(c_13401, plain, (![A_1860, B_1861, B_1862]: (r2_hidden('#skF_1'(k3_xboole_0(A_1860, B_1861), B_1862), B_1861) | r1_tarski(k3_xboole_0(A_1860, B_1861), B_1862))), inference(resolution, [status(thm)], [c_8, c_3819])).
% 8.87/2.97  tff(c_13467, plain, (![A_1863, B_1864]: (r1_tarski(k3_xboole_0(A_1863, B_1864), B_1864))), inference(resolution, [status(thm)], [c_13401, c_6])).
% 8.87/2.97  tff(c_13499, plain, (r1_tarski('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12977, c_13467])).
% 8.87/2.97  tff(c_13532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3818, c_13499])).
% 8.87/2.97  tff(c_13534, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_9863])).
% 8.87/2.97  tff(c_13552, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_13534, c_3817])).
% 8.87/2.97  tff(c_13571, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13552, c_60])).
% 8.87/2.97  tff(c_13572, plain, (![A_22]: (k2_zfmisc_1(A_22, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13552, c_13552, c_44])).
% 8.87/2.97  tff(c_13617, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13572, c_9697])).
% 8.87/2.97  tff(c_13619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13571, c_13617])).
% 8.87/2.97  tff(c_13620, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_3812])).
% 8.87/2.97  tff(c_13646, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_13620, c_62])).
% 8.87/2.97  tff(c_14220, plain, (![A_1903, B_1904, C_1905]: (~r1_tarski(k2_zfmisc_1(A_1903, B_1904), k2_zfmisc_1(A_1903, C_1905)) | r1_tarski(B_1904, C_1905) | k1_xboole_0=A_1903)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.87/2.97  tff(c_14254, plain, (r1_tarski('#skF_5', '#skF_7') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_13646, c_14220])).
% 8.87/2.97  tff(c_14285, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3568, c_14254])).
% 8.87/2.97  tff(c_14314, plain, (![B_23]: (k2_zfmisc_1('#skF_4', B_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14285, c_14285, c_46])).
% 8.87/2.97  tff(c_14312, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14285, c_60])).
% 8.87/2.97  tff(c_14418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14314, c_14312])).
% 8.87/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.97  
% 8.87/2.97  Inference rules
% 8.87/2.97  ----------------------
% 8.87/2.97  #Ref     : 0
% 8.87/2.97  #Sup     : 3471
% 8.87/2.97  #Fact    : 0
% 8.87/2.97  #Define  : 0
% 8.87/2.97  #Split   : 22
% 8.87/2.97  #Chain   : 0
% 8.87/2.97  #Close   : 0
% 8.87/2.97  
% 8.87/2.97  Ordering : KBO
% 8.87/2.97  
% 8.87/2.97  Simplification rules
% 8.87/2.97  ----------------------
% 8.87/2.97  #Subsume      : 679
% 8.87/2.97  #Demod        : 2016
% 8.87/2.97  #Tautology    : 1561
% 8.87/2.97  #SimpNegUnit  : 42
% 8.87/2.97  #BackRed      : 217
% 8.87/2.97  
% 8.87/2.97  #Partial instantiations: 356
% 8.87/2.97  #Strategies tried      : 1
% 8.87/2.97  
% 8.87/2.97  Timing (in seconds)
% 8.87/2.97  ----------------------
% 8.87/2.97  Preprocessing        : 0.34
% 8.87/2.97  Parsing              : 0.18
% 8.87/2.97  CNF conversion       : 0.02
% 8.87/2.97  Main loop            : 1.81
% 8.87/2.97  Inferencing          : 0.57
% 8.87/2.97  Reduction            : 0.59
% 8.87/2.97  Demodulation         : 0.43
% 8.87/2.97  BG Simplification    : 0.06
% 8.87/2.97  Subsumption          : 0.45
% 8.87/2.97  Abstraction          : 0.08
% 8.87/2.97  MUC search           : 0.00
% 8.87/2.97  Cooper               : 0.00
% 8.87/2.98  Total                : 2.21
% 8.87/2.98  Index Insertion      : 0.00
% 8.87/2.98  Index Deletion       : 0.00
% 8.87/2.98  Index Matching       : 0.00
% 8.87/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
