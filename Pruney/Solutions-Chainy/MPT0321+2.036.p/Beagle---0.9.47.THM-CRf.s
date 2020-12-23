%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:18 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 316 expanded)
%              Number of leaves         :   25 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 750 expanded)
%              Number of equality atoms :   42 ( 311 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(c_50,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_59,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_110,plain,(
    ! [C_47,A_48,B_49] :
      ( r1_tarski(k2_zfmisc_1(C_47,A_48),k2_zfmisc_1(C_47,B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_118,plain,(
    ! [A_48] :
      ( r1_tarski(k2_zfmisc_1('#skF_6',A_48),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_48,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_110])).

tff(c_337,plain,(
    ! [B_87,A_88,C_89] :
      ( ~ r1_tarski(k2_zfmisc_1(B_87,A_88),k2_zfmisc_1(C_89,A_88))
      | r1_tarski(B_87,C_89)
      | k1_xboole_0 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_345,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_118,c_337])).

tff(c_368,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_345])).

tff(c_1868,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2612,plain,(
    ! [A_251,B_252,C_253,D_254] :
      ( r2_hidden(k4_tarski(A_251,B_252),k2_zfmisc_1(C_253,D_254))
      | ~ r2_hidden(B_252,D_254)
      | ~ r2_hidden(A_251,C_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [B_36,D_37,A_38,C_39] :
      ( r2_hidden(B_36,D_37)
      | ~ r2_hidden(k4_tarski(A_38,B_36),k2_zfmisc_1(C_39,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95,plain,(
    ! [B_36,A_38] :
      ( r2_hidden(B_36,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_38,B_36),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_92])).

tff(c_2632,plain,(
    ! [B_252,A_251] :
      ( r2_hidden(B_252,'#skF_7')
      | ~ r2_hidden(B_252,'#skF_5')
      | ~ r2_hidden(A_251,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2612,c_95])).

tff(c_2638,plain,(
    ! [A_255] : ~ r2_hidden(A_255,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2632])).

tff(c_2662,plain,(
    ! [B_256] : r1_tarski('#skF_4',B_256) ),
    inference(resolution,[status(thm)],[c_6,c_2638])).

tff(c_34,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_120,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden(A_50,B_51)
      | ~ r2_hidden(A_50,C_52)
      | r2_hidden(A_50,k5_xboole_0(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_53,A_54] :
      ( r2_hidden(A_53,A_54)
      | ~ r2_hidden(A_53,k1_xboole_0)
      | r2_hidden(A_53,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_120])).

tff(c_137,plain,(
    ! [B_55,A_56] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_55),A_56)
      | r1_tarski(k1_xboole_0,B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [A_57] : r1_tarski(k1_xboole_0,A_57) ),
    inference(resolution,[status(thm)],[c_137,c_4])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_154,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ r1_tarski(A_57,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_151,c_28])).

tff(c_2669,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2662,c_154])).

tff(c_2677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2669])).

tff(c_2699,plain,(
    ! [B_259] :
      ( r2_hidden(B_259,'#skF_7')
      | ~ r2_hidden(B_259,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2632])).

tff(c_2717,plain,(
    ! [A_260] :
      ( r1_tarski(A_260,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_260,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2699,c_4])).

tff(c_2725,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_2717])).

tff(c_2730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1868,c_1868,c_2725])).

tff(c_2731,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_376,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_646,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r2_hidden(k4_tarski(A_105,B_106),k2_zfmisc_1(C_107,D_108))
      | ~ r2_hidden(B_106,D_108)
      | ~ r2_hidden(A_105,C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_666,plain,(
    ! [B_106,A_105] :
      ( r2_hidden(B_106,'#skF_7')
      | ~ r2_hidden(B_106,'#skF_5')
      | ~ r2_hidden(A_105,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_646,c_95])).

tff(c_672,plain,(
    ! [A_109] : ~ r2_hidden(A_109,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_666])).

tff(c_694,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_672])).

tff(c_115,plain,(
    ! [B_49] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6',B_49))
      | ~ r1_tarski('#skF_7',B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_110])).

tff(c_341,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_115,c_337])).

tff(c_365,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_341])).

tff(c_375,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_96,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(k2_zfmisc_1(A_40,C_41),k2_zfmisc_1(B_42,C_41))
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_104,plain,(
    ! [A_40] :
      ( r1_tarski(k2_zfmisc_1(A_40,'#skF_7'),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_40,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_96])).

tff(c_465,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_tarski(k2_zfmisc_1(A_96,B_97),k2_zfmisc_1(A_96,C_98))
      | r1_tarski(B_97,C_98)
      | k1_xboole_0 = A_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_473,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_465])).

tff(c_496,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_375,c_473])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_496])).

tff(c_719,plain,(
    ! [B_112] :
      ( r2_hidden(B_112,'#skF_7')
      | ~ r2_hidden(B_112,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_666])).

tff(c_737,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_113,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_719,c_4])).

tff(c_745,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_737])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_376,c_745])).

tff(c_751,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_754,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_751,c_28])).

tff(c_757,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_754])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),B_10)
      | r2_hidden('#skF_3'(A_9,B_10),A_9)
      | B_10 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_854,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_2'(A_121,B_122),B_122)
      | r2_hidden('#skF_3'(A_121,B_122),A_121)
      | B_122 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_219,plain,(
    ! [A_70,C_71,B_72] :
      ( ~ r2_hidden(A_70,C_71)
      | ~ r2_hidden(A_70,B_72)
      | ~ r2_hidden(A_70,k5_xboole_0(B_72,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_229,plain,(
    ! [A_70,A_14] :
      ( ~ r2_hidden(A_70,k1_xboole_0)
      | ~ r2_hidden(A_70,A_14)
      | ~ r2_hidden(A_70,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_219])).

tff(c_1625,plain,(
    ! [B_174,A_175] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_174),A_175)
      | r2_hidden('#skF_2'(k1_xboole_0,B_174),B_174)
      | k1_xboole_0 = B_174 ) ),
    inference(resolution,[status(thm)],[c_854,c_229])).

tff(c_1638,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_10),B_10)
      | k1_xboole_0 = B_10 ) ),
    inference(resolution,[status(thm)],[c_26,c_1625])).

tff(c_1642,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( r2_hidden(k4_tarski(A_176,B_177),k2_zfmisc_1(C_178,D_179))
      | ~ r2_hidden(B_177,D_179)
      | ~ r2_hidden(A_176,C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    ! [A_43,C_44,B_45,D_46] :
      ( r2_hidden(A_43,C_44)
      | ~ r2_hidden(k4_tarski(A_43,B_45),k2_zfmisc_1(C_44,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [A_43,B_45] :
      ( r2_hidden(A_43,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_43,B_45),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_106])).

tff(c_1663,plain,(
    ! [A_176,B_177] :
      ( r2_hidden(A_176,'#skF_6')
      | ~ r2_hidden(B_177,'#skF_5')
      | ~ r2_hidden(A_176,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1642,c_109])).

tff(c_1806,plain,(
    ! [B_192] : ~ r2_hidden(B_192,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1663])).

tff(c_1810,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1638,c_1806])).

tff(c_1832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1810])).

tff(c_1834,plain,(
    ! [A_193] :
      ( r2_hidden(A_193,'#skF_6')
      | ~ r2_hidden(A_193,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1663])).

tff(c_1852,plain,(
    ! [A_194] :
      ( r1_tarski(A_194,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_194,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1834,c_4])).

tff(c_1860,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_1852])).

tff(c_1865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_757,c_757,c_1860])).

tff(c_1866,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_2742,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1866,c_28])).

tff(c_2745,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_2742])).

tff(c_2747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_2745])).

tff(c_2748,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_32,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2749,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2763,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_56])).

tff(c_2791,plain,(
    ! [A_275,C_276,B_277] :
      ( r1_tarski(k2_zfmisc_1(A_275,C_276),k2_zfmisc_1(B_277,C_276))
      | ~ r1_tarski(A_275,B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2796,plain,(
    ! [B_277] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_277,'#skF_7'))
      | ~ r1_tarski('#skF_4',B_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_2791])).

tff(c_3137,plain,(
    ! [A_329,B_330,C_331] :
      ( ~ r1_tarski(k2_zfmisc_1(A_329,B_330),k2_zfmisc_1(A_329,C_331))
      | r1_tarski(B_330,C_331)
      | k1_xboole_0 = A_329 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3144,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2796,c_3137])).

tff(c_3174,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3144])).

tff(c_3175,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3174])).

tff(c_2799,plain,(
    ! [A_275] :
      ( r1_tarski(k2_zfmisc_1(A_275,'#skF_7'),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_275,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_2791])).

tff(c_3151,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2799,c_3137])).

tff(c_3181,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3151])).

tff(c_3182,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3181])).

tff(c_3197,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_3182,c_28])).

tff(c_3200,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_3197])).

tff(c_3202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2748,c_3200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.81  
% 4.43/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.81  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 4.55/1.81  
% 4.55/1.81  %Foreground sorts:
% 4.55/1.81  
% 4.55/1.81  
% 4.55/1.81  %Background operators:
% 4.55/1.81  
% 4.55/1.81  
% 4.55/1.81  %Foreground operators:
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.55/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.55/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.55/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.55/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.55/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.55/1.81  
% 4.63/1.84  tff(f_88, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 4.63/1.84  tff(f_77, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 4.63/1.84  tff(f_71, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 4.63/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.63/1.84  tff(f_60, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.63/1.84  tff(f_54, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.63/1.84  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.63/1.84  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.63/1.84  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 4.63/1.84  tff(c_50, plain, ('#skF_7'!='#skF_5' | '#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.63/1.84  tff(c_59, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 4.63/1.84  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.63/1.84  tff(c_56, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.63/1.84  tff(c_110, plain, (![C_47, A_48, B_49]: (r1_tarski(k2_zfmisc_1(C_47, A_48), k2_zfmisc_1(C_47, B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.84  tff(c_118, plain, (![A_48]: (r1_tarski(k2_zfmisc_1('#skF_6', A_48), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_48, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_110])).
% 4.63/1.84  tff(c_337, plain, (![B_87, A_88, C_89]: (~r1_tarski(k2_zfmisc_1(B_87, A_88), k2_zfmisc_1(C_89, A_88)) | r1_tarski(B_87, C_89) | k1_xboole_0=A_88)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_345, plain, (r1_tarski('#skF_6', '#skF_4') | k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_118, c_337])).
% 4.63/1.84  tff(c_368, plain, (r1_tarski('#skF_6', '#skF_4') | ~r1_tarski('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_52, c_345])).
% 4.63/1.84  tff(c_1868, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_368])).
% 4.63/1.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.84  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.63/1.84  tff(c_2612, plain, (![A_251, B_252, C_253, D_254]: (r2_hidden(k4_tarski(A_251, B_252), k2_zfmisc_1(C_253, D_254)) | ~r2_hidden(B_252, D_254) | ~r2_hidden(A_251, C_253))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.84  tff(c_92, plain, (![B_36, D_37, A_38, C_39]: (r2_hidden(B_36, D_37) | ~r2_hidden(k4_tarski(A_38, B_36), k2_zfmisc_1(C_39, D_37)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.84  tff(c_95, plain, (![B_36, A_38]: (r2_hidden(B_36, '#skF_7') | ~r2_hidden(k4_tarski(A_38, B_36), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_92])).
% 4.63/1.84  tff(c_2632, plain, (![B_252, A_251]: (r2_hidden(B_252, '#skF_7') | ~r2_hidden(B_252, '#skF_5') | ~r2_hidden(A_251, '#skF_4'))), inference(resolution, [status(thm)], [c_2612, c_95])).
% 4.63/1.84  tff(c_2638, plain, (![A_255]: (~r2_hidden(A_255, '#skF_4'))), inference(splitLeft, [status(thm)], [c_2632])).
% 4.63/1.84  tff(c_2662, plain, (![B_256]: (r1_tarski('#skF_4', B_256))), inference(resolution, [status(thm)], [c_6, c_2638])).
% 4.63/1.84  tff(c_34, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.84  tff(c_120, plain, (![A_50, B_51, C_52]: (r2_hidden(A_50, B_51) | ~r2_hidden(A_50, C_52) | r2_hidden(A_50, k5_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.84  tff(c_132, plain, (![A_53, A_54]: (r2_hidden(A_53, A_54) | ~r2_hidden(A_53, k1_xboole_0) | r2_hidden(A_53, A_54))), inference(superposition, [status(thm), theory('equality')], [c_34, c_120])).
% 4.63/1.84  tff(c_137, plain, (![B_55, A_56]: (r2_hidden('#skF_1'(k1_xboole_0, B_55), A_56) | r1_tarski(k1_xboole_0, B_55))), inference(resolution, [status(thm)], [c_6, c_132])).
% 4.63/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.84  tff(c_151, plain, (![A_57]: (r1_tarski(k1_xboole_0, A_57))), inference(resolution, [status(thm)], [c_137, c_4])).
% 4.63/1.84  tff(c_28, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.84  tff(c_154, plain, (![A_57]: (k1_xboole_0=A_57 | ~r1_tarski(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_151, c_28])).
% 4.63/1.84  tff(c_2669, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2662, c_154])).
% 4.63/1.84  tff(c_2677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2669])).
% 4.63/1.84  tff(c_2699, plain, (![B_259]: (r2_hidden(B_259, '#skF_7') | ~r2_hidden(B_259, '#skF_5'))), inference(splitRight, [status(thm)], [c_2632])).
% 4.63/1.84  tff(c_2717, plain, (![A_260]: (r1_tarski(A_260, '#skF_7') | ~r2_hidden('#skF_1'(A_260, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_2699, c_4])).
% 4.63/1.84  tff(c_2725, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_2717])).
% 4.63/1.84  tff(c_2730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1868, c_1868, c_2725])).
% 4.63/1.84  tff(c_2731, plain, (r1_tarski('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_368])).
% 4.63/1.84  tff(c_376, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_368])).
% 4.63/1.84  tff(c_646, plain, (![A_105, B_106, C_107, D_108]: (r2_hidden(k4_tarski(A_105, B_106), k2_zfmisc_1(C_107, D_108)) | ~r2_hidden(B_106, D_108) | ~r2_hidden(A_105, C_107))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.84  tff(c_666, plain, (![B_106, A_105]: (r2_hidden(B_106, '#skF_7') | ~r2_hidden(B_106, '#skF_5') | ~r2_hidden(A_105, '#skF_4'))), inference(resolution, [status(thm)], [c_646, c_95])).
% 4.63/1.84  tff(c_672, plain, (![A_109]: (~r2_hidden(A_109, '#skF_4'))), inference(splitLeft, [status(thm)], [c_666])).
% 4.63/1.84  tff(c_694, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_672])).
% 4.63/1.84  tff(c_115, plain, (![B_49]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', B_49)) | ~r1_tarski('#skF_7', B_49))), inference(superposition, [status(thm), theory('equality')], [c_56, c_110])).
% 4.63/1.84  tff(c_341, plain, (r1_tarski('#skF_4', '#skF_6') | k1_xboole_0='#skF_5' | ~r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_115, c_337])).
% 4.63/1.84  tff(c_365, plain, (r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_341])).
% 4.63/1.84  tff(c_375, plain, (~r1_tarski('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_365])).
% 4.63/1.84  tff(c_96, plain, (![A_40, C_41, B_42]: (r1_tarski(k2_zfmisc_1(A_40, C_41), k2_zfmisc_1(B_42, C_41)) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.84  tff(c_104, plain, (![A_40]: (r1_tarski(k2_zfmisc_1(A_40, '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_40, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_96])).
% 4.63/1.84  tff(c_465, plain, (![A_96, B_97, C_98]: (~r1_tarski(k2_zfmisc_1(A_96, B_97), k2_zfmisc_1(A_96, C_98)) | r1_tarski(B_97, C_98) | k1_xboole_0=A_96)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_473, plain, (r1_tarski('#skF_7', '#skF_5') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_104, c_465])).
% 4.63/1.84  tff(c_496, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_375, c_473])).
% 4.63/1.84  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_694, c_496])).
% 4.63/1.84  tff(c_719, plain, (![B_112]: (r2_hidden(B_112, '#skF_7') | ~r2_hidden(B_112, '#skF_5'))), inference(splitRight, [status(thm)], [c_666])).
% 4.63/1.84  tff(c_737, plain, (![A_113]: (r1_tarski(A_113, '#skF_7') | ~r2_hidden('#skF_1'(A_113, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_719, c_4])).
% 4.63/1.84  tff(c_745, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_737])).
% 4.63/1.84  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_376, c_745])).
% 4.63/1.84  tff(c_751, plain, (r1_tarski('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_368])).
% 4.63/1.84  tff(c_754, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_751, c_28])).
% 4.63/1.84  tff(c_757, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_59, c_754])).
% 4.63/1.84  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), B_10) | r2_hidden('#skF_3'(A_9, B_10), A_9) | B_10=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.63/1.84  tff(c_854, plain, (![A_121, B_122]: (r2_hidden('#skF_2'(A_121, B_122), B_122) | r2_hidden('#skF_3'(A_121, B_122), A_121) | B_122=A_121)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.63/1.84  tff(c_219, plain, (![A_70, C_71, B_72]: (~r2_hidden(A_70, C_71) | ~r2_hidden(A_70, B_72) | ~r2_hidden(A_70, k5_xboole_0(B_72, C_71)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.84  tff(c_229, plain, (![A_70, A_14]: (~r2_hidden(A_70, k1_xboole_0) | ~r2_hidden(A_70, A_14) | ~r2_hidden(A_70, A_14))), inference(superposition, [status(thm), theory('equality')], [c_34, c_219])).
% 4.63/1.84  tff(c_1625, plain, (![B_174, A_175]: (~r2_hidden('#skF_3'(k1_xboole_0, B_174), A_175) | r2_hidden('#skF_2'(k1_xboole_0, B_174), B_174) | k1_xboole_0=B_174)), inference(resolution, [status(thm)], [c_854, c_229])).
% 4.63/1.84  tff(c_1638, plain, (![B_10]: (r2_hidden('#skF_2'(k1_xboole_0, B_10), B_10) | k1_xboole_0=B_10)), inference(resolution, [status(thm)], [c_26, c_1625])).
% 4.63/1.84  tff(c_1642, plain, (![A_176, B_177, C_178, D_179]: (r2_hidden(k4_tarski(A_176, B_177), k2_zfmisc_1(C_178, D_179)) | ~r2_hidden(B_177, D_179) | ~r2_hidden(A_176, C_178))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.84  tff(c_106, plain, (![A_43, C_44, B_45, D_46]: (r2_hidden(A_43, C_44) | ~r2_hidden(k4_tarski(A_43, B_45), k2_zfmisc_1(C_44, D_46)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.84  tff(c_109, plain, (![A_43, B_45]: (r2_hidden(A_43, '#skF_6') | ~r2_hidden(k4_tarski(A_43, B_45), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_106])).
% 4.63/1.84  tff(c_1663, plain, (![A_176, B_177]: (r2_hidden(A_176, '#skF_6') | ~r2_hidden(B_177, '#skF_5') | ~r2_hidden(A_176, '#skF_4'))), inference(resolution, [status(thm)], [c_1642, c_109])).
% 4.63/1.84  tff(c_1806, plain, (![B_192]: (~r2_hidden(B_192, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1663])).
% 4.63/1.84  tff(c_1810, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1638, c_1806])).
% 4.63/1.84  tff(c_1832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1810])).
% 4.63/1.84  tff(c_1834, plain, (![A_193]: (r2_hidden(A_193, '#skF_6') | ~r2_hidden(A_193, '#skF_4'))), inference(splitRight, [status(thm)], [c_1663])).
% 4.63/1.84  tff(c_1852, plain, (![A_194]: (r1_tarski(A_194, '#skF_6') | ~r2_hidden('#skF_1'(A_194, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_1834, c_4])).
% 4.63/1.84  tff(c_1860, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_1852])).
% 4.63/1.84  tff(c_1865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_757, c_757, c_1860])).
% 4.63/1.84  tff(c_1866, plain, (r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_365])).
% 4.63/1.84  tff(c_2742, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1866, c_28])).
% 4.63/1.84  tff(c_2745, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_2742])).
% 4.63/1.84  tff(c_2747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_2745])).
% 4.63/1.84  tff(c_2748, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 4.63/1.84  tff(c_32, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.84  tff(c_2749, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 4.63/1.84  tff(c_2763, plain, (k2_zfmisc_1('#skF_4', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2749, c_56])).
% 4.63/1.84  tff(c_2791, plain, (![A_275, C_276, B_277]: (r1_tarski(k2_zfmisc_1(A_275, C_276), k2_zfmisc_1(B_277, C_276)) | ~r1_tarski(A_275, B_277))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.84  tff(c_2796, plain, (![B_277]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_277, '#skF_7')) | ~r1_tarski('#skF_4', B_277))), inference(superposition, [status(thm), theory('equality')], [c_2763, c_2791])).
% 4.63/1.84  tff(c_3137, plain, (![A_329, B_330, C_331]: (~r1_tarski(k2_zfmisc_1(A_329, B_330), k2_zfmisc_1(A_329, C_331)) | r1_tarski(B_330, C_331) | k1_xboole_0=A_329)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_3144, plain, (r1_tarski('#skF_5', '#skF_7') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2796, c_3137])).
% 4.63/1.84  tff(c_3174, plain, (r1_tarski('#skF_5', '#skF_7') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3144])).
% 4.63/1.84  tff(c_3175, plain, (r1_tarski('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_3174])).
% 4.63/1.84  tff(c_2799, plain, (![A_275]: (r1_tarski(k2_zfmisc_1(A_275, '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_275, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2763, c_2791])).
% 4.63/1.84  tff(c_3151, plain, (r1_tarski('#skF_7', '#skF_5') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2799, c_3137])).
% 4.63/1.84  tff(c_3181, plain, (r1_tarski('#skF_7', '#skF_5') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3151])).
% 4.63/1.84  tff(c_3182, plain, (r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_3181])).
% 4.63/1.84  tff(c_3197, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_3182, c_28])).
% 4.63/1.84  tff(c_3200, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_3197])).
% 4.63/1.84  tff(c_3202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2748, c_3200])).
% 4.63/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.84  
% 4.63/1.84  Inference rules
% 4.63/1.84  ----------------------
% 4.63/1.84  #Ref     : 0
% 4.63/1.84  #Sup     : 613
% 4.63/1.84  #Fact    : 0
% 4.63/1.84  #Define  : 0
% 4.63/1.84  #Split   : 20
% 4.63/1.84  #Chain   : 0
% 4.63/1.84  #Close   : 0
% 4.63/1.84  
% 4.63/1.84  Ordering : KBO
% 4.63/1.84  
% 4.63/1.84  Simplification rules
% 4.63/1.84  ----------------------
% 4.63/1.84  #Subsume      : 84
% 4.63/1.84  #Demod        : 287
% 4.63/1.84  #Tautology    : 231
% 4.63/1.84  #SimpNegUnit  : 56
% 4.63/1.84  #BackRed      : 101
% 4.63/1.84  
% 4.63/1.84  #Partial instantiations: 0
% 4.63/1.84  #Strategies tried      : 1
% 4.63/1.84  
% 4.63/1.84  Timing (in seconds)
% 4.63/1.84  ----------------------
% 4.63/1.85  Preprocessing        : 0.31
% 4.63/1.85  Parsing              : 0.16
% 4.63/1.85  CNF conversion       : 0.02
% 4.63/1.85  Main loop            : 0.72
% 4.63/1.85  Inferencing          : 0.26
% 4.63/1.85  Reduction            : 0.20
% 4.63/1.85  Demodulation         : 0.13
% 4.63/1.85  BG Simplification    : 0.03
% 4.63/1.85  Subsumption          : 0.16
% 4.63/1.85  Abstraction          : 0.03
% 4.63/1.85  MUC search           : 0.00
% 4.63/1.85  Cooper               : 0.00
% 4.63/1.85  Total                : 1.09
% 4.63/1.85  Index Insertion      : 0.00
% 4.63/1.85  Index Deletion       : 0.00
% 4.63/1.85  Index Matching       : 0.00
% 4.63/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
