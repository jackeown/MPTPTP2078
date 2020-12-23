%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 11.02s
% Output     : CNFRefutation 11.16s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 135 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 210 expanded)
%              Number of equality atoms :   31 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_149,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_139,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_3693,plain,(
    ! [A_251,B_252] :
      ( r1_tarski(A_251,B_252)
      | k4_xboole_0(A_251,B_252) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_146,plain,(
    ! [A_71,B_72] :
      ( r1_xboole_0(A_71,B_72)
      | k3_xboole_0(A_71,B_72) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_485,plain,(
    ! [B_91,A_92] :
      ( r1_xboole_0(B_91,A_92)
      | k3_xboole_0(A_92,B_91) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_146,c_12])).

tff(c_62,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_95,plain,(
    ~ r1_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_499,plain,(
    k3_xboole_0(k3_subset_1('#skF_6','#skF_8'),'#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_485,c_95])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3545,plain,(
    ! [A_242,B_243] :
      ( k4_xboole_0(A_242,B_243) = k3_subset_1(A_242,B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3552,plain,(
    k4_xboole_0('#skF_6','#skF_8') = k3_subset_1('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_3545])).

tff(c_32,plain,(
    ! [A_27,B_28] : r1_tarski(k4_xboole_0(A_27,B_28),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_105,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = k1_xboole_0
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110,plain,(
    ! [A_68,B_69] : k4_xboole_0(k4_xboole_0(A_68,B_69),A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_38,plain,(
    ! [A_30,B_31] : r1_xboole_0(k4_xboole_0(A_30,B_31),B_31) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,(
    ! [B_58,A_59] :
      ( r1_xboole_0(B_58,A_59)
      | ~ r1_xboole_0(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [B_31,A_30] : r1_xboole_0(B_31,k4_xboole_0(A_30,B_31)) ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_121,plain,(
    ! [A_68] : r1_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_82])).

tff(c_68,plain,
    ( r1_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_8'))
    | r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_182,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_68])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_189,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_26])).

tff(c_2780,plain,(
    ! [B_220,A_221,C_222] :
      ( r1_xboole_0(B_220,k4_xboole_0(A_221,C_222))
      | ~ r1_xboole_0(A_221,k4_xboole_0(B_220,C_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2810,plain,(
    ! [A_221] :
      ( r1_xboole_0('#skF_7',k4_xboole_0(A_221,'#skF_8'))
      | ~ r1_xboole_0(A_221,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2780])).

tff(c_2851,plain,(
    ! [A_223] : r1_xboole_0('#skF_7',k4_xboole_0(A_223,'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_2810])).

tff(c_1228,plain,(
    ! [A_154,B_155] :
      ( k4_xboole_0(k2_xboole_0(A_154,B_155),B_155) = A_154
      | ~ r1_xboole_0(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_260,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = k1_xboole_0
      | ~ r1_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_279,plain,(
    ! [B_31,A_30] : k3_xboole_0(B_31,k4_xboole_0(A_30,B_31)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_260])).

tff(c_1249,plain,(
    ! [B_155,A_154] :
      ( k3_xboole_0(B_155,A_154) = k1_xboole_0
      | ~ r1_xboole_0(A_154,B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_279])).

tff(c_2891,plain,(
    ! [A_223] : k3_xboole_0(k4_xboole_0(A_223,'#skF_8'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2851,c_1249])).

tff(c_3571,plain,(
    k3_xboole_0(k3_subset_1('#skF_6','#skF_8'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3552,c_2891])).

tff(c_3631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_3571])).

tff(c_3632,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3704,plain,(
    k4_xboole_0('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3693,c_3632])).

tff(c_3633,plain,(
    r1_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6639,plain,(
    ! [A_426,B_427] :
      ( k4_xboole_0(A_426,B_427) = k3_subset_1(A_426,B_427)
      | ~ m1_subset_1(B_427,k1_zfmisc_1(A_426)) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6646,plain,(
    k4_xboole_0('#skF_6','#skF_8') = k3_subset_1('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_6639])).

tff(c_40,plain,(
    ! [B_33,A_32,C_34] :
      ( r1_xboole_0(B_33,k4_xboole_0(A_32,C_34))
      | ~ r1_xboole_0(A_32,k4_xboole_0(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_35236,plain,(
    ! [A_857] :
      ( r1_xboole_0('#skF_6',k4_xboole_0(A_857,'#skF_8'))
      | ~ r1_xboole_0(A_857,k3_subset_1('#skF_6','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6646,c_40])).

tff(c_35404,plain,(
    r1_xboole_0('#skF_6',k4_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3633,c_35236])).

tff(c_35433,plain,(
    r1_xboole_0(k4_xboole_0('#skF_7','#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_35404,c_12])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5147,plain,(
    ! [C_358,A_359,B_360] :
      ( r2_hidden(C_358,A_359)
      | ~ r2_hidden(C_358,B_360)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(A_359)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_10838,plain,(
    ! [A_537,B_538,A_539] :
      ( r2_hidden('#skF_1'(A_537,B_538),A_539)
      | ~ m1_subset_1(A_537,k1_zfmisc_1(A_539))
      | r1_tarski(A_537,B_538) ) ),
    inference(resolution,[status(thm)],[c_6,c_5147])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10890,plain,(
    ! [A_540,A_541] :
      ( ~ m1_subset_1(A_540,k1_zfmisc_1(A_541))
      | r1_tarski(A_540,A_541) ) ),
    inference(resolution,[status(thm)],[c_10838,c_4])).

tff(c_10898,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_10890])).

tff(c_4726,plain,(
    ! [A_336,B_337] :
      ( k4_xboole_0(k2_xboole_0(A_336,B_337),B_337) = A_336
      | ~ r1_xboole_0(A_336,B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    ! [A_35,C_37,B_36] :
      ( r1_xboole_0(A_35,k4_xboole_0(C_37,B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4741,plain,(
    ! [A_35,A_336,B_337] :
      ( r1_xboole_0(A_35,A_336)
      | ~ r1_tarski(A_35,B_337)
      | ~ r1_xboole_0(A_336,B_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4726,c_42])).

tff(c_10929,plain,(
    ! [A_336] :
      ( r1_xboole_0('#skF_7',A_336)
      | ~ r1_xboole_0(A_336,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10898,c_4741])).

tff(c_35482,plain,(
    r1_xboole_0('#skF_7',k4_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_35433,c_10929])).

tff(c_35518,plain,(
    r1_xboole_0(k4_xboole_0('#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_35482,c_12])).

tff(c_3986,plain,(
    ! [A_276,B_277] :
      ( ~ r2_hidden('#skF_1'(A_276,B_277),B_277)
      | r1_tarski(A_276,B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3993,plain,(
    ! [A_278] : r1_tarski(A_278,A_278) ),
    inference(resolution,[status(thm)],[c_6,c_3986])).

tff(c_4000,plain,(
    ! [A_278] : k4_xboole_0(A_278,A_278) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3993,c_26])).

tff(c_90,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(A_62,B_63) = B_63
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_94,plain,(
    ! [A_27,B_28] : k2_xboole_0(k4_xboole_0(A_27,B_28),A_27) = A_27 ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_4774,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k4_xboole_0(A_27,A_27)
      | ~ r1_xboole_0(k4_xboole_0(A_27,B_28),A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4726])).

tff(c_4780,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(A_27,B_28),A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4000,c_4774])).

tff(c_35525,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35518,c_4780])).

tff(c_35546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3704,c_35525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.02/5.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.02/5.29  
% 11.02/5.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.02/5.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 11.02/5.30  
% 11.02/5.30  %Foreground sorts:
% 11.02/5.30  
% 11.02/5.30  
% 11.02/5.30  %Background operators:
% 11.02/5.30  
% 11.02/5.30  
% 11.02/5.30  %Foreground operators:
% 11.02/5.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.02/5.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.02/5.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.02/5.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.02/5.30  tff('#skF_7', type, '#skF_7': $i).
% 11.02/5.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.02/5.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.02/5.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.02/5.30  tff('#skF_6', type, '#skF_6': $i).
% 11.02/5.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.02/5.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.02/5.30  tff('#skF_8', type, '#skF_8': $i).
% 11.02/5.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.02/5.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.02/5.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.02/5.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.02/5.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.02/5.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.02/5.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.02/5.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.02/5.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.02/5.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.02/5.30  
% 11.16/5.31  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.16/5.31  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.16/5.31  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.16/5.31  tff(f_149, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 11.16/5.31  tff(f_132, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.16/5.31  tff(f_88, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.16/5.31  tff(f_102, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.16/5.31  tff(f_106, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.16/5.31  tff(f_114, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 11.16/5.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.16/5.31  tff(f_139, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 11.16/5.31  tff(f_110, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 11.16/5.31  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.16/5.31  tff(c_3693, plain, (![A_251, B_252]: (r1_tarski(A_251, B_252) | k4_xboole_0(A_251, B_252)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.16/5.31  tff(c_146, plain, (![A_71, B_72]: (r1_xboole_0(A_71, B_72) | k3_xboole_0(A_71, B_72)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.16/5.31  tff(c_12, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.16/5.31  tff(c_485, plain, (![B_91, A_92]: (r1_xboole_0(B_91, A_92) | k3_xboole_0(A_92, B_91)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_146, c_12])).
% 11.16/5.31  tff(c_62, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.16/5.31  tff(c_95, plain, (~r1_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_62])).
% 11.16/5.31  tff(c_499, plain, (k3_xboole_0(k3_subset_1('#skF_6', '#skF_8'), '#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_485, c_95])).
% 11.16/5.31  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.16/5.31  tff(c_3545, plain, (![A_242, B_243]: (k4_xboole_0(A_242, B_243)=k3_subset_1(A_242, B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.16/5.31  tff(c_3552, plain, (k4_xboole_0('#skF_6', '#skF_8')=k3_subset_1('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_58, c_3545])).
% 11.16/5.31  tff(c_32, plain, (![A_27, B_28]: (r1_tarski(k4_xboole_0(A_27, B_28), A_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.16/5.31  tff(c_105, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=k1_xboole_0 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.16/5.31  tff(c_110, plain, (![A_68, B_69]: (k4_xboole_0(k4_xboole_0(A_68, B_69), A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_105])).
% 11.16/5.31  tff(c_38, plain, (![A_30, B_31]: (r1_xboole_0(k4_xboole_0(A_30, B_31), B_31))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.16/5.31  tff(c_77, plain, (![B_58, A_59]: (r1_xboole_0(B_58, A_59) | ~r1_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.16/5.31  tff(c_82, plain, (![B_31, A_30]: (r1_xboole_0(B_31, k4_xboole_0(A_30, B_31)))), inference(resolution, [status(thm)], [c_38, c_77])).
% 11.16/5.31  tff(c_121, plain, (![A_68]: (r1_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_82])).
% 11.16/5.31  tff(c_68, plain, (r1_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_8')) | r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.16/5.31  tff(c_182, plain, (r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_95, c_68])).
% 11.16/5.31  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.16/5.31  tff(c_189, plain, (k4_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_26])).
% 11.16/5.31  tff(c_2780, plain, (![B_220, A_221, C_222]: (r1_xboole_0(B_220, k4_xboole_0(A_221, C_222)) | ~r1_xboole_0(A_221, k4_xboole_0(B_220, C_222)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.16/5.31  tff(c_2810, plain, (![A_221]: (r1_xboole_0('#skF_7', k4_xboole_0(A_221, '#skF_8')) | ~r1_xboole_0(A_221, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_189, c_2780])).
% 11.16/5.31  tff(c_2851, plain, (![A_223]: (r1_xboole_0('#skF_7', k4_xboole_0(A_223, '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_2810])).
% 11.16/5.31  tff(c_1228, plain, (![A_154, B_155]: (k4_xboole_0(k2_xboole_0(A_154, B_155), B_155)=A_154 | ~r1_xboole_0(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.16/5.31  tff(c_260, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=k1_xboole_0 | ~r1_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.16/5.31  tff(c_279, plain, (![B_31, A_30]: (k3_xboole_0(B_31, k4_xboole_0(A_30, B_31))=k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_260])).
% 11.16/5.31  tff(c_1249, plain, (![B_155, A_154]: (k3_xboole_0(B_155, A_154)=k1_xboole_0 | ~r1_xboole_0(A_154, B_155))), inference(superposition, [status(thm), theory('equality')], [c_1228, c_279])).
% 11.16/5.31  tff(c_2891, plain, (![A_223]: (k3_xboole_0(k4_xboole_0(A_223, '#skF_8'), '#skF_7')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2851, c_1249])).
% 11.16/5.31  tff(c_3571, plain, (k3_xboole_0(k3_subset_1('#skF_6', '#skF_8'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3552, c_2891])).
% 11.16/5.31  tff(c_3631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_3571])).
% 11.16/5.31  tff(c_3632, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_62])).
% 11.16/5.31  tff(c_3704, plain, (k4_xboole_0('#skF_7', '#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3693, c_3632])).
% 11.16/5.31  tff(c_3633, plain, (r1_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_62])).
% 11.16/5.31  tff(c_6639, plain, (![A_426, B_427]: (k4_xboole_0(A_426, B_427)=k3_subset_1(A_426, B_427) | ~m1_subset_1(B_427, k1_zfmisc_1(A_426)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.16/5.31  tff(c_6646, plain, (k4_xboole_0('#skF_6', '#skF_8')=k3_subset_1('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_58, c_6639])).
% 11.16/5.31  tff(c_40, plain, (![B_33, A_32, C_34]: (r1_xboole_0(B_33, k4_xboole_0(A_32, C_34)) | ~r1_xboole_0(A_32, k4_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.16/5.31  tff(c_35236, plain, (![A_857]: (r1_xboole_0('#skF_6', k4_xboole_0(A_857, '#skF_8')) | ~r1_xboole_0(A_857, k3_subset_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_6646, c_40])).
% 11.16/5.31  tff(c_35404, plain, (r1_xboole_0('#skF_6', k4_xboole_0('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_3633, c_35236])).
% 11.16/5.31  tff(c_35433, plain, (r1_xboole_0(k4_xboole_0('#skF_7', '#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_35404, c_12])).
% 11.16/5.31  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.16/5.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.16/5.31  tff(c_5147, plain, (![C_358, A_359, B_360]: (r2_hidden(C_358, A_359) | ~r2_hidden(C_358, B_360) | ~m1_subset_1(B_360, k1_zfmisc_1(A_359)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.16/5.31  tff(c_10838, plain, (![A_537, B_538, A_539]: (r2_hidden('#skF_1'(A_537, B_538), A_539) | ~m1_subset_1(A_537, k1_zfmisc_1(A_539)) | r1_tarski(A_537, B_538))), inference(resolution, [status(thm)], [c_6, c_5147])).
% 11.16/5.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.16/5.31  tff(c_10890, plain, (![A_540, A_541]: (~m1_subset_1(A_540, k1_zfmisc_1(A_541)) | r1_tarski(A_540, A_541))), inference(resolution, [status(thm)], [c_10838, c_4])).
% 11.16/5.31  tff(c_10898, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_10890])).
% 11.16/5.31  tff(c_4726, plain, (![A_336, B_337]: (k4_xboole_0(k2_xboole_0(A_336, B_337), B_337)=A_336 | ~r1_xboole_0(A_336, B_337))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.16/5.31  tff(c_42, plain, (![A_35, C_37, B_36]: (r1_xboole_0(A_35, k4_xboole_0(C_37, B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.16/5.31  tff(c_4741, plain, (![A_35, A_336, B_337]: (r1_xboole_0(A_35, A_336) | ~r1_tarski(A_35, B_337) | ~r1_xboole_0(A_336, B_337))), inference(superposition, [status(thm), theory('equality')], [c_4726, c_42])).
% 11.16/5.31  tff(c_10929, plain, (![A_336]: (r1_xboole_0('#skF_7', A_336) | ~r1_xboole_0(A_336, '#skF_6'))), inference(resolution, [status(thm)], [c_10898, c_4741])).
% 11.16/5.31  tff(c_35482, plain, (r1_xboole_0('#skF_7', k4_xboole_0('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_35433, c_10929])).
% 11.16/5.31  tff(c_35518, plain, (r1_xboole_0(k4_xboole_0('#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_35482, c_12])).
% 11.16/5.31  tff(c_3986, plain, (![A_276, B_277]: (~r2_hidden('#skF_1'(A_276, B_277), B_277) | r1_tarski(A_276, B_277))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.16/5.31  tff(c_3993, plain, (![A_278]: (r1_tarski(A_278, A_278))), inference(resolution, [status(thm)], [c_6, c_3986])).
% 11.16/5.31  tff(c_4000, plain, (![A_278]: (k4_xboole_0(A_278, A_278)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3993, c_26])).
% 11.16/5.31  tff(c_90, plain, (![A_62, B_63]: (k2_xboole_0(A_62, B_63)=B_63 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.16/5.31  tff(c_94, plain, (![A_27, B_28]: (k2_xboole_0(k4_xboole_0(A_27, B_28), A_27)=A_27)), inference(resolution, [status(thm)], [c_32, c_90])).
% 11.16/5.31  tff(c_4774, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k4_xboole_0(A_27, A_27) | ~r1_xboole_0(k4_xboole_0(A_27, B_28), A_27))), inference(superposition, [status(thm), theory('equality')], [c_94, c_4726])).
% 11.16/5.31  tff(c_4780, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(A_27, B_28), A_27))), inference(demodulation, [status(thm), theory('equality')], [c_4000, c_4774])).
% 11.16/5.31  tff(c_35525, plain, (k4_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_35518, c_4780])).
% 11.16/5.31  tff(c_35546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3704, c_35525])).
% 11.16/5.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.16/5.31  
% 11.16/5.31  Inference rules
% 11.16/5.31  ----------------------
% 11.16/5.31  #Ref     : 0
% 11.16/5.31  #Sup     : 8496
% 11.16/5.31  #Fact    : 0
% 11.16/5.31  #Define  : 0
% 11.16/5.31  #Split   : 9
% 11.16/5.31  #Chain   : 0
% 11.16/5.31  #Close   : 0
% 11.16/5.31  
% 11.16/5.31  Ordering : KBO
% 11.16/5.31  
% 11.16/5.31  Simplification rules
% 11.16/5.31  ----------------------
% 11.16/5.31  #Subsume      : 1556
% 11.16/5.31  #Demod        : 6149
% 11.16/5.31  #Tautology    : 5138
% 11.16/5.31  #SimpNegUnit  : 106
% 11.16/5.31  #BackRed      : 8
% 11.16/5.31  
% 11.16/5.31  #Partial instantiations: 0
% 11.16/5.31  #Strategies tried      : 1
% 11.16/5.31  
% 11.16/5.31  Timing (in seconds)
% 11.16/5.31  ----------------------
% 11.16/5.32  Preprocessing        : 0.34
% 11.16/5.32  Parsing              : 0.19
% 11.16/5.32  CNF conversion       : 0.02
% 11.16/5.32  Main loop            : 4.22
% 11.16/5.32  Inferencing          : 0.86
% 11.16/5.32  Reduction            : 1.91
% 11.16/5.32  Demodulation         : 1.48
% 11.16/5.32  BG Simplification    : 0.07
% 11.16/5.32  Subsumption          : 1.14
% 11.16/5.32  Abstraction          : 0.12
% 11.16/5.32  MUC search           : 0.00
% 11.16/5.32  Cooper               : 0.00
% 11.16/5.32  Total                : 4.59
% 11.16/5.32  Index Insertion      : 0.00
% 11.16/5.32  Index Deletion       : 0.00
% 11.16/5.32  Index Matching       : 0.00
% 11.16/5.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
