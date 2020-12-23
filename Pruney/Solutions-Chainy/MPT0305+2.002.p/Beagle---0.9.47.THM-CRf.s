%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:51 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 752 expanded)
%              Number of leaves         :   17 ( 236 expanded)
%              Depth                    :   14
%              Number of atoms          :  297 (1754 expanded)
%              Number of equality atoms :   27 ( 264 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
            | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
          & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1031,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( r2_hidden(k4_tarski(A_169,B_170),k2_zfmisc_1(C_171,D_172))
      | ~ r2_hidden(B_170,D_172)
      | ~ r2_hidden(A_169,C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1051,plain,(
    ! [A_178,B_179,A_180] :
      ( r2_hidden(k4_tarski(A_178,B_179),k1_xboole_0)
      | ~ r2_hidden(B_179,k1_xboole_0)
      | ~ r2_hidden(A_178,A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1031])).

tff(c_1665,plain,(
    ! [A_261,B_262,B_263] :
      ( r2_hidden(k4_tarski('#skF_1'(A_261,B_262),B_263),k1_xboole_0)
      | ~ r2_hidden(B_263,k1_xboole_0)
      | r1_tarski(A_261,B_262) ) ),
    inference(resolution,[status(thm)],[c_6,c_1051])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1024,plain,(
    ! [B_165,D_166,A_167,C_168] :
      ( r2_hidden(B_165,D_166)
      | ~ r2_hidden(k4_tarski(A_167,B_165),k2_zfmisc_1(C_168,D_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1030,plain,(
    ! [B_165,B_13,A_167] :
      ( r2_hidden(B_165,B_13)
      | ~ r2_hidden(k4_tarski(A_167,B_165),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1024])).

tff(c_1678,plain,(
    ! [B_263,B_13,A_261,B_262] :
      ( r2_hidden(B_263,B_13)
      | ~ r2_hidden(B_263,k1_xboole_0)
      | r1_tarski(A_261,B_262) ) ),
    inference(resolution,[status(thm)],[c_1665,c_1030])).

tff(c_1681,plain,(
    ! [A_261,B_262] : r1_tarski(A_261,B_262) ),
    inference(splitLeft,[status(thm)],[c_1678])).

tff(c_1417,plain,(
    ! [A_233,B_234,B_235] :
      ( r2_hidden(k4_tarski('#skF_1'(A_233,B_234),B_235),k1_xboole_0)
      | ~ r2_hidden(B_235,k1_xboole_0)
      | r1_tarski(A_233,B_234) ) ),
    inference(resolution,[status(thm)],[c_6,c_1051])).

tff(c_1430,plain,(
    ! [B_235,B_13,A_233,B_234] :
      ( r2_hidden(B_235,B_13)
      | ~ r2_hidden(B_235,k1_xboole_0)
      | r1_tarski(A_233,B_234) ) ),
    inference(resolution,[status(thm)],[c_1417,c_1030])).

tff(c_1433,plain,(
    ! [A_233,B_234] : r1_tarski(A_233,B_234) ),
    inference(splitLeft,[status(thm)],[c_1430])).

tff(c_364,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( r2_hidden(k4_tarski(A_82,B_83),k2_zfmisc_1(C_84,D_85))
      | ~ r2_hidden(B_83,D_85)
      | ~ r2_hidden(A_82,C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_591,plain,(
    ! [A_114,B_115,B_116] :
      ( r2_hidden(k4_tarski(A_114,B_115),k1_xboole_0)
      | ~ r2_hidden(B_115,B_116)
      | ~ r2_hidden(A_114,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_364])).

tff(c_734,plain,(
    ! [A_134,A_135,B_136] :
      ( r2_hidden(k4_tarski(A_134,'#skF_1'(A_135,B_136)),k1_xboole_0)
      | ~ r2_hidden(A_134,k1_xboole_0)
      | r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_6,c_591])).

tff(c_89,plain,(
    ! [A_28,C_29,B_30,D_31] :
      ( r2_hidden(A_28,C_29)
      | ~ r2_hidden(k4_tarski(A_28,B_30),k2_zfmisc_1(C_29,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_28,A_12,B_30] :
      ( r2_hidden(A_28,A_12)
      | ~ r2_hidden(k4_tarski(A_28,B_30),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_89])).

tff(c_748,plain,(
    ! [A_134,A_12,A_135,B_136] :
      ( r2_hidden(A_134,A_12)
      | ~ r2_hidden(A_134,k1_xboole_0)
      | r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_734,c_92])).

tff(c_750,plain,(
    ! [A_135,B_136] : r1_tarski(A_135,B_136) ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_390,plain,(
    ! [A_86,B_87,A_88] :
      ( r2_hidden(k4_tarski(A_86,B_87),k1_xboole_0)
      | ~ r2_hidden(B_87,k1_xboole_0)
      | ~ r2_hidden(A_86,A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_364])).

tff(c_450,plain,(
    ! [A_97,B_98,B_99] :
      ( r2_hidden(k4_tarski('#skF_1'(A_97,B_98),B_99),k1_xboole_0)
      | ~ r2_hidden(B_99,k1_xboole_0)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_390])).

tff(c_97,plain,(
    ! [B_35,D_36,A_37,C_38] :
      ( r2_hidden(B_35,D_36)
      | ~ r2_hidden(k4_tarski(A_37,B_35),k2_zfmisc_1(C_38,D_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_103,plain,(
    ! [B_35,B_13,A_37] :
      ( r2_hidden(B_35,B_13)
      | ~ r2_hidden(k4_tarski(A_37,B_35),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_463,plain,(
    ! [B_99,B_13,A_97,B_98] :
      ( r2_hidden(B_99,B_13)
      | ~ r2_hidden(B_99,k1_xboole_0)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_450,c_103])).

tff(c_466,plain,(
    ! [A_97,B_98] : r1_tarski(A_97,B_98) ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_26])).

tff(c_499,plain,(
    ! [B_105,B_106] :
      ( r2_hidden(B_105,B_106)
      | ~ r2_hidden(B_105,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_511,plain,(
    ! [B_107,B_108] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_107),B_108)
      | r1_tarski(k1_xboole_0,B_107) ) ),
    inference(resolution,[status(thm)],[c_6,c_499])).

tff(c_28,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_116,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( r2_hidden(k4_tarski(A_47,B_48),k2_zfmisc_1(C_49,D_50))
      | ~ r2_hidden(B_48,D_50)
      | ~ r2_hidden(A_47,C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [B_63,B_62,A_60,D_61,C_64] :
      ( r2_hidden(k4_tarski(A_60,B_62),B_63)
      | ~ r1_tarski(k2_zfmisc_1(C_64,D_61),B_63)
      | ~ r2_hidden(B_62,D_61)
      | ~ r2_hidden(A_60,C_64) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_214,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(k4_tarski(A_67,B_68),k2_zfmisc_1('#skF_4','#skF_2'))
      | ~ r2_hidden(B_68,'#skF_2')
      | ~ r2_hidden(A_67,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_81,c_170])).

tff(c_18,plain,(
    ! [A_8,C_10,B_9,D_11] :
      ( r2_hidden(A_8,C_10)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_230,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(A_67,'#skF_4')
      | ~ r2_hidden(B_68,'#skF_2')
      | ~ r2_hidden(A_67,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_214,c_18])).

tff(c_270,plain,(
    ! [B_73] : ~ r2_hidden(B_73,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_302,plain,(
    ! [B_77] : r1_tarski('#skF_2',B_77) ),
    inference(resolution,[status(thm)],[c_6,c_270])).

tff(c_134,plain,(
    ! [A_51,B_52,A_53] :
      ( r2_hidden(k4_tarski(A_51,B_52),k1_xboole_0)
      | ~ r2_hidden(B_52,k1_xboole_0)
      | ~ r2_hidden(A_51,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_154,plain,(
    ! [A_57,B_58,B_59] :
      ( r2_hidden(k4_tarski('#skF_1'(A_57,B_58),B_59),k1_xboole_0)
      | ~ r2_hidden(B_59,k1_xboole_0)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_167,plain,(
    ! [B_59,B_13,A_57,B_58] :
      ( r2_hidden(B_59,B_13)
      | ~ r2_hidden(B_59,k1_xboole_0)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_154,c_103])).

tff(c_182,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,B_58) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_4','#skF_2')
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_115,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_115])).

tff(c_202,plain,(
    ! [B_65,B_66] :
      ( r2_hidden(B_65,B_66)
      | ~ r2_hidden(B_65,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_232,plain,(
    ! [B_69,B_70] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_69),B_70)
      | r1_tarski(k1_xboole_0,B_69) ) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_252,plain,(
    ! [B_71] : r1_tarski(k1_xboole_0,B_71) ),
    inference(resolution,[status(thm)],[c_232,c_4])).

tff(c_255,plain,(
    ! [B_71] :
      ( k1_xboole_0 = B_71
      | ~ r1_tarski(B_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_252,c_8])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_302,c_255])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_306])).

tff(c_314,plain,(
    ! [A_78] :
      ( r2_hidden(A_78,'#skF_4')
      | ~ r2_hidden(A_78,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_325,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_1'('#skF_3',B_79),'#skF_4')
      | r1_tarski('#skF_3',B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_314])).

tff(c_335,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_325,c_4])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_335])).

tff(c_343,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_353,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,'#skF_3')
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_18])).

tff(c_386,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(A_82,'#skF_3')
      | ~ r2_hidden(B_83,'#skF_2')
      | ~ r2_hidden(A_82,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_364,c_353])).

tff(c_400,plain,(
    ! [B_83] : ~ r2_hidden(B_83,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_535,plain,(
    ! [B_109] : r1_tarski(k1_xboole_0,B_109) ),
    inference(resolution,[status(thm)],[c_511,c_400])).

tff(c_401,plain,(
    ! [B_89] : ~ r2_hidden(B_89,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_412,plain,(
    ! [B_90] : r1_tarski('#skF_2',B_90) ),
    inference(resolution,[status(thm)],[c_6,c_401])).

tff(c_415,plain,(
    ! [B_90] :
      ( B_90 = '#skF_2'
      | ~ r1_tarski(B_90,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_412,c_8])).

tff(c_542,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_535,c_415])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_542])).

tff(c_552,plain,(
    ! [A_110] :
      ( r2_hidden(A_110,'#skF_3')
      | ~ r2_hidden(A_110,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_604,plain,(
    ! [A_117,B_118] :
      ( r2_hidden(A_117,B_118)
      | ~ r1_tarski('#skF_3',B_118)
      | ~ r2_hidden(A_117,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_552,c_2])).

tff(c_612,plain,(
    ! [B_2,B_118] :
      ( r2_hidden('#skF_1'('#skF_4',B_2),B_118)
      | ~ r1_tarski('#skF_3',B_118)
      | r1_tarski('#skF_4',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_604])).

tff(c_651,plain,(
    ! [A_122,B_123] :
      ( r2_hidden(k4_tarski(A_122,B_123),k2_zfmisc_1('#skF_4','#skF_2'))
      | ~ r2_hidden(B_123,'#skF_2')
      | ~ r2_hidden(A_122,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_364])).

tff(c_671,plain,(
    ! [A_122,B_123] :
      ( r2_hidden(A_122,'#skF_4')
      | ~ r2_hidden(B_123,'#skF_2')
      | ~ r2_hidden(A_122,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_651,c_18])).

tff(c_674,plain,(
    ! [B_124] : ~ r2_hidden(B_124,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_687,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_3','#skF_2')
      | r1_tarski('#skF_4',B_2) ) ),
    inference(resolution,[status(thm)],[c_612,c_674])).

tff(c_733,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_733])).

tff(c_786,plain,(
    ! [A_137,A_138] :
      ( r2_hidden(A_137,A_138)
      | ~ r2_hidden(A_137,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_802,plain,(
    ! [B_139,A_140] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_139),A_140)
      | r1_tarski(k1_xboole_0,B_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_786])).

tff(c_835,plain,(
    ! [A_141] : r1_tarski(k1_xboole_0,A_141) ),
    inference(resolution,[status(thm)],[c_802,c_4])).

tff(c_690,plain,(
    ! [B_125] : r1_tarski('#skF_2',B_125) ),
    inference(resolution,[status(thm)],[c_6,c_674])).

tff(c_693,plain,(
    ! [B_125] :
      ( B_125 = '#skF_2'
      | ~ r1_tarski(B_125,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_690,c_8])).

tff(c_842,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_835,c_693])).

tff(c_850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_842])).

tff(c_852,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_882,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_852,c_693])).

tff(c_689,plain,(
    ! [B_2] : r1_tarski('#skF_2',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_674])).

tff(c_893,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_689])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_26])).

tff(c_958,plain,(
    ! [A_153] :
      ( r2_hidden(A_153,'#skF_4')
      | ~ r2_hidden(A_153,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_980,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_1'('#skF_3',B_154),'#skF_4')
      | r1_tarski('#skF_3',B_154) ) ),
    inference(resolution,[status(thm)],[c_6,c_958])).

tff(c_996,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_980,c_4])).

tff(c_1006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_996])).

tff(c_1008,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1008])).

tff(c_1455,plain,(
    ! [B_236,B_237] :
      ( r2_hidden(B_236,B_237)
      | ~ r2_hidden(B_236,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1430])).

tff(c_1467,plain,(
    ! [B_238,B_239] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_238),B_239)
      | r1_tarski(k1_xboole_0,B_238) ) ),
    inference(resolution,[status(thm)],[c_6,c_1455])).

tff(c_1491,plain,(
    ! [B_240] : r1_tarski(k1_xboole_0,B_240) ),
    inference(resolution,[status(thm)],[c_1467,c_4])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11))
      | ~ r2_hidden(B_9,D_11)
      | ~ r2_hidden(A_8,C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1007,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1207,plain,(
    ! [B_208,D_205,B_206,C_207,A_204] :
      ( r2_hidden(k4_tarski(A_204,B_206),B_208)
      | ~ r1_tarski(k2_zfmisc_1(C_207,D_205),B_208)
      | ~ r2_hidden(B_206,D_205)
      | ~ r2_hidden(A_204,C_207) ) ),
    inference(resolution,[status(thm)],[c_1031,c_2])).

tff(c_1224,plain,(
    ! [A_209,B_210] :
      ( r2_hidden(k4_tarski(A_209,B_210),k2_zfmisc_1('#skF_2','#skF_4'))
      | ~ r2_hidden(B_210,'#skF_3')
      | ~ r2_hidden(A_209,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1007,c_1207])).

tff(c_16,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1233,plain,(
    ! [B_210,A_209] :
      ( r2_hidden(B_210,'#skF_4')
      | ~ r2_hidden(B_210,'#skF_3')
      | ~ r2_hidden(A_209,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1224,c_16])).

tff(c_1256,plain,(
    ! [A_214] : ~ r2_hidden(A_214,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1233])).

tff(c_1267,plain,(
    ! [B_215] : r1_tarski('#skF_2',B_215) ),
    inference(resolution,[status(thm)],[c_6,c_1256])).

tff(c_1081,plain,(
    ! [A_187,B_188,B_189] :
      ( r2_hidden(k4_tarski('#skF_1'(A_187,B_188),B_189),k1_xboole_0)
      | ~ r2_hidden(B_189,k1_xboole_0)
      | r1_tarski(A_187,B_188) ) ),
    inference(resolution,[status(thm)],[c_6,c_1051])).

tff(c_1094,plain,(
    ! [B_189,B_13,A_187,B_188] :
      ( r2_hidden(B_189,B_13)
      | ~ r2_hidden(B_189,k1_xboole_0)
      | r1_tarski(A_187,B_188) ) ),
    inference(resolution,[status(thm)],[c_1081,c_1030])).

tff(c_1097,plain,(
    ! [A_187,B_188] : r1_tarski(A_187,B_188) ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_1011,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = k2_zfmisc_1('#skF_2','#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1007,c_8])).

tff(c_1058,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1011])).

tff(c_1129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_1058])).

tff(c_1131,plain,(
    ! [B_195,B_196] :
      ( r2_hidden(B_195,B_196)
      | ~ r2_hidden(B_195,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_1143,plain,(
    ! [B_197,B_198] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_197),B_198)
      | r1_tarski(k1_xboole_0,B_197) ) ),
    inference(resolution,[status(thm)],[c_6,c_1131])).

tff(c_1163,plain,(
    ! [B_199] : r1_tarski(k1_xboole_0,B_199) ),
    inference(resolution,[status(thm)],[c_1143,c_4])).

tff(c_1166,plain,(
    ! [B_199] :
      ( k1_xboole_0 = B_199
      | ~ r1_tarski(B_199,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1163,c_8])).

tff(c_1274,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1267,c_1166])).

tff(c_1282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1274])).

tff(c_1284,plain,(
    ! [B_216] :
      ( r2_hidden(B_216,'#skF_4')
      | ~ r2_hidden(B_216,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1233])).

tff(c_1295,plain,(
    ! [B_217] :
      ( r2_hidden('#skF_1'('#skF_3',B_217),'#skF_4')
      | r1_tarski('#skF_3',B_217) ) ),
    inference(resolution,[status(thm)],[c_6,c_1284])).

tff(c_1301,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1295,c_4])).

tff(c_1306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_1301])).

tff(c_1307,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k2_zfmisc_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_1330,plain,(
    ! [B_218,A_219] :
      ( r2_hidden(B_218,'#skF_3')
      | ~ r2_hidden(k4_tarski(A_219,B_218),k2_zfmisc_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_16])).

tff(c_1335,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,'#skF_3')
      | ~ r2_hidden(B_9,'#skF_4')
      | ~ r2_hidden(A_8,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_1330])).

tff(c_1356,plain,(
    ! [A_222] : ~ r2_hidden(A_222,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1335])).

tff(c_1362,plain,(
    ! [B_223] : r1_tarski('#skF_2',B_223) ),
    inference(resolution,[status(thm)],[c_6,c_1356])).

tff(c_1365,plain,(
    ! [B_223] :
      ( B_223 = '#skF_2'
      | ~ r1_tarski(B_223,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1362,c_8])).

tff(c_1498,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1491,c_1365])).

tff(c_1506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1498])).

tff(c_1520,plain,(
    ! [B_244] :
      ( r2_hidden(B_244,'#skF_3')
      | ~ r2_hidden(B_244,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1335])).

tff(c_1612,plain,(
    ! [B_256,B_257] :
      ( r2_hidden(B_256,B_257)
      | ~ r1_tarski('#skF_3',B_257)
      | ~ r2_hidden(B_256,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1520,c_2])).

tff(c_1621,plain,(
    ! [B_258,B_259] :
      ( r2_hidden('#skF_1'('#skF_4',B_258),B_259)
      | ~ r1_tarski('#skF_3',B_259)
      | r1_tarski('#skF_4',B_258) ) ),
    inference(resolution,[status(thm)],[c_6,c_1612])).

tff(c_1336,plain,(
    ! [A_220,B_221] :
      ( r2_hidden(k4_tarski(A_220,B_221),k2_zfmisc_1('#skF_2','#skF_4'))
      | ~ r2_hidden(B_221,'#skF_3')
      | ~ r2_hidden(A_220,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_14])).

tff(c_1352,plain,(
    ! [B_221,A_220] :
      ( r2_hidden(B_221,'#skF_4')
      | ~ r2_hidden(B_221,'#skF_3')
      | ~ r2_hidden(A_220,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1336,c_16])).

tff(c_1546,plain,(
    ! [A_220] : ~ r2_hidden(A_220,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1352])).

tff(c_1645,plain,(
    ! [B_258] :
      ( ~ r1_tarski('#skF_3','#skF_2')
      | r1_tarski('#skF_4',B_258) ) ),
    inference(resolution,[status(thm)],[c_1621,c_1546])).

tff(c_1664,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1645])).

tff(c_1732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1664])).

tff(c_1734,plain,(
    ! [B_269,B_270] :
      ( r2_hidden(B_269,B_270)
      | ~ r2_hidden(B_269,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1678])).

tff(c_1750,plain,(
    ! [B_271,B_272] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_271),B_272)
      | r1_tarski(k1_xboole_0,B_271) ) ),
    inference(resolution,[status(thm)],[c_6,c_1734])).

tff(c_1787,plain,(
    ! [B_273] : r1_tarski(k1_xboole_0,B_273) ),
    inference(resolution,[status(thm)],[c_1750,c_4])).

tff(c_1547,plain,(
    ! [A_246] : ~ r2_hidden(A_246,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1352])).

tff(c_1558,plain,(
    ! [B_247] : r1_tarski('#skF_2',B_247) ),
    inference(resolution,[status(thm)],[c_6,c_1547])).

tff(c_1561,plain,(
    ! [B_247] :
      ( B_247 = '#skF_2'
      | ~ r1_tarski(B_247,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1558,c_8])).

tff(c_1794,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1787,c_1561])).

tff(c_1802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1794])).

tff(c_1808,plain,(
    ! [B_274] : r1_tarski('#skF_4',B_274) ),
    inference(splitRight,[status(thm)],[c_1645])).

tff(c_1820,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1808,c_1561])).

tff(c_1804,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1645])).

tff(c_1849,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_1804])).

tff(c_1850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1849])).

tff(c_1852,plain,(
    ! [B_280] :
      ( r2_hidden(B_280,'#skF_4')
      | ~ r2_hidden(B_280,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1352])).

tff(c_1884,plain,(
    ! [B_285] :
      ( r2_hidden('#skF_1'('#skF_3',B_285),'#skF_4')
      | r1_tarski('#skF_3',B_285) ) ),
    inference(resolution,[status(thm)],[c_6,c_1852])).

tff(c_1896,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1884,c_4])).

tff(c_1904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_1896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.58  
% 3.41/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.58  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.41/1.58  
% 3.41/1.58  %Foreground sorts:
% 3.41/1.58  
% 3.41/1.58  
% 3.41/1.58  %Background operators:
% 3.41/1.58  
% 3.41/1.58  
% 3.41/1.58  %Foreground operators:
% 3.41/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.41/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.41/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.41/1.58  
% 3.41/1.61  tff(f_62, negated_conjecture, ~(![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 3.41/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.41/1.61  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.41/1.61  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.41/1.61  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.41/1.61  tff(c_26, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.61  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.61  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.41/1.61  tff(c_1031, plain, (![A_169, B_170, C_171, D_172]: (r2_hidden(k4_tarski(A_169, B_170), k2_zfmisc_1(C_171, D_172)) | ~r2_hidden(B_170, D_172) | ~r2_hidden(A_169, C_171))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_1051, plain, (![A_178, B_179, A_180]: (r2_hidden(k4_tarski(A_178, B_179), k1_xboole_0) | ~r2_hidden(B_179, k1_xboole_0) | ~r2_hidden(A_178, A_180))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1031])).
% 3.41/1.61  tff(c_1665, plain, (![A_261, B_262, B_263]: (r2_hidden(k4_tarski('#skF_1'(A_261, B_262), B_263), k1_xboole_0) | ~r2_hidden(B_263, k1_xboole_0) | r1_tarski(A_261, B_262))), inference(resolution, [status(thm)], [c_6, c_1051])).
% 3.41/1.61  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.41/1.61  tff(c_1024, plain, (![B_165, D_166, A_167, C_168]: (r2_hidden(B_165, D_166) | ~r2_hidden(k4_tarski(A_167, B_165), k2_zfmisc_1(C_168, D_166)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_1030, plain, (![B_165, B_13, A_167]: (r2_hidden(B_165, B_13) | ~r2_hidden(k4_tarski(A_167, B_165), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1024])).
% 3.41/1.61  tff(c_1678, plain, (![B_263, B_13, A_261, B_262]: (r2_hidden(B_263, B_13) | ~r2_hidden(B_263, k1_xboole_0) | r1_tarski(A_261, B_262))), inference(resolution, [status(thm)], [c_1665, c_1030])).
% 3.41/1.61  tff(c_1681, plain, (![A_261, B_262]: (r1_tarski(A_261, B_262))), inference(splitLeft, [status(thm)], [c_1678])).
% 3.41/1.61  tff(c_1417, plain, (![A_233, B_234, B_235]: (r2_hidden(k4_tarski('#skF_1'(A_233, B_234), B_235), k1_xboole_0) | ~r2_hidden(B_235, k1_xboole_0) | r1_tarski(A_233, B_234))), inference(resolution, [status(thm)], [c_6, c_1051])).
% 3.41/1.61  tff(c_1430, plain, (![B_235, B_13, A_233, B_234]: (r2_hidden(B_235, B_13) | ~r2_hidden(B_235, k1_xboole_0) | r1_tarski(A_233, B_234))), inference(resolution, [status(thm)], [c_1417, c_1030])).
% 3.41/1.61  tff(c_1433, plain, (![A_233, B_234]: (r1_tarski(A_233, B_234))), inference(splitLeft, [status(thm)], [c_1430])).
% 3.41/1.61  tff(c_364, plain, (![A_82, B_83, C_84, D_85]: (r2_hidden(k4_tarski(A_82, B_83), k2_zfmisc_1(C_84, D_85)) | ~r2_hidden(B_83, D_85) | ~r2_hidden(A_82, C_84))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_591, plain, (![A_114, B_115, B_116]: (r2_hidden(k4_tarski(A_114, B_115), k1_xboole_0) | ~r2_hidden(B_115, B_116) | ~r2_hidden(A_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_364])).
% 3.41/1.61  tff(c_734, plain, (![A_134, A_135, B_136]: (r2_hidden(k4_tarski(A_134, '#skF_1'(A_135, B_136)), k1_xboole_0) | ~r2_hidden(A_134, k1_xboole_0) | r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_6, c_591])).
% 3.41/1.61  tff(c_89, plain, (![A_28, C_29, B_30, D_31]: (r2_hidden(A_28, C_29) | ~r2_hidden(k4_tarski(A_28, B_30), k2_zfmisc_1(C_29, D_31)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_92, plain, (![A_28, A_12, B_30]: (r2_hidden(A_28, A_12) | ~r2_hidden(k4_tarski(A_28, B_30), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_89])).
% 3.41/1.61  tff(c_748, plain, (![A_134, A_12, A_135, B_136]: (r2_hidden(A_134, A_12) | ~r2_hidden(A_134, k1_xboole_0) | r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_734, c_92])).
% 3.41/1.61  tff(c_750, plain, (![A_135, B_136]: (r1_tarski(A_135, B_136))), inference(splitLeft, [status(thm)], [c_748])).
% 3.41/1.61  tff(c_390, plain, (![A_86, B_87, A_88]: (r2_hidden(k4_tarski(A_86, B_87), k1_xboole_0) | ~r2_hidden(B_87, k1_xboole_0) | ~r2_hidden(A_86, A_88))), inference(superposition, [status(thm), theory('equality')], [c_22, c_364])).
% 3.41/1.61  tff(c_450, plain, (![A_97, B_98, B_99]: (r2_hidden(k4_tarski('#skF_1'(A_97, B_98), B_99), k1_xboole_0) | ~r2_hidden(B_99, k1_xboole_0) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_6, c_390])).
% 3.41/1.61  tff(c_97, plain, (![B_35, D_36, A_37, C_38]: (r2_hidden(B_35, D_36) | ~r2_hidden(k4_tarski(A_37, B_35), k2_zfmisc_1(C_38, D_36)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_103, plain, (![B_35, B_13, A_37]: (r2_hidden(B_35, B_13) | ~r2_hidden(k4_tarski(A_37, B_35), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_97])).
% 3.41/1.61  tff(c_463, plain, (![B_99, B_13, A_97, B_98]: (r2_hidden(B_99, B_13) | ~r2_hidden(B_99, k1_xboole_0) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_450, c_103])).
% 3.41/1.61  tff(c_466, plain, (![A_97, B_98]: (r1_tarski(A_97, B_98))), inference(splitLeft, [status(thm)], [c_463])).
% 3.41/1.61  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_466, c_26])).
% 3.41/1.61  tff(c_499, plain, (![B_105, B_106]: (r2_hidden(B_105, B_106) | ~r2_hidden(B_105, k1_xboole_0))), inference(splitRight, [status(thm)], [c_463])).
% 3.41/1.61  tff(c_511, plain, (![B_107, B_108]: (r2_hidden('#skF_1'(k1_xboole_0, B_107), B_108) | r1_tarski(k1_xboole_0, B_107))), inference(resolution, [status(thm)], [c_6, c_499])).
% 3.41/1.61  tff(c_28, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.61  tff(c_81, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_28])).
% 3.41/1.61  tff(c_116, plain, (![A_47, B_48, C_49, D_50]: (r2_hidden(k4_tarski(A_47, B_48), k2_zfmisc_1(C_49, D_50)) | ~r2_hidden(B_48, D_50) | ~r2_hidden(A_47, C_49))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.61  tff(c_170, plain, (![B_63, B_62, A_60, D_61, C_64]: (r2_hidden(k4_tarski(A_60, B_62), B_63) | ~r1_tarski(k2_zfmisc_1(C_64, D_61), B_63) | ~r2_hidden(B_62, D_61) | ~r2_hidden(A_60, C_64))), inference(resolution, [status(thm)], [c_116, c_2])).
% 3.41/1.61  tff(c_214, plain, (![A_67, B_68]: (r2_hidden(k4_tarski(A_67, B_68), k2_zfmisc_1('#skF_4', '#skF_2')) | ~r2_hidden(B_68, '#skF_2') | ~r2_hidden(A_67, '#skF_3'))), inference(resolution, [status(thm)], [c_81, c_170])).
% 3.41/1.61  tff(c_18, plain, (![A_8, C_10, B_9, D_11]: (r2_hidden(A_8, C_10) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_230, plain, (![A_67, B_68]: (r2_hidden(A_67, '#skF_4') | ~r2_hidden(B_68, '#skF_2') | ~r2_hidden(A_67, '#skF_3'))), inference(resolution, [status(thm)], [c_214, c_18])).
% 3.41/1.61  tff(c_270, plain, (![B_73]: (~r2_hidden(B_73, '#skF_2'))), inference(splitLeft, [status(thm)], [c_230])).
% 3.41/1.61  tff(c_302, plain, (![B_77]: (r1_tarski('#skF_2', B_77))), inference(resolution, [status(thm)], [c_6, c_270])).
% 3.41/1.61  tff(c_134, plain, (![A_51, B_52, A_53]: (r2_hidden(k4_tarski(A_51, B_52), k1_xboole_0) | ~r2_hidden(B_52, k1_xboole_0) | ~r2_hidden(A_51, A_53))), inference(superposition, [status(thm), theory('equality')], [c_22, c_116])).
% 3.41/1.61  tff(c_154, plain, (![A_57, B_58, B_59]: (r2_hidden(k4_tarski('#skF_1'(A_57, B_58), B_59), k1_xboole_0) | ~r2_hidden(B_59, k1_xboole_0) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_6, c_134])).
% 3.41/1.61  tff(c_167, plain, (![B_59, B_13, A_57, B_58]: (r2_hidden(B_59, B_13) | ~r2_hidden(B_59, k1_xboole_0) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_154, c_103])).
% 3.41/1.61  tff(c_182, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58))), inference(splitLeft, [status(thm)], [c_167])).
% 3.41/1.61  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.61  tff(c_84, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_2') | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_81, c_8])).
% 3.41/1.61  tff(c_115, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_84])).
% 3.41/1.61  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_115])).
% 3.41/1.61  tff(c_202, plain, (![B_65, B_66]: (r2_hidden(B_65, B_66) | ~r2_hidden(B_65, k1_xboole_0))), inference(splitRight, [status(thm)], [c_167])).
% 3.41/1.61  tff(c_232, plain, (![B_69, B_70]: (r2_hidden('#skF_1'(k1_xboole_0, B_69), B_70) | r1_tarski(k1_xboole_0, B_69))), inference(resolution, [status(thm)], [c_6, c_202])).
% 3.41/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.61  tff(c_252, plain, (![B_71]: (r1_tarski(k1_xboole_0, B_71))), inference(resolution, [status(thm)], [c_232, c_4])).
% 3.41/1.61  tff(c_255, plain, (![B_71]: (k1_xboole_0=B_71 | ~r1_tarski(B_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_252, c_8])).
% 3.41/1.61  tff(c_306, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_302, c_255])).
% 3.41/1.61  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_306])).
% 3.41/1.61  tff(c_314, plain, (![A_78]: (r2_hidden(A_78, '#skF_4') | ~r2_hidden(A_78, '#skF_3'))), inference(splitRight, [status(thm)], [c_230])).
% 3.41/1.61  tff(c_325, plain, (![B_79]: (r2_hidden('#skF_1'('#skF_3', B_79), '#skF_4') | r1_tarski('#skF_3', B_79))), inference(resolution, [status(thm)], [c_6, c_314])).
% 3.41/1.61  tff(c_335, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_325, c_4])).
% 3.41/1.61  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_335])).
% 3.41/1.61  tff(c_343, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_84])).
% 3.41/1.61  tff(c_353, plain, (![A_8, B_9]: (r2_hidden(A_8, '#skF_3') | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1('#skF_4', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_343, c_18])).
% 3.41/1.61  tff(c_386, plain, (![A_82, B_83]: (r2_hidden(A_82, '#skF_3') | ~r2_hidden(B_83, '#skF_2') | ~r2_hidden(A_82, '#skF_4'))), inference(resolution, [status(thm)], [c_364, c_353])).
% 3.41/1.61  tff(c_400, plain, (![B_83]: (~r2_hidden(B_83, '#skF_2'))), inference(splitLeft, [status(thm)], [c_386])).
% 3.41/1.61  tff(c_535, plain, (![B_109]: (r1_tarski(k1_xboole_0, B_109))), inference(resolution, [status(thm)], [c_511, c_400])).
% 3.41/1.61  tff(c_401, plain, (![B_89]: (~r2_hidden(B_89, '#skF_2'))), inference(splitLeft, [status(thm)], [c_386])).
% 3.41/1.61  tff(c_412, plain, (![B_90]: (r1_tarski('#skF_2', B_90))), inference(resolution, [status(thm)], [c_6, c_401])).
% 3.41/1.61  tff(c_415, plain, (![B_90]: (B_90='#skF_2' | ~r1_tarski(B_90, '#skF_2'))), inference(resolution, [status(thm)], [c_412, c_8])).
% 3.41/1.61  tff(c_542, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_535, c_415])).
% 3.41/1.61  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_542])).
% 3.41/1.61  tff(c_552, plain, (![A_110]: (r2_hidden(A_110, '#skF_3') | ~r2_hidden(A_110, '#skF_4'))), inference(splitRight, [status(thm)], [c_386])).
% 3.41/1.61  tff(c_604, plain, (![A_117, B_118]: (r2_hidden(A_117, B_118) | ~r1_tarski('#skF_3', B_118) | ~r2_hidden(A_117, '#skF_4'))), inference(resolution, [status(thm)], [c_552, c_2])).
% 3.41/1.61  tff(c_612, plain, (![B_2, B_118]: (r2_hidden('#skF_1'('#skF_4', B_2), B_118) | ~r1_tarski('#skF_3', B_118) | r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_604])).
% 3.41/1.61  tff(c_651, plain, (![A_122, B_123]: (r2_hidden(k4_tarski(A_122, B_123), k2_zfmisc_1('#skF_4', '#skF_2')) | ~r2_hidden(B_123, '#skF_2') | ~r2_hidden(A_122, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_343, c_364])).
% 3.41/1.61  tff(c_671, plain, (![A_122, B_123]: (r2_hidden(A_122, '#skF_4') | ~r2_hidden(B_123, '#skF_2') | ~r2_hidden(A_122, '#skF_3'))), inference(resolution, [status(thm)], [c_651, c_18])).
% 3.41/1.61  tff(c_674, plain, (![B_124]: (~r2_hidden(B_124, '#skF_2'))), inference(splitLeft, [status(thm)], [c_671])).
% 3.41/1.61  tff(c_687, plain, (![B_2]: (~r1_tarski('#skF_3', '#skF_2') | r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_612, c_674])).
% 3.41/1.61  tff(c_733, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_687])).
% 3.41/1.61  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_750, c_733])).
% 3.41/1.61  tff(c_786, plain, (![A_137, A_138]: (r2_hidden(A_137, A_138) | ~r2_hidden(A_137, k1_xboole_0))), inference(splitRight, [status(thm)], [c_748])).
% 3.41/1.61  tff(c_802, plain, (![B_139, A_140]: (r2_hidden('#skF_1'(k1_xboole_0, B_139), A_140) | r1_tarski(k1_xboole_0, B_139))), inference(resolution, [status(thm)], [c_6, c_786])).
% 3.41/1.61  tff(c_835, plain, (![A_141]: (r1_tarski(k1_xboole_0, A_141))), inference(resolution, [status(thm)], [c_802, c_4])).
% 3.41/1.61  tff(c_690, plain, (![B_125]: (r1_tarski('#skF_2', B_125))), inference(resolution, [status(thm)], [c_6, c_674])).
% 3.41/1.61  tff(c_693, plain, (![B_125]: (B_125='#skF_2' | ~r1_tarski(B_125, '#skF_2'))), inference(resolution, [status(thm)], [c_690, c_8])).
% 3.41/1.61  tff(c_842, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_835, c_693])).
% 3.41/1.61  tff(c_850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_842])).
% 3.41/1.61  tff(c_852, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_687])).
% 3.41/1.61  tff(c_882, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_852, c_693])).
% 3.41/1.61  tff(c_689, plain, (![B_2]: (r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_6, c_674])).
% 3.41/1.61  tff(c_893, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_882, c_689])).
% 3.41/1.61  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_893, c_26])).
% 3.41/1.61  tff(c_958, plain, (![A_153]: (r2_hidden(A_153, '#skF_4') | ~r2_hidden(A_153, '#skF_3'))), inference(splitRight, [status(thm)], [c_671])).
% 3.41/1.61  tff(c_980, plain, (![B_154]: (r2_hidden('#skF_1'('#skF_3', B_154), '#skF_4') | r1_tarski('#skF_3', B_154))), inference(resolution, [status(thm)], [c_6, c_958])).
% 3.41/1.61  tff(c_996, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_980, c_4])).
% 3.41/1.61  tff(c_1006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_996])).
% 3.41/1.61  tff(c_1008, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_28])).
% 3.41/1.61  tff(c_1453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1433, c_1008])).
% 3.41/1.61  tff(c_1455, plain, (![B_236, B_237]: (r2_hidden(B_236, B_237) | ~r2_hidden(B_236, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1430])).
% 3.41/1.61  tff(c_1467, plain, (![B_238, B_239]: (r2_hidden('#skF_1'(k1_xboole_0, B_238), B_239) | r1_tarski(k1_xboole_0, B_238))), inference(resolution, [status(thm)], [c_6, c_1455])).
% 3.41/1.61  tff(c_1491, plain, (![B_240]: (r1_tarski(k1_xboole_0, B_240))), inference(resolution, [status(thm)], [c_1467, c_4])).
% 3.41/1.61  tff(c_14, plain, (![A_8, B_9, C_10, D_11]: (r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)) | ~r2_hidden(B_9, D_11) | ~r2_hidden(A_8, C_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_1007, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_28])).
% 3.41/1.61  tff(c_1207, plain, (![B_208, D_205, B_206, C_207, A_204]: (r2_hidden(k4_tarski(A_204, B_206), B_208) | ~r1_tarski(k2_zfmisc_1(C_207, D_205), B_208) | ~r2_hidden(B_206, D_205) | ~r2_hidden(A_204, C_207))), inference(resolution, [status(thm)], [c_1031, c_2])).
% 3.41/1.61  tff(c_1224, plain, (![A_209, B_210]: (r2_hidden(k4_tarski(A_209, B_210), k2_zfmisc_1('#skF_2', '#skF_4')) | ~r2_hidden(B_210, '#skF_3') | ~r2_hidden(A_209, '#skF_2'))), inference(resolution, [status(thm)], [c_1007, c_1207])).
% 3.41/1.61  tff(c_16, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.61  tff(c_1233, plain, (![B_210, A_209]: (r2_hidden(B_210, '#skF_4') | ~r2_hidden(B_210, '#skF_3') | ~r2_hidden(A_209, '#skF_2'))), inference(resolution, [status(thm)], [c_1224, c_16])).
% 3.41/1.61  tff(c_1256, plain, (![A_214]: (~r2_hidden(A_214, '#skF_2'))), inference(splitLeft, [status(thm)], [c_1233])).
% 3.41/1.61  tff(c_1267, plain, (![B_215]: (r1_tarski('#skF_2', B_215))), inference(resolution, [status(thm)], [c_6, c_1256])).
% 3.41/1.61  tff(c_1081, plain, (![A_187, B_188, B_189]: (r2_hidden(k4_tarski('#skF_1'(A_187, B_188), B_189), k1_xboole_0) | ~r2_hidden(B_189, k1_xboole_0) | r1_tarski(A_187, B_188))), inference(resolution, [status(thm)], [c_6, c_1051])).
% 3.41/1.61  tff(c_1094, plain, (![B_189, B_13, A_187, B_188]: (r2_hidden(B_189, B_13) | ~r2_hidden(B_189, k1_xboole_0) | r1_tarski(A_187, B_188))), inference(resolution, [status(thm)], [c_1081, c_1030])).
% 3.41/1.61  tff(c_1097, plain, (![A_187, B_188]: (r1_tarski(A_187, B_188))), inference(splitLeft, [status(thm)], [c_1094])).
% 3.41/1.61  tff(c_1011, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k2_zfmisc_1('#skF_2', '#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1007, c_8])).
% 3.41/1.61  tff(c_1058, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1011])).
% 3.41/1.61  tff(c_1129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1097, c_1058])).
% 3.41/1.61  tff(c_1131, plain, (![B_195, B_196]: (r2_hidden(B_195, B_196) | ~r2_hidden(B_195, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1094])).
% 3.41/1.61  tff(c_1143, plain, (![B_197, B_198]: (r2_hidden('#skF_1'(k1_xboole_0, B_197), B_198) | r1_tarski(k1_xboole_0, B_197))), inference(resolution, [status(thm)], [c_6, c_1131])).
% 3.41/1.61  tff(c_1163, plain, (![B_199]: (r1_tarski(k1_xboole_0, B_199))), inference(resolution, [status(thm)], [c_1143, c_4])).
% 3.41/1.61  tff(c_1166, plain, (![B_199]: (k1_xboole_0=B_199 | ~r1_tarski(B_199, k1_xboole_0))), inference(resolution, [status(thm)], [c_1163, c_8])).
% 3.41/1.61  tff(c_1274, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1267, c_1166])).
% 3.41/1.61  tff(c_1282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1274])).
% 3.41/1.61  tff(c_1284, plain, (![B_216]: (r2_hidden(B_216, '#skF_4') | ~r2_hidden(B_216, '#skF_3'))), inference(splitRight, [status(thm)], [c_1233])).
% 3.41/1.61  tff(c_1295, plain, (![B_217]: (r2_hidden('#skF_1'('#skF_3', B_217), '#skF_4') | r1_tarski('#skF_3', B_217))), inference(resolution, [status(thm)], [c_6, c_1284])).
% 3.41/1.61  tff(c_1301, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1295, c_4])).
% 3.41/1.61  tff(c_1306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_1301])).
% 3.41/1.61  tff(c_1307, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k2_zfmisc_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_1011])).
% 3.41/1.61  tff(c_1330, plain, (![B_218, A_219]: (r2_hidden(B_218, '#skF_3') | ~r2_hidden(k4_tarski(A_219, B_218), k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1307, c_16])).
% 3.41/1.61  tff(c_1335, plain, (![B_9, A_8]: (r2_hidden(B_9, '#skF_3') | ~r2_hidden(B_9, '#skF_4') | ~r2_hidden(A_8, '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_1330])).
% 3.41/1.61  tff(c_1356, plain, (![A_222]: (~r2_hidden(A_222, '#skF_2'))), inference(splitLeft, [status(thm)], [c_1335])).
% 3.41/1.61  tff(c_1362, plain, (![B_223]: (r1_tarski('#skF_2', B_223))), inference(resolution, [status(thm)], [c_6, c_1356])).
% 3.41/1.61  tff(c_1365, plain, (![B_223]: (B_223='#skF_2' | ~r1_tarski(B_223, '#skF_2'))), inference(resolution, [status(thm)], [c_1362, c_8])).
% 3.41/1.61  tff(c_1498, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1491, c_1365])).
% 3.41/1.61  tff(c_1506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1498])).
% 3.41/1.61  tff(c_1520, plain, (![B_244]: (r2_hidden(B_244, '#skF_3') | ~r2_hidden(B_244, '#skF_4'))), inference(splitRight, [status(thm)], [c_1335])).
% 3.41/1.61  tff(c_1612, plain, (![B_256, B_257]: (r2_hidden(B_256, B_257) | ~r1_tarski('#skF_3', B_257) | ~r2_hidden(B_256, '#skF_4'))), inference(resolution, [status(thm)], [c_1520, c_2])).
% 3.41/1.61  tff(c_1621, plain, (![B_258, B_259]: (r2_hidden('#skF_1'('#skF_4', B_258), B_259) | ~r1_tarski('#skF_3', B_259) | r1_tarski('#skF_4', B_258))), inference(resolution, [status(thm)], [c_6, c_1612])).
% 3.41/1.61  tff(c_1336, plain, (![A_220, B_221]: (r2_hidden(k4_tarski(A_220, B_221), k2_zfmisc_1('#skF_2', '#skF_4')) | ~r2_hidden(B_221, '#skF_3') | ~r2_hidden(A_220, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1307, c_14])).
% 3.41/1.61  tff(c_1352, plain, (![B_221, A_220]: (r2_hidden(B_221, '#skF_4') | ~r2_hidden(B_221, '#skF_3') | ~r2_hidden(A_220, '#skF_2'))), inference(resolution, [status(thm)], [c_1336, c_16])).
% 3.41/1.61  tff(c_1546, plain, (![A_220]: (~r2_hidden(A_220, '#skF_2'))), inference(splitLeft, [status(thm)], [c_1352])).
% 3.41/1.61  tff(c_1645, plain, (![B_258]: (~r1_tarski('#skF_3', '#skF_2') | r1_tarski('#skF_4', B_258))), inference(resolution, [status(thm)], [c_1621, c_1546])).
% 3.41/1.61  tff(c_1664, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1645])).
% 3.41/1.61  tff(c_1732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1664])).
% 3.41/1.61  tff(c_1734, plain, (![B_269, B_270]: (r2_hidden(B_269, B_270) | ~r2_hidden(B_269, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1678])).
% 3.41/1.61  tff(c_1750, plain, (![B_271, B_272]: (r2_hidden('#skF_1'(k1_xboole_0, B_271), B_272) | r1_tarski(k1_xboole_0, B_271))), inference(resolution, [status(thm)], [c_6, c_1734])).
% 3.41/1.61  tff(c_1787, plain, (![B_273]: (r1_tarski(k1_xboole_0, B_273))), inference(resolution, [status(thm)], [c_1750, c_4])).
% 3.41/1.61  tff(c_1547, plain, (![A_246]: (~r2_hidden(A_246, '#skF_2'))), inference(splitLeft, [status(thm)], [c_1352])).
% 3.41/1.61  tff(c_1558, plain, (![B_247]: (r1_tarski('#skF_2', B_247))), inference(resolution, [status(thm)], [c_6, c_1547])).
% 3.41/1.61  tff(c_1561, plain, (![B_247]: (B_247='#skF_2' | ~r1_tarski(B_247, '#skF_2'))), inference(resolution, [status(thm)], [c_1558, c_8])).
% 3.41/1.61  tff(c_1794, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1787, c_1561])).
% 3.41/1.61  tff(c_1802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1794])).
% 3.41/1.61  tff(c_1808, plain, (![B_274]: (r1_tarski('#skF_4', B_274))), inference(splitRight, [status(thm)], [c_1645])).
% 3.41/1.61  tff(c_1820, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_1808, c_1561])).
% 3.41/1.61  tff(c_1804, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1645])).
% 3.41/1.61  tff(c_1849, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_1804])).
% 3.41/1.61  tff(c_1850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1849])).
% 3.41/1.61  tff(c_1852, plain, (![B_280]: (r2_hidden(B_280, '#skF_4') | ~r2_hidden(B_280, '#skF_3'))), inference(splitRight, [status(thm)], [c_1352])).
% 3.41/1.61  tff(c_1884, plain, (![B_285]: (r2_hidden('#skF_1'('#skF_3', B_285), '#skF_4') | r1_tarski('#skF_3', B_285))), inference(resolution, [status(thm)], [c_6, c_1852])).
% 3.41/1.61  tff(c_1896, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1884, c_4])).
% 3.41/1.61  tff(c_1904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_1896])).
% 3.41/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.61  
% 3.41/1.61  Inference rules
% 3.41/1.61  ----------------------
% 3.41/1.61  #Ref     : 0
% 3.41/1.61  #Sup     : 396
% 3.41/1.61  #Fact    : 0
% 3.41/1.61  #Define  : 0
% 3.41/1.61  #Split   : 20
% 3.41/1.61  #Chain   : 0
% 3.41/1.61  #Close   : 0
% 3.41/1.61  
% 3.41/1.61  Ordering : KBO
% 3.41/1.61  
% 3.41/1.61  Simplification rules
% 3.41/1.61  ----------------------
% 3.41/1.61  #Subsume      : 81
% 3.41/1.61  #Demod        : 198
% 3.41/1.61  #Tautology    : 142
% 3.41/1.61  #SimpNegUnit  : 18
% 3.41/1.61  #BackRed      : 61
% 3.41/1.61  
% 3.41/1.61  #Partial instantiations: 0
% 3.41/1.61  #Strategies tried      : 1
% 3.41/1.61  
% 3.41/1.61  Timing (in seconds)
% 3.41/1.61  ----------------------
% 3.77/1.61  Preprocessing        : 0.28
% 3.77/1.61  Parsing              : 0.15
% 3.77/1.61  CNF conversion       : 0.02
% 3.77/1.61  Main loop            : 0.54
% 3.77/1.61  Inferencing          : 0.19
% 3.77/1.61  Reduction            : 0.15
% 3.77/1.61  Demodulation         : 0.10
% 3.77/1.61  BG Simplification    : 0.03
% 3.77/1.61  Subsumption          : 0.14
% 3.77/1.61  Abstraction          : 0.02
% 3.77/1.61  MUC search           : 0.00
% 3.77/1.61  Cooper               : 0.00
% 3.77/1.61  Total                : 0.88
% 3.77/1.61  Index Insertion      : 0.00
% 3.77/1.61  Index Deletion       : 0.00
% 3.77/1.61  Index Matching       : 0.00
% 3.77/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
