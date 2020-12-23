%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:21 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 393 expanded)
%              Number of leaves         :   27 ( 146 expanded)
%              Depth                    :   14
%              Number of atoms          :  118 ( 697 expanded)
%              Number of equality atoms :   46 ( 268 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ~ ( r2_hidden(A,k4_zfmisc_1(B,C,D,E))
          & ! [F,G,H,I] :
              ~ ( r2_hidden(F,B)
                & r2_hidden(G,C)
                & r2_hidden(H,D)
                & r2_hidden(I,E)
                & A = k4_mcart_1(F,G,H,I) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(c_22,plain,(
    r2_hidden('#skF_3',k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    ! [A_51,B_52,C_53,D_54] : k2_zfmisc_1(k3_zfmisc_1(A_51,B_52,C_53),D_54) = k4_zfmisc_1(A_51,B_52,C_53,D_54) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,(
    ! [C_74,B_72,D_75,A_71,A_73] :
      ( r2_hidden(k2_mcart_1(A_73),D_75)
      | ~ r2_hidden(A_73,k4_zfmisc_1(A_71,B_72,C_74,D_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_116,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_113])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15,D_16] : k2_zfmisc_1(k3_zfmisc_1(A_13,B_14,C_15),D_16) = k4_zfmisc_1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [A_80,B_81,C_82] :
      ( k4_tarski('#skF_1'(A_80,B_81,C_82),'#skF_2'(A_80,B_81,C_82)) = A_80
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_24,B_25] : k2_mcart_1(k4_tarski(A_24,B_25)) = B_25 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_223,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_mcart_1(A_95) = '#skF_2'(A_95,B_96,C_97)
      | ~ r2_hidden(A_95,k2_zfmisc_1(B_96,C_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_18])).

tff(c_624,plain,(
    ! [A_166,A_165,C_167,B_164,D_163] :
      ( '#skF_2'(A_165,k3_zfmisc_1(A_166,B_164,C_167),D_163) = k2_mcart_1(A_165)
      | ~ r2_hidden(A_165,k4_zfmisc_1(A_166,B_164,C_167,D_163)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_223])).

tff(c_632,plain,(
    '#skF_2'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7') = k2_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_624])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_636,plain,
    ( k4_tarski('#skF_1'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_2])).

tff(c_640,plain,(
    k4_tarski('#skF_1'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8,c_636])).

tff(c_16,plain,(
    ! [A_24,B_25] : k1_mcart_1(k4_tarski(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_654,plain,(
    '#skF_1'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_16])).

tff(c_663,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_640])).

tff(c_12,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_315,plain,(
    ! [A_117,D_119,A_115,B_116,C_118] :
      ( r2_hidden(k1_mcart_1(A_117),k3_zfmisc_1(A_115,B_116,C_118))
      | ~ r2_hidden(A_117,k4_zfmisc_1(A_115,B_116,C_118,D_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_318,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_22,c_315])).

tff(c_4,plain,(
    ! [A_6,B_7,C_8] : k2_zfmisc_1(k2_zfmisc_1(A_6,B_7),C_8) = k3_zfmisc_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k1_mcart_1(A_41),B_42)
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_41,A_6,B_7,C_8] :
      ( r2_hidden(k1_mcart_1(A_41),k2_zfmisc_1(A_6,B_7))
      | ~ r2_hidden(A_41,k3_zfmisc_1(A_6,B_7,C_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_323,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_318,c_58])).

tff(c_161,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_mcart_1(A_80) = '#skF_2'(A_80,B_81,C_82)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_18])).

tff(c_335,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))) = '#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_323,c_161])).

tff(c_337,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_323,c_10])).

tff(c_373,plain,(
    r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_337])).

tff(c_158,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_mcart_1(A_80) = '#skF_1'(A_80,B_81,C_82)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_16])).

tff(c_336,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))) = '#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_323,c_158])).

tff(c_338,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_323,c_12])).

tff(c_339,plain,(
    r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_338])).

tff(c_59,plain,(
    ! [A_44,C_45,B_46] :
      ( r2_hidden(k2_mcart_1(A_44),C_45)
      | ~ r2_hidden(A_44,k2_zfmisc_1(B_46,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    ! [A_44,C_8,A_6,B_7] :
      ( r2_hidden(k2_mcart_1(A_44),C_8)
      | ~ r2_hidden(A_44,k3_zfmisc_1(A_6,B_7,C_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_324,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_318,c_61])).

tff(c_383,plain,(
    ! [A_130,A_131,B_132,C_133] :
      ( '#skF_2'(A_130,k2_zfmisc_1(A_131,B_132),C_133) = k2_mcart_1(A_130)
      | ~ r2_hidden(A_130,k3_zfmisc_1(A_131,B_132,C_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_223])).

tff(c_393,plain,(
    '#skF_2'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k2_mcart_1(k1_mcart_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_318,c_383])).

tff(c_399,plain,
    ( k4_tarski('#skF_1'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1(k1_mcart_1('#skF_3'))) = k1_mcart_1('#skF_3')
    | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_2])).

tff(c_403,plain,(
    k4_tarski('#skF_1'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1(k1_mcart_1('#skF_3'))) = k1_mcart_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_4,c_399])).

tff(c_417,plain,(
    '#skF_1'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k1_mcart_1(k1_mcart_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_16])).

tff(c_425,plain,(
    k4_tarski(k1_mcart_1(k1_mcart_1('#skF_3')),k2_mcart_1(k1_mcart_1('#skF_3'))) = k1_mcart_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_403])).

tff(c_79,plain,(
    ! [A_55,B_56,C_57,D_58] : k4_tarski(k3_mcart_1(A_55,B_56,C_57),D_58) = k4_mcart_1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [A_55,B_56,C_57,D_58] : k1_mcart_1(k4_mcart_1(A_55,B_56,C_57,D_58)) = k3_mcart_1(A_55,B_56,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_117,plain,(
    ! [A_76,B_77,C_78,D_79] : k4_tarski(k4_tarski(k4_tarski(A_76,B_77),C_78),D_79) = k4_mcart_1(A_76,B_77,C_78,D_79) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_129,plain,(
    ! [A_76,B_77,C_78,D_79] : k4_tarski(k4_tarski(A_76,B_77),C_78) = k1_mcart_1(k4_mcart_1(A_76,B_77,C_78,D_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_16])).

tff(c_146,plain,(
    ! [A_76,B_77,C_78] : k4_tarski(k4_tarski(A_76,B_77),C_78) = k3_mcart_1(A_76,B_77,C_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_129])).

tff(c_444,plain,(
    ! [C_78] : k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')),k2_mcart_1(k1_mcart_1('#skF_3')),C_78) = k4_tarski(k1_mcart_1('#skF_3'),C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_146])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22,D_23] : k4_tarski(k4_tarski(k4_tarski(A_20,B_21),C_22),D_23) = k4_mcart_1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_155,plain,(
    ! [C_22,D_23,B_81,A_80,C_82] :
      ( k4_mcart_1('#skF_1'(A_80,B_81,C_82),'#skF_2'(A_80,B_81,C_82),C_22,D_23) = k4_tarski(k4_tarski(A_80,C_22),D_23)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_14])).

tff(c_753,plain,(
    ! [C_171,D_175,A_172,C_174,B_173] :
      ( k4_mcart_1('#skF_1'(A_172,B_173,C_174),'#skF_2'(A_172,B_173,C_174),C_171,D_175) = k3_mcart_1(A_172,C_171,D_175)
      | ~ r2_hidden(A_172,k2_zfmisc_1(B_173,C_174)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_155])).

tff(c_20,plain,(
    ! [F_30,G_31,H_32,I_33] :
      ( k4_mcart_1(F_30,G_31,H_32,I_33) != '#skF_3'
      | ~ r2_hidden(I_33,'#skF_7')
      | ~ r2_hidden(H_32,'#skF_6')
      | ~ r2_hidden(G_31,'#skF_5')
      | ~ r2_hidden(F_30,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_846,plain,(
    ! [A_190,C_188,D_189,C_191,B_187] :
      ( k3_mcart_1(A_190,C_188,D_189) != '#skF_3'
      | ~ r2_hidden(D_189,'#skF_7')
      | ~ r2_hidden(C_188,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_190,B_187,C_191),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_190,B_187,C_191),'#skF_4')
      | ~ r2_hidden(A_190,k2_zfmisc_1(B_187,C_191)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_20])).

tff(c_852,plain,(
    ! [C_78,B_187,C_191] :
      ( k4_tarski(k1_mcart_1('#skF_3'),C_78) != '#skF_3'
      | ~ r2_hidden(C_78,'#skF_7')
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')),'#skF_6')
      | ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),B_187,C_191),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),B_187,C_191),'#skF_4')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1(B_187,C_191)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_846])).

tff(c_856,plain,(
    ! [C_78,B_187,C_191] :
      ( k4_tarski(k1_mcart_1('#skF_3'),C_78) != '#skF_3'
      | ~ r2_hidden(C_78,'#skF_7')
      | ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),B_187,C_191),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),B_187,C_191),'#skF_4')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1(B_187,C_191)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_852])).

tff(c_1149,plain,(
    ! [B_232,C_233] :
      ( ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),B_232,C_233),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),B_232,C_233),'#skF_4')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1(B_232,C_233)) ) ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_1152,plain,
    ( ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_339,c_1149])).

tff(c_1156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_373,c_1152])).

tff(c_1179,plain,(
    ! [C_242] :
      ( k4_tarski(k1_mcart_1('#skF_3'),C_242) != '#skF_3'
      | ~ r2_hidden(C_242,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_1182,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_1179])).

tff(c_1186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_1182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:39:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.66  
% 3.29/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.66  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.29/1.66  
% 3.29/1.66  %Foreground sorts:
% 3.29/1.66  
% 3.29/1.66  
% 3.29/1.66  %Background operators:
% 3.29/1.66  
% 3.29/1.66  
% 3.29/1.66  %Foreground operators:
% 3.29/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.29/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.29/1.66  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.29/1.66  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.29/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.66  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.29/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.66  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.29/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.66  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.29/1.66  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.29/1.66  
% 3.64/1.68  tff(f_66, negated_conjecture, ~(![A, B, C, D, E]: ~(r2_hidden(A, k4_zfmisc_1(B, C, D, E)) & (![F, G, H, I]: ~((((r2_hidden(F, B) & r2_hidden(G, C)) & r2_hidden(H, D)) & r2_hidden(I, E)) & (A = k4_mcart_1(F, G, H, I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 3.64/1.68  tff(f_38, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.64/1.68  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.64/1.68  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.64/1.68  tff(f_50, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.64/1.68  tff(f_34, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.64/1.68  tff(f_36, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.64/1.68  tff(f_46, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 3.64/1.68  tff(c_22, plain, (r2_hidden('#skF_3', k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.64/1.68  tff(c_63, plain, (![A_51, B_52, C_53, D_54]: (k2_zfmisc_1(k3_zfmisc_1(A_51, B_52, C_53), D_54)=k4_zfmisc_1(A_51, B_52, C_53, D_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.68  tff(c_10, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.68  tff(c_113, plain, (![C_74, B_72, D_75, A_71, A_73]: (r2_hidden(k2_mcart_1(A_73), D_75) | ~r2_hidden(A_73, k4_zfmisc_1(A_71, B_72, C_74, D_75)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_10])).
% 3.64/1.68  tff(c_116, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_7')), inference(resolution, [status(thm)], [c_22, c_113])).
% 3.64/1.68  tff(c_8, plain, (![A_13, B_14, C_15, D_16]: (k2_zfmisc_1(k3_zfmisc_1(A_13, B_14, C_15), D_16)=k4_zfmisc_1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.68  tff(c_149, plain, (![A_80, B_81, C_82]: (k4_tarski('#skF_1'(A_80, B_81, C_82), '#skF_2'(A_80, B_81, C_82))=A_80 | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.68  tff(c_18, plain, (![A_24, B_25]: (k2_mcart_1(k4_tarski(A_24, B_25))=B_25)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.64/1.68  tff(c_223, plain, (![A_95, B_96, C_97]: (k2_mcart_1(A_95)='#skF_2'(A_95, B_96, C_97) | ~r2_hidden(A_95, k2_zfmisc_1(B_96, C_97)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_18])).
% 3.64/1.68  tff(c_624, plain, (![A_166, A_165, C_167, B_164, D_163]: ('#skF_2'(A_165, k3_zfmisc_1(A_166, B_164, C_167), D_163)=k2_mcart_1(A_165) | ~r2_hidden(A_165, k4_zfmisc_1(A_166, B_164, C_167, D_163)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_223])).
% 3.64/1.68  tff(c_632, plain, ('#skF_2'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k2_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_624])).
% 3.64/1.68  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.68  tff(c_636, plain, (k4_tarski('#skF_1'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7'), k2_mcart_1('#skF_3'))='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_632, c_2])).
% 3.64/1.68  tff(c_640, plain, (k4_tarski('#skF_1'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8, c_636])).
% 3.64/1.68  tff(c_16, plain, (![A_24, B_25]: (k1_mcart_1(k4_tarski(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.64/1.68  tff(c_654, plain, ('#skF_1'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_640, c_16])).
% 3.64/1.68  tff(c_663, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_640])).
% 3.64/1.68  tff(c_12, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.68  tff(c_315, plain, (![A_117, D_119, A_115, B_116, C_118]: (r2_hidden(k1_mcart_1(A_117), k3_zfmisc_1(A_115, B_116, C_118)) | ~r2_hidden(A_117, k4_zfmisc_1(A_115, B_116, C_118, D_119)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_12])).
% 3.64/1.68  tff(c_318, plain, (r2_hidden(k1_mcart_1('#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_315])).
% 3.64/1.68  tff(c_4, plain, (![A_6, B_7, C_8]: (k2_zfmisc_1(k2_zfmisc_1(A_6, B_7), C_8)=k3_zfmisc_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.68  tff(c_56, plain, (![A_41, B_42, C_43]: (r2_hidden(k1_mcart_1(A_41), B_42) | ~r2_hidden(A_41, k2_zfmisc_1(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.68  tff(c_58, plain, (![A_41, A_6, B_7, C_8]: (r2_hidden(k1_mcart_1(A_41), k2_zfmisc_1(A_6, B_7)) | ~r2_hidden(A_41, k3_zfmisc_1(A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_56])).
% 3.64/1.68  tff(c_323, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_318, c_58])).
% 3.64/1.68  tff(c_161, plain, (![A_80, B_81, C_82]: (k2_mcart_1(A_80)='#skF_2'(A_80, B_81, C_82) | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_18])).
% 3.64/1.68  tff(c_335, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')))='#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_323, c_161])).
% 3.64/1.68  tff(c_337, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))), '#skF_5')), inference(resolution, [status(thm)], [c_323, c_10])).
% 3.64/1.68  tff(c_373, plain, (r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_337])).
% 3.64/1.68  tff(c_158, plain, (![A_80, B_81, C_82]: (k1_mcart_1(A_80)='#skF_1'(A_80, B_81, C_82) | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_16])).
% 3.64/1.68  tff(c_336, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')))='#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_323, c_158])).
% 3.64/1.68  tff(c_338, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))), '#skF_4')), inference(resolution, [status(thm)], [c_323, c_12])).
% 3.64/1.68  tff(c_339, plain, (r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_338])).
% 3.64/1.68  tff(c_59, plain, (![A_44, C_45, B_46]: (r2_hidden(k2_mcart_1(A_44), C_45) | ~r2_hidden(A_44, k2_zfmisc_1(B_46, C_45)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.68  tff(c_61, plain, (![A_44, C_8, A_6, B_7]: (r2_hidden(k2_mcart_1(A_44), C_8) | ~r2_hidden(A_44, k3_zfmisc_1(A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 3.64/1.68  tff(c_324, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')), '#skF_6')), inference(resolution, [status(thm)], [c_318, c_61])).
% 3.64/1.68  tff(c_383, plain, (![A_130, A_131, B_132, C_133]: ('#skF_2'(A_130, k2_zfmisc_1(A_131, B_132), C_133)=k2_mcart_1(A_130) | ~r2_hidden(A_130, k3_zfmisc_1(A_131, B_132, C_133)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_223])).
% 3.64/1.68  tff(c_393, plain, ('#skF_2'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k2_mcart_1(k1_mcart_1('#skF_3'))), inference(resolution, [status(thm)], [c_318, c_383])).
% 3.64/1.68  tff(c_399, plain, (k4_tarski('#skF_1'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1(k1_mcart_1('#skF_3')))=k1_mcart_1('#skF_3') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_2])).
% 3.64/1.68  tff(c_403, plain, (k4_tarski('#skF_1'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1(k1_mcart_1('#skF_3')))=k1_mcart_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_4, c_399])).
% 3.64/1.68  tff(c_417, plain, ('#skF_1'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k1_mcart_1(k1_mcart_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_16])).
% 3.64/1.68  tff(c_425, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_3')), k2_mcart_1(k1_mcart_1('#skF_3')))=k1_mcart_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_417, c_403])).
% 3.64/1.68  tff(c_79, plain, (![A_55, B_56, C_57, D_58]: (k4_tarski(k3_mcart_1(A_55, B_56, C_57), D_58)=k4_mcart_1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.64/1.68  tff(c_85, plain, (![A_55, B_56, C_57, D_58]: (k1_mcart_1(k4_mcart_1(A_55, B_56, C_57, D_58))=k3_mcart_1(A_55, B_56, C_57))), inference(superposition, [status(thm), theory('equality')], [c_79, c_16])).
% 3.64/1.68  tff(c_117, plain, (![A_76, B_77, C_78, D_79]: (k4_tarski(k4_tarski(k4_tarski(A_76, B_77), C_78), D_79)=k4_mcart_1(A_76, B_77, C_78, D_79))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.64/1.68  tff(c_129, plain, (![A_76, B_77, C_78, D_79]: (k4_tarski(k4_tarski(A_76, B_77), C_78)=k1_mcart_1(k4_mcart_1(A_76, B_77, C_78, D_79)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_16])).
% 3.64/1.68  tff(c_146, plain, (![A_76, B_77, C_78]: (k4_tarski(k4_tarski(A_76, B_77), C_78)=k3_mcart_1(A_76, B_77, C_78))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_129])).
% 3.64/1.68  tff(c_444, plain, (![C_78]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')), k2_mcart_1(k1_mcart_1('#skF_3')), C_78)=k4_tarski(k1_mcart_1('#skF_3'), C_78))), inference(superposition, [status(thm), theory('equality')], [c_425, c_146])).
% 3.64/1.68  tff(c_14, plain, (![A_20, B_21, C_22, D_23]: (k4_tarski(k4_tarski(k4_tarski(A_20, B_21), C_22), D_23)=k4_mcart_1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.64/1.68  tff(c_155, plain, (![C_22, D_23, B_81, A_80, C_82]: (k4_mcart_1('#skF_1'(A_80, B_81, C_82), '#skF_2'(A_80, B_81, C_82), C_22, D_23)=k4_tarski(k4_tarski(A_80, C_22), D_23) | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_14])).
% 3.64/1.68  tff(c_753, plain, (![C_171, D_175, A_172, C_174, B_173]: (k4_mcart_1('#skF_1'(A_172, B_173, C_174), '#skF_2'(A_172, B_173, C_174), C_171, D_175)=k3_mcart_1(A_172, C_171, D_175) | ~r2_hidden(A_172, k2_zfmisc_1(B_173, C_174)))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_155])).
% 3.64/1.68  tff(c_20, plain, (![F_30, G_31, H_32, I_33]: (k4_mcart_1(F_30, G_31, H_32, I_33)!='#skF_3' | ~r2_hidden(I_33, '#skF_7') | ~r2_hidden(H_32, '#skF_6') | ~r2_hidden(G_31, '#skF_5') | ~r2_hidden(F_30, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.64/1.68  tff(c_846, plain, (![A_190, C_188, D_189, C_191, B_187]: (k3_mcart_1(A_190, C_188, D_189)!='#skF_3' | ~r2_hidden(D_189, '#skF_7') | ~r2_hidden(C_188, '#skF_6') | ~r2_hidden('#skF_2'(A_190, B_187, C_191), '#skF_5') | ~r2_hidden('#skF_1'(A_190, B_187, C_191), '#skF_4') | ~r2_hidden(A_190, k2_zfmisc_1(B_187, C_191)))), inference(superposition, [status(thm), theory('equality')], [c_753, c_20])).
% 3.64/1.68  tff(c_852, plain, (![C_78, B_187, C_191]: (k4_tarski(k1_mcart_1('#skF_3'), C_78)!='#skF_3' | ~r2_hidden(C_78, '#skF_7') | ~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')), '#skF_6') | ~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), B_187, C_191), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), B_187, C_191), '#skF_4') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1(B_187, C_191)))), inference(superposition, [status(thm), theory('equality')], [c_444, c_846])).
% 3.64/1.68  tff(c_856, plain, (![C_78, B_187, C_191]: (k4_tarski(k1_mcart_1('#skF_3'), C_78)!='#skF_3' | ~r2_hidden(C_78, '#skF_7') | ~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), B_187, C_191), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), B_187, C_191), '#skF_4') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1(B_187, C_191)))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_852])).
% 3.64/1.68  tff(c_1149, plain, (![B_232, C_233]: (~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), B_232, C_233), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), B_232, C_233), '#skF_4') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1(B_232, C_233)))), inference(splitLeft, [status(thm)], [c_856])).
% 3.64/1.68  tff(c_1152, plain, (~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_339, c_1149])).
% 3.64/1.68  tff(c_1156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_373, c_1152])).
% 3.64/1.68  tff(c_1179, plain, (![C_242]: (k4_tarski(k1_mcart_1('#skF_3'), C_242)!='#skF_3' | ~r2_hidden(C_242, '#skF_7'))), inference(splitRight, [status(thm)], [c_856])).
% 3.64/1.68  tff(c_1182, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_663, c_1179])).
% 3.64/1.68  tff(c_1186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_1182])).
% 3.64/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.68  
% 3.64/1.68  Inference rules
% 3.64/1.68  ----------------------
% 3.64/1.68  #Ref     : 0
% 3.64/1.68  #Sup     : 302
% 3.64/1.68  #Fact    : 0
% 3.64/1.68  #Define  : 0
% 3.64/1.68  #Split   : 4
% 3.64/1.68  #Chain   : 0
% 3.64/1.68  #Close   : 0
% 3.64/1.68  
% 3.64/1.68  Ordering : KBO
% 3.64/1.68  
% 3.64/1.68  Simplification rules
% 3.64/1.68  ----------------------
% 3.64/1.68  #Subsume      : 37
% 3.64/1.68  #Demod        : 323
% 3.64/1.68  #Tautology    : 182
% 3.64/1.68  #SimpNegUnit  : 0
% 3.64/1.68  #BackRed      : 5
% 3.64/1.68  
% 3.64/1.68  #Partial instantiations: 0
% 3.64/1.68  #Strategies tried      : 1
% 3.64/1.68  
% 3.64/1.68  Timing (in seconds)
% 3.64/1.68  ----------------------
% 3.70/1.68  Preprocessing        : 0.35
% 3.70/1.68  Parsing              : 0.21
% 3.70/1.68  CNF conversion       : 0.02
% 3.70/1.68  Main loop            : 0.58
% 3.70/1.68  Inferencing          : 0.24
% 3.70/1.68  Reduction            : 0.19
% 3.70/1.68  Demodulation         : 0.16
% 3.70/1.68  BG Simplification    : 0.03
% 3.70/1.68  Subsumption          : 0.08
% 3.70/1.68  Abstraction          : 0.03
% 3.70/1.68  MUC search           : 0.00
% 3.70/1.68  Cooper               : 0.00
% 3.70/1.68  Total                : 0.97
% 3.70/1.68  Index Insertion      : 0.00
% 3.70/1.68  Index Deletion       : 0.00
% 3.70/1.68  Index Matching       : 0.00
% 3.70/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
