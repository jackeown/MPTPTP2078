%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:21 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 361 expanded)
%              Number of leaves         :   27 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 ( 657 expanded)
%              Number of equality atoms :   46 ( 228 expanded)
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

tff(f_40,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_46,axiom,(
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

tff(f_36,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(c_22,plain,(
    r2_hidden('#skF_3',k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_103,plain,(
    ! [A_63,B_64,C_65,D_66] : k2_zfmisc_1(k3_zfmisc_1(A_63,B_64,C_65),D_66) = k4_zfmisc_1(A_63,B_64,C_65,D_66) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(k2_mcart_1(A_20),C_22)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_173,plain,(
    ! [A_85,B_83,D_86,A_84,C_82] :
      ( r2_hidden(k2_mcart_1(A_85),D_86)
      | ~ r2_hidden(A_85,k4_zfmisc_1(A_84,B_83,C_82,D_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_12])).

tff(c_176,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_173])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_zfmisc_1(k3_zfmisc_1(A_16,B_17,C_18),D_19) = k4_zfmisc_1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_155,plain,(
    ! [A_79,B_80,C_81] :
      ( k4_tarski('#skF_1'(A_79,B_80,C_81),'#skF_2'(A_79,B_80,C_81)) = A_79
      | ~ r2_hidden(A_79,k2_zfmisc_1(B_80,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_23,B_24] : k1_mcart_1(k4_tarski(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_177,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_mcart_1(A_87) = '#skF_1'(A_87,B_88,C_89)
      | ~ r2_hidden(A_87,k2_zfmisc_1(B_88,C_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_16])).

tff(c_607,plain,(
    ! [C_160,A_156,A_158,D_159,B_157] :
      ( '#skF_1'(A_156,k3_zfmisc_1(A_158,B_157,C_160),D_159) = k1_mcart_1(A_156)
      | ~ r2_hidden(A_156,k4_zfmisc_1(A_158,B_157,C_160,D_159)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_177])).

tff(c_615,plain,(
    '#skF_1'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7') = k1_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_607])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_622,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_2'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_2])).

tff(c_628,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_2'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_10,c_622])).

tff(c_18,plain,(
    ! [A_23,B_24] : k2_mcart_1(k4_tarski(A_23,B_24)) = B_24 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_645,plain,(
    '#skF_2'('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7') = k2_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_18])).

tff(c_651,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_628])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(k1_mcart_1(A_20),B_21)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_309,plain,(
    ! [C_115,A_117,D_119,A_118,B_116] :
      ( r2_hidden(k1_mcart_1(A_118),k3_zfmisc_1(A_117,B_116,C_115))
      | ~ r2_hidden(A_118,k4_zfmisc_1(A_117,B_116,C_115,D_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_14])).

tff(c_312,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_22,c_309])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k1_mcart_1(A_40),B_41)
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_41,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    ! [A_40,A_9,B_10,C_11] :
      ( r2_hidden(k1_mcart_1(A_40),k2_zfmisc_1(A_9,B_10))
      | ~ r2_hidden(A_40,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_317,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_312,c_58])).

tff(c_167,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_mcart_1(A_79) = '#skF_2'(A_79,B_80,C_81)
      | ~ r2_hidden(A_79,k2_zfmisc_1(B_80,C_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_18])).

tff(c_329,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))) = '#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_317,c_167])).

tff(c_331,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_317,c_12])).

tff(c_363,plain,(
    r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_331])).

tff(c_164,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_mcart_1(A_79) = '#skF_1'(A_79,B_80,C_81)
      | ~ r2_hidden(A_79,k2_zfmisc_1(B_80,C_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_16])).

tff(c_330,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))) = '#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_317,c_164])).

tff(c_332,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_317,c_14])).

tff(c_333,plain,(
    r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_332])).

tff(c_98,plain,(
    ! [A_52,C_53,B_54] :
      ( r2_hidden(k2_mcart_1(A_52),C_53)
      | ~ r2_hidden(A_52,k2_zfmisc_1(B_54,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_100,plain,(
    ! [A_52,C_11,A_9,B_10] :
      ( r2_hidden(k2_mcart_1(A_52),C_11)
      | ~ r2_hidden(A_52,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_318,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_312,c_100])).

tff(c_184,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_mcart_1(A_90) = '#skF_2'(A_90,B_91,C_92)
      | ~ r2_hidden(A_90,k2_zfmisc_1(B_91,C_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_18])).

tff(c_368,plain,(
    ! [A_124,A_125,B_126,C_127] :
      ( '#skF_2'(A_124,k2_zfmisc_1(A_125,B_126),C_127) = k2_mcart_1(A_124)
      | ~ r2_hidden(A_124,k3_zfmisc_1(A_125,B_126,C_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_184])).

tff(c_378,plain,(
    '#skF_2'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k2_mcart_1(k1_mcart_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_312,c_368])).

tff(c_387,plain,
    ( k4_tarski('#skF_1'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1(k1_mcart_1('#skF_3'))) = k1_mcart_1('#skF_3')
    | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_2])).

tff(c_393,plain,(
    k4_tarski('#skF_1'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1(k1_mcart_1('#skF_3'))) = k1_mcart_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_6,c_387])).

tff(c_404,plain,(
    '#skF_1'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k1_mcart_1(k1_mcart_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_16])).

tff(c_4,plain,(
    ! [A_6,B_7,C_8] : k4_tarski(k4_tarski(A_6,B_7),C_8) = k3_mcart_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_161,plain,(
    ! [A_79,B_80,C_81,C_8] :
      ( k3_mcart_1('#skF_1'(A_79,B_80,C_81),'#skF_2'(A_79,B_80,C_81),C_8) = k4_tarski(A_79,C_8)
      | ~ r2_hidden(A_79,k2_zfmisc_1(B_80,C_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_4])).

tff(c_416,plain,(
    ! [C_8] :
      ( k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_2'(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),C_8) = k4_tarski(k1_mcart_1('#skF_3'),C_8)
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_161])).

tff(c_423,plain,(
    ! [C_8] : k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')),k2_mcart_1(k1_mcart_1('#skF_3')),C_8) = k4_tarski(k1_mcart_1('#skF_3'),C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_6,c_378,c_416])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14,D_15] : k4_tarski(k3_mcart_1(A_12,B_13,C_14),D_15) = k4_mcart_1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_43,B_44,C_45] : k4_tarski(k4_tarski(A_43,B_44),C_45) = k3_mcart_1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_6,B_7,C_8,C_45] : k3_mcart_1(k4_tarski(A_6,B_7),C_8,C_45) = k4_tarski(k3_mcart_1(A_6,B_7,C_8),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_217,plain,(
    ! [A_101,B_102,C_103,C_104] : k3_mcart_1(k4_tarski(A_101,B_102),C_103,C_104) = k4_mcart_1(A_101,B_102,C_103,C_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_819,plain,(
    ! [C_185,C_181,C_183,B_182,A_184] :
      ( k4_mcart_1('#skF_1'(A_184,B_182,C_183),'#skF_2'(A_184,B_182,C_183),C_185,C_181) = k3_mcart_1(A_184,C_185,C_181)
      | ~ r2_hidden(A_184,k2_zfmisc_1(B_182,C_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_20,plain,(
    ! [F_29,G_30,H_31,I_32] :
      ( k4_mcart_1(F_29,G_30,H_31,I_32) != '#skF_3'
      | ~ r2_hidden(I_32,'#skF_7')
      | ~ r2_hidden(H_31,'#skF_6')
      | ~ r2_hidden(G_30,'#skF_5')
      | ~ r2_hidden(F_29,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_971,plain,(
    ! [C_200,B_199,A_203,C_202,C_201] :
      ( k3_mcart_1(A_203,C_202,C_201) != '#skF_3'
      | ~ r2_hidden(C_201,'#skF_7')
      | ~ r2_hidden(C_202,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_203,B_199,C_200),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_203,B_199,C_200),'#skF_4')
      | ~ r2_hidden(A_203,k2_zfmisc_1(B_199,C_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_20])).

tff(c_977,plain,(
    ! [C_8,B_199,C_200] :
      ( k4_tarski(k1_mcart_1('#skF_3'),C_8) != '#skF_3'
      | ~ r2_hidden(C_8,'#skF_7')
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')),'#skF_6')
      | ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),B_199,C_200),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),B_199,C_200),'#skF_4')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1(B_199,C_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_971])).

tff(c_985,plain,(
    ! [C_8,B_199,C_200] :
      ( k4_tarski(k1_mcart_1('#skF_3'),C_8) != '#skF_3'
      | ~ r2_hidden(C_8,'#skF_7')
      | ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),B_199,C_200),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),B_199,C_200),'#skF_4')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1(B_199,C_200)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_977])).

tff(c_1149,plain,(
    ! [B_242,C_243] :
      ( ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),B_242,C_243),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')),B_242,C_243),'#skF_4')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1(B_242,C_243)) ) ),
    inference(splitLeft,[status(thm)],[c_985])).

tff(c_1152,plain,
    ( ~ r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_333,c_1149])).

tff(c_1156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_363,c_1152])).

tff(c_1158,plain,(
    ! [C_244] :
      ( k4_tarski(k1_mcart_1('#skF_3'),C_244) != '#skF_3'
      | ~ r2_hidden(C_244,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_985])).

tff(c_1161,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_1158])).

tff(c_1165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_1161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:50:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.59  
% 3.47/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.59  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.47/1.59  
% 3.47/1.59  %Foreground sorts:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Background operators:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Foreground operators:
% 3.47/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.47/1.59  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.47/1.59  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.47/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.47/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.47/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.47/1.59  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.59  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.47/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.59  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.47/1.59  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.47/1.59  
% 3.47/1.61  tff(f_66, negated_conjecture, ~(![A, B, C, D, E]: ~(r2_hidden(A, k4_zfmisc_1(B, C, D, E)) & (![F, G, H, I]: ~((((r2_hidden(F, B) & r2_hidden(G, C)) & r2_hidden(H, D)) & r2_hidden(I, E)) & (A = k4_mcart_1(F, G, H, I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 3.47/1.61  tff(f_40, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.47/1.61  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.47/1.61  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.47/1.61  tff(f_50, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.47/1.61  tff(f_36, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.47/1.61  tff(f_34, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.47/1.61  tff(f_38, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.47/1.61  tff(c_22, plain, (r2_hidden('#skF_3', k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.61  tff(c_103, plain, (![A_63, B_64, C_65, D_66]: (k2_zfmisc_1(k3_zfmisc_1(A_63, B_64, C_65), D_66)=k4_zfmisc_1(A_63, B_64, C_65, D_66))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.47/1.61  tff(c_12, plain, (![A_20, C_22, B_21]: (r2_hidden(k2_mcart_1(A_20), C_22) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.61  tff(c_173, plain, (![A_85, B_83, D_86, A_84, C_82]: (r2_hidden(k2_mcart_1(A_85), D_86) | ~r2_hidden(A_85, k4_zfmisc_1(A_84, B_83, C_82, D_86)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_12])).
% 3.47/1.61  tff(c_176, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_7')), inference(resolution, [status(thm)], [c_22, c_173])).
% 3.47/1.61  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_zfmisc_1(k3_zfmisc_1(A_16, B_17, C_18), D_19)=k4_zfmisc_1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.47/1.61  tff(c_155, plain, (![A_79, B_80, C_81]: (k4_tarski('#skF_1'(A_79, B_80, C_81), '#skF_2'(A_79, B_80, C_81))=A_79 | ~r2_hidden(A_79, k2_zfmisc_1(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.61  tff(c_16, plain, (![A_23, B_24]: (k1_mcart_1(k4_tarski(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.61  tff(c_177, plain, (![A_87, B_88, C_89]: (k1_mcart_1(A_87)='#skF_1'(A_87, B_88, C_89) | ~r2_hidden(A_87, k2_zfmisc_1(B_88, C_89)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_16])).
% 3.47/1.61  tff(c_607, plain, (![C_160, A_156, A_158, D_159, B_157]: ('#skF_1'(A_156, k3_zfmisc_1(A_158, B_157, C_160), D_159)=k1_mcart_1(A_156) | ~r2_hidden(A_156, k4_zfmisc_1(A_158, B_157, C_160, D_159)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_177])).
% 3.47/1.61  tff(c_615, plain, ('#skF_1'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k1_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_607])).
% 3.47/1.61  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.61  tff(c_622, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_2'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7'))='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_2])).
% 3.47/1.61  tff(c_628, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_2'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_10, c_622])).
% 3.47/1.61  tff(c_18, plain, (![A_23, B_24]: (k2_mcart_1(k4_tarski(A_23, B_24))=B_24)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.61  tff(c_645, plain, ('#skF_2'('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7')=k2_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_628, c_18])).
% 3.47/1.61  tff(c_651, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_645, c_628])).
% 3.47/1.61  tff(c_14, plain, (![A_20, B_21, C_22]: (r2_hidden(k1_mcart_1(A_20), B_21) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.61  tff(c_309, plain, (![C_115, A_117, D_119, A_118, B_116]: (r2_hidden(k1_mcart_1(A_118), k3_zfmisc_1(A_117, B_116, C_115)) | ~r2_hidden(A_118, k4_zfmisc_1(A_117, B_116, C_115, D_119)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_14])).
% 3.47/1.61  tff(c_312, plain, (r2_hidden(k1_mcart_1('#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_309])).
% 3.47/1.61  tff(c_6, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.47/1.61  tff(c_56, plain, (![A_40, B_41, C_42]: (r2_hidden(k1_mcart_1(A_40), B_41) | ~r2_hidden(A_40, k2_zfmisc_1(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.61  tff(c_58, plain, (![A_40, A_9, B_10, C_11]: (r2_hidden(k1_mcart_1(A_40), k2_zfmisc_1(A_9, B_10)) | ~r2_hidden(A_40, k3_zfmisc_1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_56])).
% 3.47/1.61  tff(c_317, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_312, c_58])).
% 3.47/1.61  tff(c_167, plain, (![A_79, B_80, C_81]: (k2_mcart_1(A_79)='#skF_2'(A_79, B_80, C_81) | ~r2_hidden(A_79, k2_zfmisc_1(B_80, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_18])).
% 3.47/1.61  tff(c_329, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')))='#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_317, c_167])).
% 3.47/1.61  tff(c_331, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))), '#skF_5')), inference(resolution, [status(thm)], [c_317, c_12])).
% 3.47/1.61  tff(c_363, plain, (r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_331])).
% 3.47/1.61  tff(c_164, plain, (![A_79, B_80, C_81]: (k1_mcart_1(A_79)='#skF_1'(A_79, B_80, C_81) | ~r2_hidden(A_79, k2_zfmisc_1(B_80, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_16])).
% 3.47/1.61  tff(c_330, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')))='#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_317, c_164])).
% 3.47/1.61  tff(c_332, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3'))), '#skF_4')), inference(resolution, [status(thm)], [c_317, c_14])).
% 3.47/1.61  tff(c_333, plain, (r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_332])).
% 3.47/1.61  tff(c_98, plain, (![A_52, C_53, B_54]: (r2_hidden(k2_mcart_1(A_52), C_53) | ~r2_hidden(A_52, k2_zfmisc_1(B_54, C_53)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.61  tff(c_100, plain, (![A_52, C_11, A_9, B_10]: (r2_hidden(k2_mcart_1(A_52), C_11) | ~r2_hidden(A_52, k3_zfmisc_1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_98])).
% 3.47/1.61  tff(c_318, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')), '#skF_6')), inference(resolution, [status(thm)], [c_312, c_100])).
% 3.47/1.61  tff(c_184, plain, (![A_90, B_91, C_92]: (k2_mcart_1(A_90)='#skF_2'(A_90, B_91, C_92) | ~r2_hidden(A_90, k2_zfmisc_1(B_91, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_18])).
% 3.47/1.61  tff(c_368, plain, (![A_124, A_125, B_126, C_127]: ('#skF_2'(A_124, k2_zfmisc_1(A_125, B_126), C_127)=k2_mcart_1(A_124) | ~r2_hidden(A_124, k3_zfmisc_1(A_125, B_126, C_127)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_184])).
% 3.47/1.61  tff(c_378, plain, ('#skF_2'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k2_mcart_1(k1_mcart_1('#skF_3'))), inference(resolution, [status(thm)], [c_312, c_368])).
% 3.47/1.61  tff(c_387, plain, (k4_tarski('#skF_1'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1(k1_mcart_1('#skF_3')))=k1_mcart_1('#skF_3') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_2])).
% 3.47/1.61  tff(c_393, plain, (k4_tarski('#skF_1'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1(k1_mcart_1('#skF_3')))=k1_mcart_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_6, c_387])).
% 3.47/1.61  tff(c_404, plain, ('#skF_1'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k1_mcart_1(k1_mcart_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_16])).
% 3.47/1.61  tff(c_4, plain, (![A_6, B_7, C_8]: (k4_tarski(k4_tarski(A_6, B_7), C_8)=k3_mcart_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.47/1.61  tff(c_161, plain, (![A_79, B_80, C_81, C_8]: (k3_mcart_1('#skF_1'(A_79, B_80, C_81), '#skF_2'(A_79, B_80, C_81), C_8)=k4_tarski(A_79, C_8) | ~r2_hidden(A_79, k2_zfmisc_1(B_80, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_4])).
% 3.47/1.61  tff(c_416, plain, (![C_8]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_2'(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), C_8)=k4_tarski(k1_mcart_1('#skF_3'), C_8) | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_404, c_161])).
% 3.47/1.61  tff(c_423, plain, (![C_8]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_3')), k2_mcart_1(k1_mcart_1('#skF_3')), C_8)=k4_tarski(k1_mcart_1('#skF_3'), C_8))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_6, c_378, c_416])).
% 3.47/1.61  tff(c_8, plain, (![A_12, B_13, C_14, D_15]: (k4_tarski(k3_mcart_1(A_12, B_13, C_14), D_15)=k4_mcart_1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.61  tff(c_59, plain, (![A_43, B_44, C_45]: (k4_tarski(k4_tarski(A_43, B_44), C_45)=k3_mcart_1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.47/1.61  tff(c_74, plain, (![A_6, B_7, C_8, C_45]: (k3_mcart_1(k4_tarski(A_6, B_7), C_8, C_45)=k4_tarski(k3_mcart_1(A_6, B_7, C_8), C_45))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 3.47/1.61  tff(c_217, plain, (![A_101, B_102, C_103, C_104]: (k3_mcart_1(k4_tarski(A_101, B_102), C_103, C_104)=k4_mcart_1(A_101, B_102, C_103, C_104))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_74])).
% 3.47/1.61  tff(c_819, plain, (![C_185, C_181, C_183, B_182, A_184]: (k4_mcart_1('#skF_1'(A_184, B_182, C_183), '#skF_2'(A_184, B_182, C_183), C_185, C_181)=k3_mcart_1(A_184, C_185, C_181) | ~r2_hidden(A_184, k2_zfmisc_1(B_182, C_183)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_217])).
% 3.47/1.61  tff(c_20, plain, (![F_29, G_30, H_31, I_32]: (k4_mcart_1(F_29, G_30, H_31, I_32)!='#skF_3' | ~r2_hidden(I_32, '#skF_7') | ~r2_hidden(H_31, '#skF_6') | ~r2_hidden(G_30, '#skF_5') | ~r2_hidden(F_29, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.61  tff(c_971, plain, (![C_200, B_199, A_203, C_202, C_201]: (k3_mcart_1(A_203, C_202, C_201)!='#skF_3' | ~r2_hidden(C_201, '#skF_7') | ~r2_hidden(C_202, '#skF_6') | ~r2_hidden('#skF_2'(A_203, B_199, C_200), '#skF_5') | ~r2_hidden('#skF_1'(A_203, B_199, C_200), '#skF_4') | ~r2_hidden(A_203, k2_zfmisc_1(B_199, C_200)))), inference(superposition, [status(thm), theory('equality')], [c_819, c_20])).
% 3.47/1.61  tff(c_977, plain, (![C_8, B_199, C_200]: (k4_tarski(k1_mcart_1('#skF_3'), C_8)!='#skF_3' | ~r2_hidden(C_8, '#skF_7') | ~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')), '#skF_6') | ~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), B_199, C_200), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), B_199, C_200), '#skF_4') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1(B_199, C_200)))), inference(superposition, [status(thm), theory('equality')], [c_423, c_971])).
% 3.47/1.61  tff(c_985, plain, (![C_8, B_199, C_200]: (k4_tarski(k1_mcart_1('#skF_3'), C_8)!='#skF_3' | ~r2_hidden(C_8, '#skF_7') | ~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), B_199, C_200), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), B_199, C_200), '#skF_4') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1(B_199, C_200)))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_977])).
% 3.47/1.61  tff(c_1149, plain, (![B_242, C_243]: (~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), B_242, C_243), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_3')), B_242, C_243), '#skF_4') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1(B_242, C_243)))), inference(splitLeft, [status(thm)], [c_985])).
% 3.47/1.61  tff(c_1152, plain, (~r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_333, c_1149])).
% 3.47/1.61  tff(c_1156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_363, c_1152])).
% 3.47/1.61  tff(c_1158, plain, (![C_244]: (k4_tarski(k1_mcart_1('#skF_3'), C_244)!='#skF_3' | ~r2_hidden(C_244, '#skF_7'))), inference(splitRight, [status(thm)], [c_985])).
% 3.47/1.61  tff(c_1161, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_651, c_1158])).
% 3.47/1.61  tff(c_1165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_1161])).
% 3.47/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  Inference rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Ref     : 0
% 3.47/1.61  #Sup     : 299
% 3.47/1.61  #Fact    : 0
% 3.47/1.61  #Define  : 0
% 3.47/1.61  #Split   : 3
% 3.47/1.61  #Chain   : 0
% 3.47/1.61  #Close   : 0
% 3.47/1.61  
% 3.47/1.61  Ordering : KBO
% 3.47/1.61  
% 3.47/1.61  Simplification rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Subsume      : 36
% 3.47/1.61  #Demod        : 311
% 3.47/1.61  #Tautology    : 172
% 3.47/1.61  #SimpNegUnit  : 0
% 3.47/1.61  #BackRed      : 4
% 3.47/1.61  
% 3.47/1.61  #Partial instantiations: 0
% 3.47/1.61  #Strategies tried      : 1
% 3.47/1.61  
% 3.47/1.61  Timing (in seconds)
% 3.47/1.61  ----------------------
% 3.47/1.61  Preprocessing        : 0.29
% 3.47/1.61  Parsing              : 0.16
% 3.47/1.61  CNF conversion       : 0.02
% 3.47/1.61  Main loop            : 0.56
% 3.47/1.61  Inferencing          : 0.23
% 3.47/1.61  Reduction            : 0.19
% 3.47/1.61  Demodulation         : 0.16
% 3.47/1.61  BG Simplification    : 0.03
% 3.47/1.61  Subsumption          : 0.08
% 3.47/1.61  Abstraction          : 0.03
% 3.47/1.61  MUC search           : 0.00
% 3.47/1.61  Cooper               : 0.00
% 3.47/1.61  Total                : 0.89
% 3.47/1.61  Index Insertion      : 0.00
% 3.47/1.61  Index Deletion       : 0.00
% 3.47/1.61  Index Matching       : 0.00
% 3.47/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
