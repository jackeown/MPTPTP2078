%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:21 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  101 (1236 expanded)
%              Number of leaves         :   31 ( 438 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 (1954 expanded)
%              Number of equality atoms :   56 (1104 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ~ ( r2_hidden(A,k4_zfmisc_1(B,C,D,E))
          & ! [F,G,H,I] :
              ~ ( r2_hidden(F,B)
                & r2_hidden(G,C)
                & r2_hidden(H,D)
                & r2_hidden(I,E)
                & A = k4_mcart_1(F,G,H,I) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_mcart_1)).

tff(f_36,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
        & ! [E,F,G] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & r2_hidden(G,D)
              & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(c_30,plain,(
    r2_hidden('#skF_6',k4_zfmisc_1('#skF_7','#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_19,B_20),C_21),D_22) = k4_zfmisc_1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_zfmisc_1(k3_zfmisc_1(A_19,B_20,C_21),D_22) = k4_zfmisc_1(A_19,B_20,C_21,D_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_53,plain,(
    ! [A_50,B_51,C_52] : k2_zfmisc_1(k2_zfmisc_1(A_50,B_51),C_52) = k3_zfmisc_1(A_50,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_9,B_10,C_11,C_52] : k3_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11,C_52) = k2_zfmisc_1(k3_zfmisc_1(A_9,B_10,C_11),C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_53])).

tff(c_239,plain,(
    ! [A_9,B_10,C_11,C_52] : k3_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11,C_52) = k4_zfmisc_1(A_9,B_10,C_11,C_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_66])).

tff(c_394,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k3_mcart_1('#skF_3'(A_129,B_130,C_131,D_132),'#skF_4'(A_129,B_130,C_131,D_132),'#skF_5'(A_129,B_130,C_131,D_132)) = A_129
      | ~ r2_hidden(A_129,k3_zfmisc_1(B_130,C_131,D_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_53,B_54,C_55] : k4_tarski(k4_tarski(A_53,B_54),C_55) = k3_mcart_1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_30,B_31] : k2_mcart_1(k4_tarski(A_30,B_31)) = B_31 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    ! [A_53,B_54,C_55] : k2_mcart_1(k3_mcart_1(A_53,B_54,C_55)) = C_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_26])).

tff(c_417,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k2_mcart_1(A_133) = '#skF_5'(A_133,B_134,C_135,D_136)
      | ~ r2_hidden(A_133,k3_zfmisc_1(B_134,C_135,D_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_84])).

tff(c_1252,plain,(
    ! [C_225,C_224,A_226,A_222,B_223] :
      ( '#skF_5'(A_222,k2_zfmisc_1(A_226,B_223),C_225,C_224) = k2_mcart_1(A_222)
      | ~ r2_hidden(A_222,k4_zfmisc_1(A_226,B_223,C_225,C_224)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_417])).

tff(c_1299,plain,(
    '#skF_5'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10') = k2_mcart_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_1252])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k3_mcart_1('#skF_3'(A_23,B_24,C_25,D_26),'#skF_4'(A_23,B_24,C_25,D_26),'#skF_5'(A_23,B_24,C_25,D_26)) = A_23
      | ~ r2_hidden(A_23,k3_zfmisc_1(B_24,C_25,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1303,plain,
    ( k3_mcart_1('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_4'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ r2_hidden('#skF_6',k3_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_16])).

tff(c_1310,plain,(
    k3_mcart_1('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_4'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_239,c_1303])).

tff(c_24,plain,(
    ! [A_30,B_31] : k1_mcart_1(k4_tarski(A_30,B_31)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_53,B_54,C_55] : k1_mcart_1(k3_mcart_1(A_53,B_54,C_55)) = k4_tarski(A_53,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_24])).

tff(c_1411,plain,(
    k4_tarski('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_4'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10')) = k1_mcart_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_81])).

tff(c_1509,plain,(
    k1_mcart_1(k1_mcart_1('#skF_6')) = '#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_24])).

tff(c_149,plain,(
    ! [A_82,B_83,C_84,D_85] : k2_zfmisc_1(k3_zfmisc_1(A_82,B_83,C_84),D_85) = k4_zfmisc_1(A_82,B_83,C_84,D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(A_12),B_13)
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_353,plain,(
    ! [A_124,C_126,A_128,D_125,B_127] :
      ( r2_hidden(k1_mcart_1(A_124),k3_zfmisc_1(A_128,B_127,C_126))
      | ~ r2_hidden(A_124,k4_zfmisc_1(A_128,B_127,C_126,D_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_10])).

tff(c_368,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_30,c_353])).

tff(c_63,plain,(
    ! [A_12,A_50,B_51,C_52] :
      ( r2_hidden(k1_mcart_1(A_12),k2_zfmisc_1(A_50,B_51))
      | ~ r2_hidden(A_12,k3_zfmisc_1(A_50,B_51,C_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_373,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_368,c_63])).

tff(c_1525,plain,(
    r2_hidden('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_373])).

tff(c_286,plain,(
    ! [A_115,B_116,C_117] :
      ( k4_tarski('#skF_1'(A_115,B_116,C_117),'#skF_2'(A_115,B_116,C_117)) = A_115
      | ~ r2_hidden(A_115,k2_zfmisc_1(B_116,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_298,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_mcart_1(A_115) = '#skF_1'(A_115,B_116,C_117)
      | ~ r2_hidden(A_115,k2_zfmisc_1(B_116,C_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_24])).

tff(c_386,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = '#skF_1'(k1_mcart_1(k1_mcart_1('#skF_6')),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_373,c_298])).

tff(c_1522,plain,(
    k1_mcart_1('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10')) = '#skF_1'('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1509,c_386])).

tff(c_1794,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( k4_tarski('#skF_3'(A_255,B_256,C_257,D_258),'#skF_4'(A_255,B_256,C_257,D_258)) = k1_mcart_1(A_255)
      | ~ r2_hidden(A_255,k3_zfmisc_1(B_256,C_257,D_258)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_81])).

tff(c_1825,plain,(
    ! [A_259,B_260,C_261,D_262] :
      ( k1_mcart_1(k1_mcart_1(A_259)) = '#skF_3'(A_259,B_260,C_261,D_262)
      | ~ r2_hidden(A_259,k3_zfmisc_1(B_260,C_261,D_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1794,c_24])).

tff(c_1855,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = '#skF_3'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_368,c_1825])).

tff(c_1881,plain,(
    '#skF_1'('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_7','#skF_8') = '#skF_3'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1522,c_1509,c_1855])).

tff(c_388,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_373,c_10])).

tff(c_412,plain,(
    r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_6')),'#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_388])).

tff(c_1521,plain,(
    r2_hidden('#skF_1'('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_412])).

tff(c_1948,plain,(
    r2_hidden('#skF_3'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1521])).

tff(c_301,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_mcart_1(A_115) = '#skF_2'(A_115,B_116,C_117)
      | ~ r2_hidden(A_115,k2_zfmisc_1(B_116,C_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_26])).

tff(c_385,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = '#skF_2'(k1_mcart_1(k1_mcart_1('#skF_6')),'#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_373,c_301])).

tff(c_1524,plain,(
    k2_mcart_1('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10')) = '#skF_2'('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1509,c_385])).

tff(c_1886,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( k2_mcart_1(k1_mcart_1(A_263)) = '#skF_4'(A_263,B_264,C_265,D_266)
      | ~ r2_hidden(A_263,k3_zfmisc_1(B_264,C_265,D_266)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1794,c_26])).

tff(c_1916,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = '#skF_4'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_368,c_1886])).

tff(c_1942,plain,(
    '#skF_2'('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_7','#skF_8') = '#skF_4'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_1509,c_1916])).

tff(c_8,plain,(
    ! [A_12,C_14,B_13] :
      ( r2_hidden(k2_mcart_1(A_12),C_14)
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_387,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))),'#skF_8') ),
    inference(resolution,[status(thm)],[c_373,c_8])).

tff(c_389,plain,(
    r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_6')),'#skF_7','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_387])).

tff(c_1523,plain,(
    r2_hidden('#skF_2'('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_7','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_389])).

tff(c_1974,plain,(
    r2_hidden('#skF_4'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1942,c_1523])).

tff(c_436,plain,(
    k2_mcart_1(k1_mcart_1('#skF_6')) = '#skF_5'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_368,c_417])).

tff(c_61,plain,(
    ! [A_12,C_52,A_50,B_51] :
      ( r2_hidden(k2_mcart_1(A_12),C_52)
      | ~ r2_hidden(A_12,k3_zfmisc_1(A_50,B_51,C_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_374,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_368,c_61])).

tff(c_440,plain,(
    r2_hidden('#skF_5'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_374])).

tff(c_1512,plain,(
    k2_mcart_1(k1_mcart_1('#skF_6')) = '#skF_4'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_26])).

tff(c_1515,plain,(
    '#skF_4'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10') = '#skF_5'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_1512])).

tff(c_178,plain,(
    ! [C_92,D_91,B_93,A_94,A_90] :
      ( r2_hidden(k2_mcart_1(A_90),D_91)
      | ~ r2_hidden(A_90,k4_zfmisc_1(A_94,B_93,C_92,D_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_8])).

tff(c_185,plain,(
    r2_hidden(k2_mcart_1('#skF_6'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_178])).

tff(c_4,plain,(
    ! [A_6,B_7,C_8] : k4_tarski(k4_tarski(A_6,B_7),C_8) = k3_mcart_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_18] : k4_tarski(k4_tarski(k4_tarski(A_15,B_16),C_17),D_18) = k4_mcart_1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_15,B_16,C_17,D_18] : k4_tarski(k3_mcart_1(A_15,B_16,C_17),D_18) = k4_mcart_1(A_15,B_16,C_17,D_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_75,plain,(
    ! [A_53,B_54,C_55,C_8] : k3_mcart_1(k4_tarski(A_53,B_54),C_55,C_8) = k4_tarski(k3_mcart_1(A_53,B_54,C_55),C_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_212,plain,(
    ! [A_53,B_54,C_55,C_8] : k3_mcart_1(k4_tarski(A_53,B_54),C_55,C_8) = k4_mcart_1(A_53,B_54,C_55,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_2254,plain,(
    ! [C_299,C_297,B_300,A_301,C_298] :
      ( k4_mcart_1('#skF_1'(A_301,B_300,C_298),'#skF_2'(A_301,B_300,C_298),C_297,C_299) = k3_mcart_1(A_301,C_297,C_299)
      | ~ r2_hidden(A_301,k2_zfmisc_1(B_300,C_298)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_212])).

tff(c_28,plain,(
    ! [F_36,G_37,H_38,I_39] :
      ( k4_mcart_1(F_36,G_37,H_38,I_39) != '#skF_6'
      | ~ r2_hidden(I_39,'#skF_10')
      | ~ r2_hidden(H_38,'#skF_9')
      | ~ r2_hidden(G_37,'#skF_8')
      | ~ r2_hidden(F_36,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2313,plain,(
    ! [C_305,C_302,A_306,C_304,B_303] :
      ( k3_mcart_1(A_306,C_305,C_302) != '#skF_6'
      | ~ r2_hidden(C_302,'#skF_10')
      | ~ r2_hidden(C_305,'#skF_9')
      | ~ r2_hidden('#skF_2'(A_306,B_303,C_304),'#skF_8')
      | ~ r2_hidden('#skF_1'(A_306,B_303,C_304),'#skF_7')
      | ~ r2_hidden(A_306,k2_zfmisc_1(B_303,C_304)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2254,c_28])).

tff(c_5518,plain,(
    ! [D_528,B_526,C_525,A_530,C_527,B_529] :
      ( A_530 != '#skF_6'
      | ~ r2_hidden('#skF_5'(A_530,B_526,C_525,D_528),'#skF_10')
      | ~ r2_hidden('#skF_4'(A_530,B_526,C_525,D_528),'#skF_9')
      | ~ r2_hidden('#skF_2'('#skF_3'(A_530,B_526,C_525,D_528),B_529,C_527),'#skF_8')
      | ~ r2_hidden('#skF_1'('#skF_3'(A_530,B_526,C_525,D_528),B_529,C_527),'#skF_7')
      | ~ r2_hidden('#skF_3'(A_530,B_526,C_525,D_528),k2_zfmisc_1(B_529,C_527))
      | ~ r2_hidden(A_530,k3_zfmisc_1(B_526,C_525,D_528)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2313])).

tff(c_5521,plain,
    ( ~ r2_hidden('#skF_5'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_10')
    | ~ r2_hidden('#skF_4'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_2'('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),'#skF_7','#skF_8'),'#skF_8')
    | ~ r2_hidden('#skF_3'(k1_mcart_1('#skF_6'),'#skF_7','#skF_8','#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10'),k2_zfmisc_1('#skF_7','#skF_8'))
    | ~ r2_hidden('#skF_6',k3_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'),'#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_5518])).

tff(c_5525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_239,c_1525,c_1948,c_1974,c_1942,c_440,c_1515,c_185,c_1299,c_5521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.72/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.70  
% 7.74/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.71  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3
% 7.74/2.71  
% 7.74/2.71  %Foreground sorts:
% 7.74/2.71  
% 7.74/2.71  
% 7.74/2.71  %Background operators:
% 7.74/2.71  
% 7.74/2.71  
% 7.74/2.71  %Foreground operators:
% 7.74/2.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.74/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.74/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.74/2.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.74/2.71  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.74/2.71  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 7.74/2.71  tff('#skF_7', type, '#skF_7': $i).
% 7.74/2.71  tff('#skF_10', type, '#skF_10': $i).
% 7.74/2.71  tff('#skF_6', type, '#skF_6': $i).
% 7.74/2.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.74/2.71  tff('#skF_9', type, '#skF_9': $i).
% 7.74/2.71  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.74/2.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.74/2.71  tff('#skF_8', type, '#skF_8': $i).
% 7.74/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.74/2.71  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.74/2.71  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.74/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.74/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.74/2.71  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.74/2.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.74/2.71  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 7.74/2.71  
% 7.74/2.73  tff(f_79, negated_conjecture, ~(![A, B, C, D, E]: ~(r2_hidden(A, k4_zfmisc_1(B, C, D, E)) & (![F, G, H, I]: ~((((r2_hidden(F, B) & r2_hidden(G, C)) & r2_hidden(H, D)) & r2_hidden(I, E)) & (A = k4_mcart_1(F, G, H, I)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_mcart_1)).
% 7.74/2.73  tff(f_36, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.74/2.73  tff(f_46, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 7.74/2.73  tff(f_59, axiom, (![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 7.74/2.73  tff(f_34, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 7.74/2.73  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.74/2.73  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.74/2.73  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 7.74/2.73  tff(f_44, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 7.74/2.73  tff(c_30, plain, (r2_hidden('#skF_6', k4_zfmisc_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.74/2.73  tff(c_6, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.74/2.73  tff(c_14, plain, (![A_19, B_20, C_21, D_22]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_19, B_20), C_21), D_22)=k4_zfmisc_1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.74/2.73  tff(c_31, plain, (![A_19, B_20, C_21, D_22]: (k2_zfmisc_1(k3_zfmisc_1(A_19, B_20, C_21), D_22)=k4_zfmisc_1(A_19, B_20, C_21, D_22))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 7.74/2.73  tff(c_53, plain, (![A_50, B_51, C_52]: (k2_zfmisc_1(k2_zfmisc_1(A_50, B_51), C_52)=k3_zfmisc_1(A_50, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.74/2.73  tff(c_66, plain, (![A_9, B_10, C_11, C_52]: (k3_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11, C_52)=k2_zfmisc_1(k3_zfmisc_1(A_9, B_10, C_11), C_52))), inference(superposition, [status(thm), theory('equality')], [c_6, c_53])).
% 7.74/2.73  tff(c_239, plain, (![A_9, B_10, C_11, C_52]: (k3_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11, C_52)=k4_zfmisc_1(A_9, B_10, C_11, C_52))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_66])).
% 7.74/2.73  tff(c_394, plain, (![A_129, B_130, C_131, D_132]: (k3_mcart_1('#skF_3'(A_129, B_130, C_131, D_132), '#skF_4'(A_129, B_130, C_131, D_132), '#skF_5'(A_129, B_130, C_131, D_132))=A_129 | ~r2_hidden(A_129, k3_zfmisc_1(B_130, C_131, D_132)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.74/2.73  tff(c_72, plain, (![A_53, B_54, C_55]: (k4_tarski(k4_tarski(A_53, B_54), C_55)=k3_mcart_1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.74/2.73  tff(c_26, plain, (![A_30, B_31]: (k2_mcart_1(k4_tarski(A_30, B_31))=B_31)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.74/2.73  tff(c_84, plain, (![A_53, B_54, C_55]: (k2_mcart_1(k3_mcart_1(A_53, B_54, C_55))=C_55)), inference(superposition, [status(thm), theory('equality')], [c_72, c_26])).
% 7.74/2.73  tff(c_417, plain, (![A_133, B_134, C_135, D_136]: (k2_mcart_1(A_133)='#skF_5'(A_133, B_134, C_135, D_136) | ~r2_hidden(A_133, k3_zfmisc_1(B_134, C_135, D_136)))), inference(superposition, [status(thm), theory('equality')], [c_394, c_84])).
% 7.74/2.73  tff(c_1252, plain, (![C_225, C_224, A_226, A_222, B_223]: ('#skF_5'(A_222, k2_zfmisc_1(A_226, B_223), C_225, C_224)=k2_mcart_1(A_222) | ~r2_hidden(A_222, k4_zfmisc_1(A_226, B_223, C_225, C_224)))), inference(superposition, [status(thm), theory('equality')], [c_239, c_417])).
% 7.74/2.73  tff(c_1299, plain, ('#skF_5'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10')=k2_mcart_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_1252])).
% 7.74/2.73  tff(c_16, plain, (![A_23, B_24, C_25, D_26]: (k3_mcart_1('#skF_3'(A_23, B_24, C_25, D_26), '#skF_4'(A_23, B_24, C_25, D_26), '#skF_5'(A_23, B_24, C_25, D_26))=A_23 | ~r2_hidden(A_23, k3_zfmisc_1(B_24, C_25, D_26)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.74/2.73  tff(c_1303, plain, (k3_mcart_1('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_4'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), k2_mcart_1('#skF_6'))='#skF_6' | ~r2_hidden('#skF_6', k3_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1299, c_16])).
% 7.74/2.73  tff(c_1310, plain, (k3_mcart_1('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_4'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), k2_mcart_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_239, c_1303])).
% 7.74/2.73  tff(c_24, plain, (![A_30, B_31]: (k1_mcart_1(k4_tarski(A_30, B_31))=A_30)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.74/2.73  tff(c_81, plain, (![A_53, B_54, C_55]: (k1_mcart_1(k3_mcart_1(A_53, B_54, C_55))=k4_tarski(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_72, c_24])).
% 7.74/2.73  tff(c_1411, plain, (k4_tarski('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_4'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'))=k1_mcart_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1310, c_81])).
% 7.74/2.73  tff(c_1509, plain, (k1_mcart_1(k1_mcart_1('#skF_6'))='#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1411, c_24])).
% 7.74/2.73  tff(c_149, plain, (![A_82, B_83, C_84, D_85]: (k2_zfmisc_1(k3_zfmisc_1(A_82, B_83, C_84), D_85)=k4_zfmisc_1(A_82, B_83, C_84, D_85))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 7.74/2.73  tff(c_10, plain, (![A_12, B_13, C_14]: (r2_hidden(k1_mcart_1(A_12), B_13) | ~r2_hidden(A_12, k2_zfmisc_1(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.74/2.73  tff(c_353, plain, (![A_124, C_126, A_128, D_125, B_127]: (r2_hidden(k1_mcart_1(A_124), k3_zfmisc_1(A_128, B_127, C_126)) | ~r2_hidden(A_124, k4_zfmisc_1(A_128, B_127, C_126, D_125)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_10])).
% 7.74/2.73  tff(c_368, plain, (r2_hidden(k1_mcart_1('#skF_6'), k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_30, c_353])).
% 7.74/2.73  tff(c_63, plain, (![A_12, A_50, B_51, C_52]: (r2_hidden(k1_mcart_1(A_12), k2_zfmisc_1(A_50, B_51)) | ~r2_hidden(A_12, k3_zfmisc_1(A_50, B_51, C_52)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_10])).
% 7.74/2.73  tff(c_373, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_368, c_63])).
% 7.74/2.73  tff(c_1525, plain, (r2_hidden('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_373])).
% 7.74/2.73  tff(c_286, plain, (![A_115, B_116, C_117]: (k4_tarski('#skF_1'(A_115, B_116, C_117), '#skF_2'(A_115, B_116, C_117))=A_115 | ~r2_hidden(A_115, k2_zfmisc_1(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.74/2.73  tff(c_298, plain, (![A_115, B_116, C_117]: (k1_mcart_1(A_115)='#skF_1'(A_115, B_116, C_117) | ~r2_hidden(A_115, k2_zfmisc_1(B_116, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_286, c_24])).
% 7.74/2.73  tff(c_386, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))='#skF_1'(k1_mcart_1(k1_mcart_1('#skF_6')), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_373, c_298])).
% 7.74/2.73  tff(c_1522, plain, (k1_mcart_1('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'))='#skF_1'('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_1509, c_386])).
% 7.74/2.73  tff(c_1794, plain, (![A_255, B_256, C_257, D_258]: (k4_tarski('#skF_3'(A_255, B_256, C_257, D_258), '#skF_4'(A_255, B_256, C_257, D_258))=k1_mcart_1(A_255) | ~r2_hidden(A_255, k3_zfmisc_1(B_256, C_257, D_258)))), inference(superposition, [status(thm), theory('equality')], [c_394, c_81])).
% 7.74/2.73  tff(c_1825, plain, (![A_259, B_260, C_261, D_262]: (k1_mcart_1(k1_mcart_1(A_259))='#skF_3'(A_259, B_260, C_261, D_262) | ~r2_hidden(A_259, k3_zfmisc_1(B_260, C_261, D_262)))), inference(superposition, [status(thm), theory('equality')], [c_1794, c_24])).
% 7.74/2.73  tff(c_1855, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))='#skF_3'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_368, c_1825])).
% 7.74/2.73  tff(c_1881, plain, ('#skF_1'('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_7', '#skF_8')='#skF_3'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1522, c_1509, c_1855])).
% 7.74/2.73  tff(c_388, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))), '#skF_7')), inference(resolution, [status(thm)], [c_373, c_10])).
% 7.74/2.73  tff(c_412, plain, (r2_hidden('#skF_1'(k1_mcart_1(k1_mcart_1('#skF_6')), '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_388])).
% 7.74/2.73  tff(c_1521, plain, (r2_hidden('#skF_1'('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_412])).
% 7.74/2.73  tff(c_1948, plain, (r2_hidden('#skF_3'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1521])).
% 7.74/2.73  tff(c_301, plain, (![A_115, B_116, C_117]: (k2_mcart_1(A_115)='#skF_2'(A_115, B_116, C_117) | ~r2_hidden(A_115, k2_zfmisc_1(B_116, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_286, c_26])).
% 7.74/2.73  tff(c_385, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))='#skF_2'(k1_mcart_1(k1_mcart_1('#skF_6')), '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_373, c_301])).
% 7.74/2.73  tff(c_1524, plain, (k2_mcart_1('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'))='#skF_2'('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_1509, c_385])).
% 7.74/2.73  tff(c_1886, plain, (![A_263, B_264, C_265, D_266]: (k2_mcart_1(k1_mcart_1(A_263))='#skF_4'(A_263, B_264, C_265, D_266) | ~r2_hidden(A_263, k3_zfmisc_1(B_264, C_265, D_266)))), inference(superposition, [status(thm), theory('equality')], [c_1794, c_26])).
% 7.74/2.73  tff(c_1916, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))='#skF_4'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_368, c_1886])).
% 7.74/2.73  tff(c_1942, plain, ('#skF_2'('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_7', '#skF_8')='#skF_4'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1524, c_1509, c_1916])).
% 7.74/2.73  tff(c_8, plain, (![A_12, C_14, B_13]: (r2_hidden(k2_mcart_1(A_12), C_14) | ~r2_hidden(A_12, k2_zfmisc_1(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.74/2.73  tff(c_387, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))), '#skF_8')), inference(resolution, [status(thm)], [c_373, c_8])).
% 7.74/2.73  tff(c_389, plain, (r2_hidden('#skF_2'(k1_mcart_1(k1_mcart_1('#skF_6')), '#skF_7', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_387])).
% 7.74/2.73  tff(c_1523, plain, (r2_hidden('#skF_2'('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_7', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_389])).
% 7.74/2.73  tff(c_1974, plain, (r2_hidden('#skF_4'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1942, c_1523])).
% 7.74/2.73  tff(c_436, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))='#skF_5'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_368, c_417])).
% 7.74/2.73  tff(c_61, plain, (![A_12, C_52, A_50, B_51]: (r2_hidden(k2_mcart_1(A_12), C_52) | ~r2_hidden(A_12, k3_zfmisc_1(A_50, B_51, C_52)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_8])).
% 7.74/2.73  tff(c_374, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')), '#skF_9')), inference(resolution, [status(thm)], [c_368, c_61])).
% 7.74/2.73  tff(c_440, plain, (r2_hidden('#skF_5'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_374])).
% 7.74/2.73  tff(c_1512, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))='#skF_4'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1411, c_26])).
% 7.74/2.73  tff(c_1515, plain, ('#skF_4'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10')='#skF_5'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_1512])).
% 7.74/2.73  tff(c_178, plain, (![C_92, D_91, B_93, A_94, A_90]: (r2_hidden(k2_mcart_1(A_90), D_91) | ~r2_hidden(A_90, k4_zfmisc_1(A_94, B_93, C_92, D_91)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_8])).
% 7.74/2.73  tff(c_185, plain, (r2_hidden(k2_mcart_1('#skF_6'), '#skF_10')), inference(resolution, [status(thm)], [c_30, c_178])).
% 7.74/2.73  tff(c_4, plain, (![A_6, B_7, C_8]: (k4_tarski(k4_tarski(A_6, B_7), C_8)=k3_mcart_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.74/2.73  tff(c_12, plain, (![A_15, B_16, C_17, D_18]: (k4_tarski(k4_tarski(k4_tarski(A_15, B_16), C_17), D_18)=k4_mcart_1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.74/2.73  tff(c_32, plain, (![A_15, B_16, C_17, D_18]: (k4_tarski(k3_mcart_1(A_15, B_16, C_17), D_18)=k4_mcart_1(A_15, B_16, C_17, D_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 7.74/2.73  tff(c_75, plain, (![A_53, B_54, C_55, C_8]: (k3_mcart_1(k4_tarski(A_53, B_54), C_55, C_8)=k4_tarski(k3_mcart_1(A_53, B_54, C_55), C_8))), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 7.74/2.73  tff(c_212, plain, (![A_53, B_54, C_55, C_8]: (k3_mcart_1(k4_tarski(A_53, B_54), C_55, C_8)=k4_mcart_1(A_53, B_54, C_55, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75])).
% 7.74/2.73  tff(c_2254, plain, (![C_299, C_297, B_300, A_301, C_298]: (k4_mcart_1('#skF_1'(A_301, B_300, C_298), '#skF_2'(A_301, B_300, C_298), C_297, C_299)=k3_mcart_1(A_301, C_297, C_299) | ~r2_hidden(A_301, k2_zfmisc_1(B_300, C_298)))), inference(superposition, [status(thm), theory('equality')], [c_286, c_212])).
% 7.74/2.73  tff(c_28, plain, (![F_36, G_37, H_38, I_39]: (k4_mcart_1(F_36, G_37, H_38, I_39)!='#skF_6' | ~r2_hidden(I_39, '#skF_10') | ~r2_hidden(H_38, '#skF_9') | ~r2_hidden(G_37, '#skF_8') | ~r2_hidden(F_36, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.74/2.73  tff(c_2313, plain, (![C_305, C_302, A_306, C_304, B_303]: (k3_mcart_1(A_306, C_305, C_302)!='#skF_6' | ~r2_hidden(C_302, '#skF_10') | ~r2_hidden(C_305, '#skF_9') | ~r2_hidden('#skF_2'(A_306, B_303, C_304), '#skF_8') | ~r2_hidden('#skF_1'(A_306, B_303, C_304), '#skF_7') | ~r2_hidden(A_306, k2_zfmisc_1(B_303, C_304)))), inference(superposition, [status(thm), theory('equality')], [c_2254, c_28])).
% 7.74/2.73  tff(c_5518, plain, (![D_528, B_526, C_525, A_530, C_527, B_529]: (A_530!='#skF_6' | ~r2_hidden('#skF_5'(A_530, B_526, C_525, D_528), '#skF_10') | ~r2_hidden('#skF_4'(A_530, B_526, C_525, D_528), '#skF_9') | ~r2_hidden('#skF_2'('#skF_3'(A_530, B_526, C_525, D_528), B_529, C_527), '#skF_8') | ~r2_hidden('#skF_1'('#skF_3'(A_530, B_526, C_525, D_528), B_529, C_527), '#skF_7') | ~r2_hidden('#skF_3'(A_530, B_526, C_525, D_528), k2_zfmisc_1(B_529, C_527)) | ~r2_hidden(A_530, k3_zfmisc_1(B_526, C_525, D_528)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2313])).
% 7.74/2.73  tff(c_5521, plain, (~r2_hidden('#skF_5'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_10') | ~r2_hidden('#skF_4'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_2'('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), '#skF_7', '#skF_8'), '#skF_8') | ~r2_hidden('#skF_3'(k1_mcart_1('#skF_6'), '#skF_7', '#skF_8', '#skF_9'), '#skF_7') | ~r2_hidden('#skF_3'('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden('#skF_6', k3_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'), '#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1881, c_5518])).
% 7.74/2.73  tff(c_5525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_239, c_1525, c_1948, c_1974, c_1942, c_440, c_1515, c_185, c_1299, c_5521])).
% 7.74/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.73  
% 7.74/2.73  Inference rules
% 7.74/2.73  ----------------------
% 7.74/2.73  #Ref     : 0
% 7.74/2.73  #Sup     : 1247
% 7.74/2.73  #Fact    : 0
% 7.74/2.73  #Define  : 0
% 7.74/2.73  #Split   : 3
% 7.74/2.73  #Chain   : 0
% 7.74/2.73  #Close   : 0
% 7.74/2.73  
% 7.74/2.73  Ordering : KBO
% 7.74/2.73  
% 7.74/2.73  Simplification rules
% 7.74/2.73  ----------------------
% 7.74/2.73  #Subsume      : 108
% 7.74/2.73  #Demod        : 991
% 7.74/2.73  #Tautology    : 256
% 7.74/2.73  #SimpNegUnit  : 0
% 7.74/2.73  #BackRed      : 22
% 7.74/2.73  
% 7.74/2.73  #Partial instantiations: 0
% 7.74/2.73  #Strategies tried      : 1
% 7.74/2.73  
% 7.74/2.73  Timing (in seconds)
% 7.74/2.73  ----------------------
% 7.74/2.73  Preprocessing        : 0.30
% 7.74/2.73  Parsing              : 0.17
% 7.74/2.73  CNF conversion       : 0.02
% 7.74/2.73  Main loop            : 1.66
% 7.74/2.73  Inferencing          : 0.62
% 7.74/2.73  Reduction            : 0.53
% 7.74/2.73  Demodulation         : 0.42
% 7.74/2.73  BG Simplification    : 0.12
% 7.74/2.73  Subsumption          : 0.24
% 7.74/2.73  Abstraction          : 0.19
% 7.74/2.73  MUC search           : 0.00
% 7.74/2.73  Cooper               : 0.00
% 7.74/2.73  Total                : 2.00
% 7.74/2.73  Index Insertion      : 0.00
% 7.74/2.73  Index Deletion       : 0.00
% 7.74/2.73  Index Matching       : 0.00
% 7.74/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
