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
% DateTime   : Thu Dec  3 10:10:24 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :  268 ( 926 expanded)
%              Number of leaves         :   34 ( 302 expanded)
%              Depth                    :   12
%              Number of atoms          :  471 (3348 expanded)
%              Number of equality atoms :  214 (1461 expanded)
%              Maximal formula depth    :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(A))
       => ! [F] :
            ( m1_subset_1(F,k1_zfmisc_1(B))
           => ! [G] :
                ( m1_subset_1(G,k1_zfmisc_1(C))
               => ! [H] :
                    ( m1_subset_1(H,k1_zfmisc_1(D))
                   => ! [I] :
                        ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
                       => ( r2_hidden(I,k4_zfmisc_1(E,F,G,H))
                         => ( r2_hidden(k8_mcart_1(A,B,C,D,I),E)
                            & r2_hidden(k9_mcart_1(A,B,C,D,I),F)
                            & r2_hidden(k10_mcart_1(A,B,C,D,I),G)
                            & r2_hidden(k11_mcart_1(A,B,C,D,I),H) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    r2_hidden('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_929,plain,(
    ! [A_214,B_215,C_216,D_217] : k2_zfmisc_1(k3_zfmisc_1(A_214,B_215,C_216),D_217) = k4_zfmisc_1(A_214,B_215,C_216,D_217) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_15,C_17,B_16] :
      ( r2_hidden(k2_mcart_1(A_15),C_17)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_946,plain,(
    ! [B_220,A_223,A_221,D_222,C_219] :
      ( r2_hidden(k2_mcart_1(A_221),D_222)
      | ~ r2_hidden(A_221,k4_zfmisc_1(A_223,B_220,C_219,D_222)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_12])).

tff(c_949,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_946])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    m1_subset_1('#skF_9',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_997,plain,(
    ! [B_234,E_230,D_233,C_232,A_231] :
      ( k11_mcart_1(A_231,B_234,C_232,D_233,E_230) = k2_mcart_1(E_230)
      | ~ m1_subset_1(E_230,k4_zfmisc_1(A_231,B_234,C_232,D_233))
      | k1_xboole_0 = D_233
      | k1_xboole_0 = C_232
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_231 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1001,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_997])).

tff(c_1059,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1062,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_2])).

tff(c_24,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_8')
    | ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7')
    | ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6')
    | ~ r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_43,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_133,plain,(
    ! [E_83,C_85,B_87,D_86,A_84] :
      ( k11_mcart_1(A_84,B_87,C_85,D_86,E_83) = k2_mcart_1(E_83)
      | ~ m1_subset_1(E_83,k4_zfmisc_1(A_84,B_87,C_85,D_86))
      | k1_xboole_0 = D_86
      | k1_xboole_0 = C_85
      | k1_xboole_0 = B_87
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_137,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_165,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_168,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2])).

tff(c_69,plain,(
    ! [A_65,B_66,C_67,D_68] : k2_zfmisc_1(k3_zfmisc_1(A_65,B_66,C_67),D_68) = k4_zfmisc_1(A_65,B_66,C_67,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k1_mcart_1(A_15),B_16)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_259,plain,(
    ! [A_130,D_126,A_129,C_127,B_128] :
      ( r2_hidden(k1_mcart_1(A_130),k3_zfmisc_1(A_129,B_128,C_127))
      | ~ r2_hidden(A_130,k4_zfmisc_1(A_129,B_128,C_127,D_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_266,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_259])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k1_mcart_1(A_59),B_60)
      | ~ r2_hidden(A_59,k2_zfmisc_1(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_59,A_8,B_9,C_10] :
      ( r2_hidden(k1_mcart_1(A_59),k2_zfmisc_1(A_8,B_9))
      | ~ r2_hidden(A_59,k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_276,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_266,c_64])).

tff(c_303,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_276,c_14])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_365,plain,(
    ! [A_144] :
      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),A_144)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_303,c_4])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_429,plain,(
    ! [A_146] :
      ( ~ r1_tarski(A_146,k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_146)) ) ),
    inference(resolution,[status(thm)],[c_365,c_6])).

tff(c_433,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_168,c_429])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_433])).

tff(c_439,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_448,plain,(
    ! [A_152,B_155,E_151,C_153,D_154] :
      ( k2_mcart_1(k1_mcart_1(E_151)) = k10_mcart_1(A_152,B_155,C_153,D_154,E_151)
      | ~ m1_subset_1(E_151,k4_zfmisc_1(A_152,B_155,C_153,D_154))
      | k1_xboole_0 = D_154
      | k1_xboole_0 = C_153
      | k1_xboole_0 = B_155
      | k1_xboole_0 = A_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_451,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_448])).

tff(c_454,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_451])).

tff(c_579,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_586,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_2])).

tff(c_518,plain,(
    ! [C_176,B_177,A_178,D_175,A_179] :
      ( r2_hidden(k1_mcart_1(A_179),k3_zfmisc_1(A_178,B_177,C_176))
      | ~ r2_hidden(A_179,k4_zfmisc_1(A_178,B_177,C_176,D_175)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_525,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_518])).

tff(c_541,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_525,c_64])).

tff(c_563,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_541,c_12])).

tff(c_637,plain,(
    ! [A_189] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),A_189)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_189)) ) ),
    inference(resolution,[status(thm)],[c_563,c_4])).

tff(c_702,plain,(
    ! [A_191] :
      ( ~ r1_tarski(A_191,k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_191)) ) ),
    inference(resolution,[status(thm)],[c_637,c_6])).

tff(c_706,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_586,c_702])).

tff(c_710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_706])).

tff(c_712,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_526,plain,(
    ! [C_182,A_181,D_183,E_180,B_184] :
      ( k8_mcart_1(A_181,B_184,C_182,D_183,E_180) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_180)))
      | ~ m1_subset_1(E_180,k4_zfmisc_1(A_181,B_184,C_182,D_183))
      | k1_xboole_0 = D_183
      | k1_xboole_0 = C_182
      | k1_xboole_0 = B_184
      | k1_xboole_0 = A_181 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_528,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_526])).

tff(c_531,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_528])).

tff(c_838,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_531])).

tff(c_839,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_45,plain,(
    ! [A_56,B_57,C_58] : k2_zfmisc_1(k2_zfmisc_1(A_56,B_57),C_58) = k3_zfmisc_1(A_56,B_57,C_58) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_15,C_58,A_56,B_57] :
      ( r2_hidden(k2_mcart_1(A_15),C_58)
      | ~ r2_hidden(A_15,k3_zfmisc_1(A_56,B_57,C_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_12])).

tff(c_542,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_525,c_53])).

tff(c_713,plain,(
    ! [A_192] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_192)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_192)) ) ),
    inference(resolution,[status(thm)],[c_542,c_4])).

tff(c_745,plain,(
    ! [A_193] :
      ( ~ r1_tarski(A_193,k2_mcart_1(k1_mcart_1('#skF_9')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_193)) ) ),
    inference(resolution,[status(thm)],[c_713,c_6])).

tff(c_750,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_745])).

tff(c_840,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_750])).

tff(c_851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_840])).

tff(c_853,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_472,plain,(
    ! [C_160,D_161,A_159,E_158,B_162] :
      ( k9_mcart_1(A_159,B_162,C_160,D_161,E_158) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_158)))
      | ~ m1_subset_1(E_158,k4_zfmisc_1(A_159,B_162,C_160,D_161))
      | k1_xboole_0 = D_161
      | k1_xboole_0 = C_160
      | k1_xboole_0 = B_162
      | k1_xboole_0 = A_159 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_474,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_472])).

tff(c_477,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_474])).

tff(c_854,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_853,c_477])).

tff(c_855,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_854])).

tff(c_87,plain,(
    ! [D_74,A_77,C_75,A_78,B_76] :
      ( r2_hidden(k2_mcart_1(A_78),D_74)
      | ~ r2_hidden(A_78,k4_zfmisc_1(A_77,B_76,C_75,D_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_90,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_87])).

tff(c_98,plain,(
    ! [A_79] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_79)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_122,plain,(
    ! [A_80] :
      ( ~ r1_tarski(A_80,k2_mcart_1('#skF_9'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_80)) ) ),
    inference(resolution,[status(thm)],[c_98,c_6])).

tff(c_127,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_122])).

tff(c_865,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_127])).

tff(c_869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_865])).

tff(c_871,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_854])).

tff(c_852,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_887,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_871,c_852])).

tff(c_562,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_541,c_14])).

tff(c_890,plain,(
    r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_562])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_890])).

tff(c_894,plain,(
    r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_921,plain,(
    ! [C_207,A_208,B_209] :
      ( r2_hidden(C_207,A_208)
      | ~ r2_hidden(C_207,B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1031,plain,(
    ! [A_243] :
      ( r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),A_243)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_243)) ) ),
    inference(resolution,[status(thm)],[c_894,c_921])).

tff(c_1081,plain,(
    ! [A_250] :
      ( ~ r1_tarski(A_250,k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_250)) ) ),
    inference(resolution,[status(thm)],[c_1031,c_6])).

tff(c_1085,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1062,c_1081])).

tff(c_1089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1085])).

tff(c_1090,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_1093,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1090])).

tff(c_893,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6')
    | ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7')
    | ~ r2_hidden(k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_900,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_893])).

tff(c_1094,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_900])).

tff(c_1097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_1094])).

tff(c_1098,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1090])).

tff(c_1100,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1098])).

tff(c_1104,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_2])).

tff(c_1198,plain,(
    ! [D_285,C_282,A_284,B_283,A_286] :
      ( r2_hidden(k1_mcart_1(A_284),k3_zfmisc_1(A_286,B_283,C_282))
      | ~ r2_hidden(A_284,k4_zfmisc_1(A_286,B_283,C_282,D_285)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_14])).

tff(c_1209,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_1198])).

tff(c_902,plain,(
    ! [A_204,B_205,C_206] : k2_zfmisc_1(k2_zfmisc_1(A_204,B_205),C_206) = k3_zfmisc_1(A_204,B_205,C_206) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_912,plain,(
    ! [A_15,A_204,B_205,C_206] :
      ( r2_hidden(k1_mcart_1(A_15),k2_zfmisc_1(A_204,B_205))
      | ~ r2_hidden(A_15,k3_zfmisc_1(A_204,B_205,C_206)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_14])).

tff(c_1219,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1209,c_912])).

tff(c_1240,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1219,c_12])).

tff(c_1336,plain,(
    ! [A_296] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),A_296)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_296)) ) ),
    inference(resolution,[status(thm)],[c_1240,c_4])).

tff(c_1374,plain,(
    ! [A_298] :
      ( ~ r1_tarski(A_298,k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_298)) ) ),
    inference(resolution,[status(thm)],[c_1336,c_6])).

tff(c_1378,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1104,c_1374])).

tff(c_1382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1378])).

tff(c_1383,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1098])).

tff(c_1385,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1383])).

tff(c_957,plain,(
    ! [A_224] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_224)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_224)) ) ),
    inference(resolution,[status(thm)],[c_949,c_4])).

tff(c_981,plain,(
    ! [A_225] :
      ( ~ r1_tarski(A_225,k2_mcart_1('#skF_9'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_225)) ) ),
    inference(resolution,[status(thm)],[c_957,c_6])).

tff(c_986,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_981])).

tff(c_1389,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1385,c_986])).

tff(c_1393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1389])).

tff(c_1394,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1383])).

tff(c_1401,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_2])).

tff(c_1500,plain,(
    ! [A_337,B_334,C_333,D_336,A_335] :
      ( r2_hidden(k1_mcart_1(A_335),k3_zfmisc_1(A_337,B_334,C_333))
      | ~ r2_hidden(A_335,k4_zfmisc_1(A_337,B_334,C_333,D_336)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_14])).

tff(c_1511,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_1500])).

tff(c_910,plain,(
    ! [A_15,C_206,A_204,B_205] :
      ( r2_hidden(k2_mcart_1(A_15),C_206)
      | ~ r2_hidden(A_15,k3_zfmisc_1(A_204,B_205,C_206)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_12])).

tff(c_1522,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1511,c_910])).

tff(c_1568,plain,(
    ! [A_344] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_344)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_344)) ) ),
    inference(resolution,[status(thm)],[c_1522,c_4])).

tff(c_1600,plain,(
    ! [A_345] :
      ( ~ r1_tarski(A_345,k2_mcart_1(k1_mcart_1('#skF_9')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_345)) ) ),
    inference(resolution,[status(thm)],[c_1568,c_6])).

tff(c_1604,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1401,c_1600])).

tff(c_1608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1604])).

tff(c_1609,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7')
    | ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_1615,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1609])).

tff(c_1710,plain,(
    ! [D_376,C_375,A_374,B_377,E_373] :
      ( k11_mcart_1(A_374,B_377,C_375,D_376,E_373) = k2_mcart_1(E_373)
      | ~ m1_subset_1(E_373,k4_zfmisc_1(A_374,B_377,C_375,D_376))
      | k1_xboole_0 = D_376
      | k1_xboole_0 = C_375
      | k1_xboole_0 = B_377
      | k1_xboole_0 = A_374 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1714,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_1710])).

tff(c_1765,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1714])).

tff(c_1768,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_2])).

tff(c_1636,plain,(
    ! [C_352,A_353,B_354] :
      ( r2_hidden(C_352,A_353)
      | ~ r2_hidden(C_352,B_354)
      | ~ m1_subset_1(B_354,k1_zfmisc_1(A_353)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1779,plain,(
    ! [A_386] :
      ( r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),A_386)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_386)) ) ),
    inference(resolution,[status(thm)],[c_894,c_1636])).

tff(c_1827,plain,(
    ! [A_396] :
      ( ~ r1_tarski(A_396,k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_396)) ) ),
    inference(resolution,[status(thm)],[c_1779,c_6])).

tff(c_1831,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1768,c_1827])).

tff(c_1835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1831])).

tff(c_1837,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1714])).

tff(c_1891,plain,(
    ! [C_406,A_405,B_408,D_407,E_404] :
      ( k2_mcart_1(k1_mcart_1(E_404)) = k10_mcart_1(A_405,B_408,C_406,D_407,E_404)
      | ~ m1_subset_1(E_404,k4_zfmisc_1(A_405,B_408,C_406,D_407))
      | k1_xboole_0 = D_407
      | k1_xboole_0 = C_406
      | k1_xboole_0 = B_408
      | k1_xboole_0 = A_405 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1894,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_1891])).

tff(c_1897,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1837,c_1894])).

tff(c_2146,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1897])).

tff(c_2160,plain,(
    ! [A_445] : r1_tarski('#skF_2',A_445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_2])).

tff(c_1646,plain,(
    ! [A_355,B_356,C_357,D_358] : k2_zfmisc_1(k3_zfmisc_1(A_355,B_356,C_357),D_358) = k4_zfmisc_1(A_355,B_356,C_357,D_358) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1935,plain,(
    ! [A_424,C_427,D_423,A_425,B_426] :
      ( r2_hidden(k1_mcart_1(A_425),k3_zfmisc_1(A_424,B_426,C_427))
      | ~ r2_hidden(A_425,k4_zfmisc_1(A_424,B_426,C_427,D_423)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_14])).

tff(c_1946,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_1935])).

tff(c_1617,plain,(
    ! [A_349,B_350,C_351] : k2_zfmisc_1(k2_zfmisc_1(A_349,B_350),C_351) = k3_zfmisc_1(A_349,B_350,C_351) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1627,plain,(
    ! [A_15,A_349,B_350,C_351] :
      ( r2_hidden(k1_mcart_1(A_15),k2_zfmisc_1(A_349,B_350))
      | ~ r2_hidden(A_15,k3_zfmisc_1(A_349,B_350,C_351)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_14])).

tff(c_1962,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1946,c_1627])).

tff(c_1983,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1962,c_12])).

tff(c_2102,plain,(
    ! [A_442] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),A_442)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_442)) ) ),
    inference(resolution,[status(thm)],[c_1983,c_4])).

tff(c_2133,plain,(
    ! [A_442] :
      ( ~ r1_tarski(A_442,k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_442)) ) ),
    inference(resolution,[status(thm)],[c_2102,c_6])).

tff(c_2164,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2160,c_2133])).

tff(c_2184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2164])).

tff(c_2186,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1897])).

tff(c_1947,plain,(
    ! [D_431,C_430,A_429,B_432,E_428] :
      ( k8_mcart_1(A_429,B_432,C_430,D_431,E_428) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_428)))
      | ~ m1_subset_1(E_428,k4_zfmisc_1(A_429,B_432,C_430,D_431))
      | k1_xboole_0 = D_431
      | k1_xboole_0 = C_430
      | k1_xboole_0 = B_432
      | k1_xboole_0 = A_429 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1949,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_1947])).

tff(c_1952,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1837,c_1949])).

tff(c_2207,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2186,c_1952])).

tff(c_2208,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2207])).

tff(c_1625,plain,(
    ! [A_15,C_351,A_349,B_350] :
      ( r2_hidden(k2_mcart_1(A_15),C_351)
      | ~ r2_hidden(A_15,k3_zfmisc_1(A_349,B_350,C_351)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_12])).

tff(c_1963,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1946,c_1625])).

tff(c_2031,plain,(
    ! [A_438] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_438)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_438)) ) ),
    inference(resolution,[status(thm)],[c_1963,c_4])).

tff(c_2063,plain,(
    ! [A_439] :
      ( ~ r1_tarski(A_439,k2_mcart_1(k1_mcart_1('#skF_9')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_439)) ) ),
    inference(resolution,[status(thm)],[c_2031,c_6])).

tff(c_2068,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_2063])).

tff(c_2211,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_2068])).

tff(c_2222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2211])).

tff(c_2224,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2207])).

tff(c_1917,plain,(
    ! [C_416,E_414,A_415,B_418,D_417] :
      ( k9_mcart_1(A_415,B_418,C_416,D_417,E_414) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_414)))
      | ~ m1_subset_1(E_414,k4_zfmisc_1(A_415,B_418,C_416,D_417))
      | k1_xboole_0 = D_417
      | k1_xboole_0 = C_416
      | k1_xboole_0 = B_418
      | k1_xboole_0 = A_415 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1919,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_1917])).

tff(c_1922,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1837,c_1919])).

tff(c_2187,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1922])).

tff(c_2188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2186,c_2187])).

tff(c_2189,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1922])).

tff(c_2305,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_2224,c_2189])).

tff(c_2306,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2305])).

tff(c_2310,plain,(
    r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2306,c_1983])).

tff(c_2312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_2310])).

tff(c_2313,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2305])).

tff(c_1664,plain,(
    ! [C_368,B_367,A_366,A_365,D_364] :
      ( r2_hidden(k2_mcart_1(A_366),D_364)
      | ~ r2_hidden(A_366,k4_zfmisc_1(A_365,B_367,C_368,D_364)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_12])).

tff(c_1667,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_1664])).

tff(c_1675,plain,(
    ! [A_369] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_369)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_369)) ) ),
    inference(resolution,[status(thm)],[c_1667,c_4])).

tff(c_1699,plain,(
    ! [A_370] :
      ( ~ r1_tarski(A_370,k2_mcart_1('#skF_9'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_370)) ) ),
    inference(resolution,[status(thm)],[c_1675,c_6])).

tff(c_1704,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_1699])).

tff(c_2326,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_1704])).

tff(c_2330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2326])).

tff(c_2331,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_2399,plain,(
    ! [E_472,D_475,C_474,B_476,A_473] :
      ( k11_mcart_1(A_473,B_476,C_474,D_475,E_472) = k2_mcart_1(E_472)
      | ~ m1_subset_1(E_472,k4_zfmisc_1(A_473,B_476,C_474,D_475))
      | k1_xboole_0 = D_475
      | k1_xboole_0 = C_474
      | k1_xboole_0 = B_476
      | k1_xboole_0 = A_473 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2403,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_2399])).

tff(c_2434,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2403])).

tff(c_2437,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_2])).

tff(c_2357,plain,(
    ! [C_455,A_456,B_457] :
      ( r2_hidden(C_455,A_456)
      | ~ r2_hidden(C_455,B_457)
      | ~ m1_subset_1(B_457,k1_zfmisc_1(A_456)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2510,plain,(
    ! [A_494] :
      ( r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),A_494)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_494)) ) ),
    inference(resolution,[status(thm)],[c_894,c_2357])).

tff(c_2597,plain,(
    ! [A_507] :
      ( ~ r1_tarski(A_507,k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_507)) ) ),
    inference(resolution,[status(thm)],[c_2510,c_6])).

tff(c_2601,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2437,c_2597])).

tff(c_2605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2601])).

tff(c_2607,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2403])).

tff(c_2676,plain,(
    ! [E_521,A_522,B_525,D_524,C_523] :
      ( k2_mcart_1(k1_mcart_1(E_521)) = k10_mcart_1(A_522,B_525,C_523,D_524,E_521)
      | ~ m1_subset_1(E_521,k4_zfmisc_1(A_522,B_525,C_523,D_524))
      | k1_xboole_0 = D_524
      | k1_xboole_0 = C_523
      | k1_xboole_0 = B_525
      | k1_xboole_0 = A_522 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2679,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_2676])).

tff(c_2682,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2607,c_2679])).

tff(c_2800,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2682])).

tff(c_2332,plain,(
    r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_2711,plain,(
    ! [A_527] :
      ( r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),A_527)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_527)) ) ),
    inference(resolution,[status(thm)],[c_2332,c_2357])).

tff(c_2761,plain,(
    ! [A_530] :
      ( ~ r1_tarski(A_530,k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_530)) ) ),
    inference(resolution,[status(thm)],[c_2711,c_6])).

tff(c_2766,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_2761])).

tff(c_2803,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2800,c_2766])).

tff(c_2812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2803])).

tff(c_2813,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2682])).

tff(c_2815,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2813])).

tff(c_2372,plain,(
    ! [A_463,B_464,C_465,D_466] : k2_zfmisc_1(k3_zfmisc_1(A_463,B_464,C_465),D_466) = k4_zfmisc_1(A_463,B_464,C_465,D_466) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2820,plain,(
    ! [B_551,A_553,D_550,C_552,A_554] :
      ( r2_hidden(k1_mcart_1(A_553),k3_zfmisc_1(A_554,B_551,C_552))
      | ~ r2_hidden(A_553,k4_zfmisc_1(A_554,B_551,C_552,D_550)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2372,c_14])).

tff(c_2835,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_2820])).

tff(c_2354,plain,(
    ! [A_452,C_453,B_454] :
      ( r2_hidden(k2_mcart_1(A_452),C_453)
      | ~ r2_hidden(A_452,k2_zfmisc_1(B_454,C_453)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2356,plain,(
    ! [A_452,C_10,A_8,B_9] :
      ( r2_hidden(k2_mcart_1(A_452),C_10)
      | ~ r2_hidden(A_452,k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2354])).

tff(c_2839,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2835,c_2356])).

tff(c_2847,plain,(
    r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2815,c_2839])).

tff(c_2849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2331,c_2847])).

tff(c_2850,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2813])).

tff(c_2852,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2850])).

tff(c_2862,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2852,c_2])).

tff(c_2886,plain,(
    ! [C_558,B_557,A_559,A_560,D_556] :
      ( r2_hidden(k1_mcart_1(A_559),k3_zfmisc_1(A_560,B_557,C_558))
      | ~ r2_hidden(A_559,k4_zfmisc_1(A_560,B_557,C_558,D_556)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2372,c_14])).

tff(c_2901,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_26,c_2886])).

tff(c_2912,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2901,c_2356])).

tff(c_2988,plain,(
    ! [A_571] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_571)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_571)) ) ),
    inference(resolution,[status(thm)],[c_2912,c_4])).

tff(c_3020,plain,(
    ! [A_572] :
      ( ~ r1_tarski(A_572,k2_mcart_1(k1_mcart_1('#skF_9')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_572)) ) ),
    inference(resolution,[status(thm)],[c_2988,c_6])).

tff(c_3024,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2862,c_3020])).

tff(c_3028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3024])).

tff(c_3029,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2850])).

tff(c_2388,plain,(
    ! [A_470,B_468,A_471,C_469,D_467] :
      ( r2_hidden(k2_mcart_1(A_470),D_467)
      | ~ r2_hidden(A_470,k4_zfmisc_1(A_471,B_468,C_469,D_467)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2372,c_12])).

tff(c_2391,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_2388])).

tff(c_2404,plain,(
    ! [A_477] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_477)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_477)) ) ),
    inference(resolution,[status(thm)],[c_2391,c_4])).

tff(c_2428,plain,(
    ! [A_478] :
      ( ~ r1_tarski(A_478,k2_mcart_1('#skF_9'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_478)) ) ),
    inference(resolution,[status(thm)],[c_2404,c_6])).

tff(c_2433,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_2428])).

tff(c_3038,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3029,c_2433])).

tff(c_3043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.89  
% 4.78/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.89  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 4.78/1.89  
% 4.78/1.89  %Foreground sorts:
% 4.78/1.89  
% 4.78/1.89  
% 4.78/1.89  %Background operators:
% 4.78/1.89  
% 4.78/1.89  
% 4.78/1.89  %Foreground operators:
% 4.78/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.78/1.89  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.78/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.78/1.89  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.78/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.78/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.78/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.78/1.89  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.78/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.78/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.78/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.78/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.78/1.89  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.78/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.78/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.78/1.89  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.78/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.89  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.78/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.78/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.78/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.89  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.78/1.89  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.78/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.89  
% 4.78/1.92  tff(f_99, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_mcart_1)).
% 4.78/1.92  tff(f_43, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 4.78/1.92  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.78/1.92  tff(f_74, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 4.78/1.92  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.78/1.92  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.78/1.92  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.78/1.92  tff(f_39, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.78/1.92  tff(c_30, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.92  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.92  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.92  tff(c_26, plain, (r2_hidden('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.92  tff(c_929, plain, (![A_214, B_215, C_216, D_217]: (k2_zfmisc_1(k3_zfmisc_1(A_214, B_215, C_216), D_217)=k4_zfmisc_1(A_214, B_215, C_216, D_217))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.78/1.92  tff(c_12, plain, (![A_15, C_17, B_16]: (r2_hidden(k2_mcart_1(A_15), C_17) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.78/1.92  tff(c_946, plain, (![B_220, A_223, A_221, D_222, C_219]: (r2_hidden(k2_mcart_1(A_221), D_222) | ~r2_hidden(A_221, k4_zfmisc_1(A_223, B_220, C_219, D_222)))), inference(superposition, [status(thm), theory('equality')], [c_929, c_12])).
% 4.78/1.92  tff(c_949, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_26, c_946])).
% 4.78/1.92  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.92  tff(c_28, plain, (m1_subset_1('#skF_9', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.92  tff(c_997, plain, (![B_234, E_230, D_233, C_232, A_231]: (k11_mcart_1(A_231, B_234, C_232, D_233, E_230)=k2_mcart_1(E_230) | ~m1_subset_1(E_230, k4_zfmisc_1(A_231, B_234, C_232, D_233)) | k1_xboole_0=D_233 | k1_xboole_0=C_232 | k1_xboole_0=B_234 | k1_xboole_0=A_231)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.92  tff(c_1001, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_997])).
% 4.78/1.92  tff(c_1059, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1001])).
% 4.78/1.92  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.78/1.92  tff(c_1062, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_2])).
% 4.78/1.92  tff(c_24, plain, (~r2_hidden(k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_8') | ~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7') | ~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6') | ~r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.92  tff(c_43, plain, (~r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(splitLeft, [status(thm)], [c_24])).
% 4.78/1.92  tff(c_133, plain, (![E_83, C_85, B_87, D_86, A_84]: (k11_mcart_1(A_84, B_87, C_85, D_86, E_83)=k2_mcart_1(E_83) | ~m1_subset_1(E_83, k4_zfmisc_1(A_84, B_87, C_85, D_86)) | k1_xboole_0=D_86 | k1_xboole_0=C_85 | k1_xboole_0=B_87 | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.92  tff(c_137, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_133])).
% 4.78/1.92  tff(c_165, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_137])).
% 4.78/1.92  tff(c_168, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_2])).
% 4.78/1.92  tff(c_69, plain, (![A_65, B_66, C_67, D_68]: (k2_zfmisc_1(k3_zfmisc_1(A_65, B_66, C_67), D_68)=k4_zfmisc_1(A_65, B_66, C_67, D_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.78/1.92  tff(c_14, plain, (![A_15, B_16, C_17]: (r2_hidden(k1_mcart_1(A_15), B_16) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.78/1.92  tff(c_259, plain, (![A_130, D_126, A_129, C_127, B_128]: (r2_hidden(k1_mcart_1(A_130), k3_zfmisc_1(A_129, B_128, C_127)) | ~r2_hidden(A_130, k4_zfmisc_1(A_129, B_128, C_127, D_126)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_14])).
% 4.78/1.92  tff(c_266, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_259])).
% 4.78/1.92  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.78/1.92  tff(c_62, plain, (![A_59, B_60, C_61]: (r2_hidden(k1_mcart_1(A_59), B_60) | ~r2_hidden(A_59, k2_zfmisc_1(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.78/1.92  tff(c_64, plain, (![A_59, A_8, B_9, C_10]: (r2_hidden(k1_mcart_1(A_59), k2_zfmisc_1(A_8, B_9)) | ~r2_hidden(A_59, k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_62])).
% 4.78/1.92  tff(c_276, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_266, c_64])).
% 4.78/1.92  tff(c_303, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_5')), inference(resolution, [status(thm)], [c_276, c_14])).
% 4.78/1.92  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.78/1.92  tff(c_365, plain, (![A_144]: (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), A_144) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_144)))), inference(resolution, [status(thm)], [c_303, c_4])).
% 4.78/1.92  tff(c_6, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.92  tff(c_429, plain, (![A_146]: (~r1_tarski(A_146, k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_146)))), inference(resolution, [status(thm)], [c_365, c_6])).
% 4.78/1.92  tff(c_433, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_168, c_429])).
% 4.78/1.92  tff(c_437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_433])).
% 4.78/1.92  tff(c_439, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_137])).
% 4.78/1.92  tff(c_448, plain, (![A_152, B_155, E_151, C_153, D_154]: (k2_mcart_1(k1_mcart_1(E_151))=k10_mcart_1(A_152, B_155, C_153, D_154, E_151) | ~m1_subset_1(E_151, k4_zfmisc_1(A_152, B_155, C_153, D_154)) | k1_xboole_0=D_154 | k1_xboole_0=C_153 | k1_xboole_0=B_155 | k1_xboole_0=A_152)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.92  tff(c_451, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_448])).
% 4.78/1.92  tff(c_454, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_439, c_451])).
% 4.78/1.92  tff(c_579, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_454])).
% 4.78/1.92  tff(c_586, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_2])).
% 4.78/1.92  tff(c_518, plain, (![C_176, B_177, A_178, D_175, A_179]: (r2_hidden(k1_mcart_1(A_179), k3_zfmisc_1(A_178, B_177, C_176)) | ~r2_hidden(A_179, k4_zfmisc_1(A_178, B_177, C_176, D_175)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_14])).
% 4.78/1.92  tff(c_525, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_518])).
% 4.78/1.92  tff(c_541, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_525, c_64])).
% 4.78/1.92  tff(c_563, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_6')), inference(resolution, [status(thm)], [c_541, c_12])).
% 4.78/1.92  tff(c_637, plain, (![A_189]: (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), A_189) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_189)))), inference(resolution, [status(thm)], [c_563, c_4])).
% 4.78/1.92  tff(c_702, plain, (![A_191]: (~r1_tarski(A_191, k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_191)))), inference(resolution, [status(thm)], [c_637, c_6])).
% 4.78/1.92  tff(c_706, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_586, c_702])).
% 4.78/1.92  tff(c_710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_706])).
% 4.78/1.92  tff(c_712, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_454])).
% 4.78/1.92  tff(c_526, plain, (![C_182, A_181, D_183, E_180, B_184]: (k8_mcart_1(A_181, B_184, C_182, D_183, E_180)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_180))) | ~m1_subset_1(E_180, k4_zfmisc_1(A_181, B_184, C_182, D_183)) | k1_xboole_0=D_183 | k1_xboole_0=C_182 | k1_xboole_0=B_184 | k1_xboole_0=A_181)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.92  tff(c_528, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_526])).
% 4.78/1.92  tff(c_531, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_439, c_528])).
% 4.78/1.92  tff(c_838, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_712, c_531])).
% 4.78/1.92  tff(c_839, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_838])).
% 4.78/1.92  tff(c_45, plain, (![A_56, B_57, C_58]: (k2_zfmisc_1(k2_zfmisc_1(A_56, B_57), C_58)=k3_zfmisc_1(A_56, B_57, C_58))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.78/1.92  tff(c_53, plain, (![A_15, C_58, A_56, B_57]: (r2_hidden(k2_mcart_1(A_15), C_58) | ~r2_hidden(A_15, k3_zfmisc_1(A_56, B_57, C_58)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_12])).
% 4.78/1.92  tff(c_542, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_525, c_53])).
% 4.78/1.92  tff(c_713, plain, (![A_192]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_192) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_192)))), inference(resolution, [status(thm)], [c_542, c_4])).
% 4.78/1.92  tff(c_745, plain, (![A_193]: (~r1_tarski(A_193, k2_mcart_1(k1_mcart_1('#skF_9'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_193)))), inference(resolution, [status(thm)], [c_713, c_6])).
% 4.78/1.92  tff(c_750, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_745])).
% 4.78/1.92  tff(c_840, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_839, c_750])).
% 4.78/1.92  tff(c_851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_840])).
% 4.78/1.92  tff(c_853, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_838])).
% 4.78/1.92  tff(c_472, plain, (![C_160, D_161, A_159, E_158, B_162]: (k9_mcart_1(A_159, B_162, C_160, D_161, E_158)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_158))) | ~m1_subset_1(E_158, k4_zfmisc_1(A_159, B_162, C_160, D_161)) | k1_xboole_0=D_161 | k1_xboole_0=C_160 | k1_xboole_0=B_162 | k1_xboole_0=A_159)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.92  tff(c_474, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_472])).
% 4.78/1.92  tff(c_477, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_439, c_474])).
% 4.78/1.92  tff(c_854, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_712, c_853, c_477])).
% 4.78/1.92  tff(c_855, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_854])).
% 4.78/1.92  tff(c_87, plain, (![D_74, A_77, C_75, A_78, B_76]: (r2_hidden(k2_mcart_1(A_78), D_74) | ~r2_hidden(A_78, k4_zfmisc_1(A_77, B_76, C_75, D_74)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_12])).
% 4.78/1.92  tff(c_90, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_26, c_87])).
% 4.78/1.92  tff(c_98, plain, (![A_79]: (r2_hidden(k2_mcart_1('#skF_9'), A_79) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_79)))), inference(resolution, [status(thm)], [c_90, c_4])).
% 4.78/1.92  tff(c_122, plain, (![A_80]: (~r1_tarski(A_80, k2_mcart_1('#skF_9')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_80)))), inference(resolution, [status(thm)], [c_98, c_6])).
% 4.78/1.92  tff(c_127, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_122])).
% 4.78/1.92  tff(c_865, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_855, c_127])).
% 4.78/1.92  tff(c_869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_865])).
% 4.78/1.92  tff(c_871, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_854])).
% 4.78/1.92  tff(c_852, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitRight, [status(thm)], [c_838])).
% 4.78/1.92  tff(c_887, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_871, c_852])).
% 4.78/1.92  tff(c_562, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_5')), inference(resolution, [status(thm)], [c_541, c_14])).
% 4.78/1.92  tff(c_890, plain, (r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_887, c_562])).
% 4.78/1.92  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_890])).
% 4.78/1.92  tff(c_894, plain, (r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 4.78/1.92  tff(c_921, plain, (![C_207, A_208, B_209]: (r2_hidden(C_207, A_208) | ~r2_hidden(C_207, B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(A_208)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.78/1.92  tff(c_1031, plain, (![A_243]: (r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), A_243) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_243)))), inference(resolution, [status(thm)], [c_894, c_921])).
% 4.78/1.92  tff(c_1081, plain, (![A_250]: (~r1_tarski(A_250, k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_250)))), inference(resolution, [status(thm)], [c_1031, c_6])).
% 4.78/1.92  tff(c_1085, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1062, c_1081])).
% 4.78/1.92  tff(c_1089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1085])).
% 4.78/1.92  tff(c_1090, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_1001])).
% 4.78/1.92  tff(c_1093, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_1090])).
% 4.78/1.92  tff(c_893, plain, (~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6') | ~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7') | ~r2_hidden(k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_24])).
% 4.78/1.92  tff(c_900, plain, (~r2_hidden(k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_893])).
% 4.78/1.92  tff(c_1094, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_900])).
% 4.78/1.92  tff(c_1097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_949, c_1094])).
% 4.78/1.92  tff(c_1098, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1090])).
% 4.78/1.92  tff(c_1100, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1098])).
% 4.78/1.92  tff(c_1104, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_2])).
% 4.78/1.92  tff(c_1198, plain, (![D_285, C_282, A_284, B_283, A_286]: (r2_hidden(k1_mcart_1(A_284), k3_zfmisc_1(A_286, B_283, C_282)) | ~r2_hidden(A_284, k4_zfmisc_1(A_286, B_283, C_282, D_285)))), inference(superposition, [status(thm), theory('equality')], [c_929, c_14])).
% 4.78/1.92  tff(c_1209, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_1198])).
% 4.78/1.92  tff(c_902, plain, (![A_204, B_205, C_206]: (k2_zfmisc_1(k2_zfmisc_1(A_204, B_205), C_206)=k3_zfmisc_1(A_204, B_205, C_206))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.78/1.92  tff(c_912, plain, (![A_15, A_204, B_205, C_206]: (r2_hidden(k1_mcart_1(A_15), k2_zfmisc_1(A_204, B_205)) | ~r2_hidden(A_15, k3_zfmisc_1(A_204, B_205, C_206)))), inference(superposition, [status(thm), theory('equality')], [c_902, c_14])).
% 4.78/1.92  tff(c_1219, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1209, c_912])).
% 4.78/1.92  tff(c_1240, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_6')), inference(resolution, [status(thm)], [c_1219, c_12])).
% 4.78/1.92  tff(c_1336, plain, (![A_296]: (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), A_296) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_296)))), inference(resolution, [status(thm)], [c_1240, c_4])).
% 4.78/1.92  tff(c_1374, plain, (![A_298]: (~r1_tarski(A_298, k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_298)))), inference(resolution, [status(thm)], [c_1336, c_6])).
% 4.78/1.92  tff(c_1378, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_1104, c_1374])).
% 4.78/1.92  tff(c_1382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1378])).
% 4.78/1.92  tff(c_1383, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1098])).
% 4.78/1.92  tff(c_1385, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1383])).
% 4.78/1.92  tff(c_957, plain, (![A_224]: (r2_hidden(k2_mcart_1('#skF_9'), A_224) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_224)))), inference(resolution, [status(thm)], [c_949, c_4])).
% 4.78/1.92  tff(c_981, plain, (![A_225]: (~r1_tarski(A_225, k2_mcart_1('#skF_9')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_225)))), inference(resolution, [status(thm)], [c_957, c_6])).
% 4.78/1.92  tff(c_986, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_981])).
% 4.78/1.92  tff(c_1389, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1385, c_986])).
% 4.78/1.92  tff(c_1393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1389])).
% 4.78/1.92  tff(c_1394, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1383])).
% 4.78/1.92  tff(c_1401, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_2])).
% 4.78/1.92  tff(c_1500, plain, (![A_337, B_334, C_333, D_336, A_335]: (r2_hidden(k1_mcart_1(A_335), k3_zfmisc_1(A_337, B_334, C_333)) | ~r2_hidden(A_335, k4_zfmisc_1(A_337, B_334, C_333, D_336)))), inference(superposition, [status(thm), theory('equality')], [c_929, c_14])).
% 4.78/1.92  tff(c_1511, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_1500])).
% 4.78/1.92  tff(c_910, plain, (![A_15, C_206, A_204, B_205]: (r2_hidden(k2_mcart_1(A_15), C_206) | ~r2_hidden(A_15, k3_zfmisc_1(A_204, B_205, C_206)))), inference(superposition, [status(thm), theory('equality')], [c_902, c_12])).
% 4.78/1.92  tff(c_1522, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_1511, c_910])).
% 4.78/1.92  tff(c_1568, plain, (![A_344]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_344) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_344)))), inference(resolution, [status(thm)], [c_1522, c_4])).
% 4.78/1.92  tff(c_1600, plain, (![A_345]: (~r1_tarski(A_345, k2_mcart_1(k1_mcart_1('#skF_9'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_345)))), inference(resolution, [status(thm)], [c_1568, c_6])).
% 4.78/1.92  tff(c_1604, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1401, c_1600])).
% 4.78/1.92  tff(c_1608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1604])).
% 4.78/1.92  tff(c_1609, plain, (~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7') | ~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_893])).
% 4.78/1.92  tff(c_1615, plain, (~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1609])).
% 4.78/1.92  tff(c_1710, plain, (![D_376, C_375, A_374, B_377, E_373]: (k11_mcart_1(A_374, B_377, C_375, D_376, E_373)=k2_mcart_1(E_373) | ~m1_subset_1(E_373, k4_zfmisc_1(A_374, B_377, C_375, D_376)) | k1_xboole_0=D_376 | k1_xboole_0=C_375 | k1_xboole_0=B_377 | k1_xboole_0=A_374)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.92  tff(c_1714, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_1710])).
% 4.78/1.92  tff(c_1765, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1714])).
% 4.78/1.92  tff(c_1768, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_2])).
% 4.78/1.92  tff(c_1636, plain, (![C_352, A_353, B_354]: (r2_hidden(C_352, A_353) | ~r2_hidden(C_352, B_354) | ~m1_subset_1(B_354, k1_zfmisc_1(A_353)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.78/1.92  tff(c_1779, plain, (![A_386]: (r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), A_386) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_386)))), inference(resolution, [status(thm)], [c_894, c_1636])).
% 4.78/1.92  tff(c_1827, plain, (![A_396]: (~r1_tarski(A_396, k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_396)))), inference(resolution, [status(thm)], [c_1779, c_6])).
% 4.78/1.92  tff(c_1831, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1768, c_1827])).
% 4.78/1.92  tff(c_1835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1831])).
% 4.78/1.92  tff(c_1837, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1714])).
% 4.78/1.92  tff(c_1891, plain, (![C_406, A_405, B_408, D_407, E_404]: (k2_mcart_1(k1_mcart_1(E_404))=k10_mcart_1(A_405, B_408, C_406, D_407, E_404) | ~m1_subset_1(E_404, k4_zfmisc_1(A_405, B_408, C_406, D_407)) | k1_xboole_0=D_407 | k1_xboole_0=C_406 | k1_xboole_0=B_408 | k1_xboole_0=A_405)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.92  tff(c_1894, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_1891])).
% 4.78/1.92  tff(c_1897, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1837, c_1894])).
% 4.78/1.92  tff(c_2146, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1897])).
% 4.78/1.92  tff(c_2160, plain, (![A_445]: (r1_tarski('#skF_2', A_445))), inference(demodulation, [status(thm), theory('equality')], [c_2146, c_2])).
% 4.78/1.92  tff(c_1646, plain, (![A_355, B_356, C_357, D_358]: (k2_zfmisc_1(k3_zfmisc_1(A_355, B_356, C_357), D_358)=k4_zfmisc_1(A_355, B_356, C_357, D_358))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.78/1.92  tff(c_1935, plain, (![A_424, C_427, D_423, A_425, B_426]: (r2_hidden(k1_mcart_1(A_425), k3_zfmisc_1(A_424, B_426, C_427)) | ~r2_hidden(A_425, k4_zfmisc_1(A_424, B_426, C_427, D_423)))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_14])).
% 4.78/1.92  tff(c_1946, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_1935])).
% 4.78/1.92  tff(c_1617, plain, (![A_349, B_350, C_351]: (k2_zfmisc_1(k2_zfmisc_1(A_349, B_350), C_351)=k3_zfmisc_1(A_349, B_350, C_351))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.78/1.92  tff(c_1627, plain, (![A_15, A_349, B_350, C_351]: (r2_hidden(k1_mcart_1(A_15), k2_zfmisc_1(A_349, B_350)) | ~r2_hidden(A_15, k3_zfmisc_1(A_349, B_350, C_351)))), inference(superposition, [status(thm), theory('equality')], [c_1617, c_14])).
% 4.78/1.92  tff(c_1962, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1946, c_1627])).
% 4.78/1.92  tff(c_1983, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_6')), inference(resolution, [status(thm)], [c_1962, c_12])).
% 4.78/1.92  tff(c_2102, plain, (![A_442]: (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), A_442) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_442)))), inference(resolution, [status(thm)], [c_1983, c_4])).
% 4.78/1.92  tff(c_2133, plain, (![A_442]: (~r1_tarski(A_442, k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_442)))), inference(resolution, [status(thm)], [c_2102, c_6])).
% 4.78/1.92  tff(c_2164, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_2160, c_2133])).
% 4.78/1.92  tff(c_2184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2164])).
% 4.78/1.92  tff(c_2186, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1897])).
% 4.78/1.92  tff(c_1947, plain, (![D_431, C_430, A_429, B_432, E_428]: (k8_mcart_1(A_429, B_432, C_430, D_431, E_428)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_428))) | ~m1_subset_1(E_428, k4_zfmisc_1(A_429, B_432, C_430, D_431)) | k1_xboole_0=D_431 | k1_xboole_0=C_430 | k1_xboole_0=B_432 | k1_xboole_0=A_429)), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.16/1.92  tff(c_1949, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_1947])).
% 5.16/1.92  tff(c_1952, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1837, c_1949])).
% 5.16/1.92  tff(c_2207, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2186, c_1952])).
% 5.16/1.92  tff(c_2208, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2207])).
% 5.16/1.92  tff(c_1625, plain, (![A_15, C_351, A_349, B_350]: (r2_hidden(k2_mcart_1(A_15), C_351) | ~r2_hidden(A_15, k3_zfmisc_1(A_349, B_350, C_351)))), inference(superposition, [status(thm), theory('equality')], [c_1617, c_12])).
% 5.16/1.92  tff(c_1963, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_1946, c_1625])).
% 5.16/1.92  tff(c_2031, plain, (![A_438]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_438) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_438)))), inference(resolution, [status(thm)], [c_1963, c_4])).
% 5.16/1.92  tff(c_2063, plain, (![A_439]: (~r1_tarski(A_439, k2_mcart_1(k1_mcart_1('#skF_9'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_439)))), inference(resolution, [status(thm)], [c_2031, c_6])).
% 5.16/1.92  tff(c_2068, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_2063])).
% 5.16/1.92  tff(c_2211, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2208, c_2068])).
% 5.16/1.92  tff(c_2222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_2211])).
% 5.16/1.92  tff(c_2224, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2207])).
% 5.16/1.92  tff(c_1917, plain, (![C_416, E_414, A_415, B_418, D_417]: (k9_mcart_1(A_415, B_418, C_416, D_417, E_414)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_414))) | ~m1_subset_1(E_414, k4_zfmisc_1(A_415, B_418, C_416, D_417)) | k1_xboole_0=D_417 | k1_xboole_0=C_416 | k1_xboole_0=B_418 | k1_xboole_0=A_415)), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.16/1.92  tff(c_1919, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_1917])).
% 5.16/1.92  tff(c_1922, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1837, c_1919])).
% 5.16/1.92  tff(c_2187, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1922])).
% 5.16/1.92  tff(c_2188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2186, c_2187])).
% 5.16/1.92  tff(c_2189, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitRight, [status(thm)], [c_1922])).
% 5.16/1.92  tff(c_2305, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_2224, c_2189])).
% 5.16/1.92  tff(c_2306, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitLeft, [status(thm)], [c_2305])).
% 5.16/1.92  tff(c_2310, plain, (r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2306, c_1983])).
% 5.16/1.92  tff(c_2312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1615, c_2310])).
% 5.16/1.92  tff(c_2313, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2305])).
% 5.16/1.92  tff(c_1664, plain, (![C_368, B_367, A_366, A_365, D_364]: (r2_hidden(k2_mcart_1(A_366), D_364) | ~r2_hidden(A_366, k4_zfmisc_1(A_365, B_367, C_368, D_364)))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_12])).
% 5.16/1.92  tff(c_1667, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_26, c_1664])).
% 5.16/1.92  tff(c_1675, plain, (![A_369]: (r2_hidden(k2_mcart_1('#skF_9'), A_369) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_369)))), inference(resolution, [status(thm)], [c_1667, c_4])).
% 5.16/1.92  tff(c_1699, plain, (![A_370]: (~r1_tarski(A_370, k2_mcart_1('#skF_9')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_370)))), inference(resolution, [status(thm)], [c_1675, c_6])).
% 5.16/1.92  tff(c_1704, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1699])).
% 5.16/1.92  tff(c_2326, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_1704])).
% 5.16/1.92  tff(c_2330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2326])).
% 5.16/1.92  tff(c_2331, plain, (~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_1609])).
% 5.16/1.92  tff(c_2399, plain, (![E_472, D_475, C_474, B_476, A_473]: (k11_mcart_1(A_473, B_476, C_474, D_475, E_472)=k2_mcart_1(E_472) | ~m1_subset_1(E_472, k4_zfmisc_1(A_473, B_476, C_474, D_475)) | k1_xboole_0=D_475 | k1_xboole_0=C_474 | k1_xboole_0=B_476 | k1_xboole_0=A_473)), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.16/1.92  tff(c_2403, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_2399])).
% 5.16/1.92  tff(c_2434, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2403])).
% 5.16/1.92  tff(c_2437, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2434, c_2])).
% 5.16/1.92  tff(c_2357, plain, (![C_455, A_456, B_457]: (r2_hidden(C_455, A_456) | ~r2_hidden(C_455, B_457) | ~m1_subset_1(B_457, k1_zfmisc_1(A_456)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.16/1.92  tff(c_2510, plain, (![A_494]: (r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), A_494) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_494)))), inference(resolution, [status(thm)], [c_894, c_2357])).
% 5.16/1.92  tff(c_2597, plain, (![A_507]: (~r1_tarski(A_507, k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_507)))), inference(resolution, [status(thm)], [c_2510, c_6])).
% 5.16/1.92  tff(c_2601, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2437, c_2597])).
% 5.16/1.92  tff(c_2605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2601])).
% 5.16/1.92  tff(c_2607, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_2403])).
% 5.16/1.92  tff(c_2676, plain, (![E_521, A_522, B_525, D_524, C_523]: (k2_mcart_1(k1_mcart_1(E_521))=k10_mcart_1(A_522, B_525, C_523, D_524, E_521) | ~m1_subset_1(E_521, k4_zfmisc_1(A_522, B_525, C_523, D_524)) | k1_xboole_0=D_524 | k1_xboole_0=C_523 | k1_xboole_0=B_525 | k1_xboole_0=A_522)), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.16/1.92  tff(c_2679, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_28, c_2676])).
% 5.16/1.92  tff(c_2682, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2607, c_2679])).
% 5.16/1.92  tff(c_2800, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2682])).
% 5.16/1.92  tff(c_2332, plain, (r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_1609])).
% 5.16/1.92  tff(c_2711, plain, (![A_527]: (r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), A_527) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_527)))), inference(resolution, [status(thm)], [c_2332, c_2357])).
% 5.16/1.92  tff(c_2761, plain, (![A_530]: (~r1_tarski(A_530, k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_530)))), inference(resolution, [status(thm)], [c_2711, c_6])).
% 5.16/1.92  tff(c_2766, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_2761])).
% 5.16/1.92  tff(c_2803, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2800, c_2766])).
% 5.16/1.92  tff(c_2812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2803])).
% 5.16/1.92  tff(c_2813, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitRight, [status(thm)], [c_2682])).
% 5.16/1.92  tff(c_2815, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitLeft, [status(thm)], [c_2813])).
% 5.16/1.92  tff(c_2372, plain, (![A_463, B_464, C_465, D_466]: (k2_zfmisc_1(k3_zfmisc_1(A_463, B_464, C_465), D_466)=k4_zfmisc_1(A_463, B_464, C_465, D_466))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.16/1.92  tff(c_2820, plain, (![B_551, A_553, D_550, C_552, A_554]: (r2_hidden(k1_mcart_1(A_553), k3_zfmisc_1(A_554, B_551, C_552)) | ~r2_hidden(A_553, k4_zfmisc_1(A_554, B_551, C_552, D_550)))), inference(superposition, [status(thm), theory('equality')], [c_2372, c_14])).
% 5.16/1.92  tff(c_2835, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_2820])).
% 5.16/1.92  tff(c_2354, plain, (![A_452, C_453, B_454]: (r2_hidden(k2_mcart_1(A_452), C_453) | ~r2_hidden(A_452, k2_zfmisc_1(B_454, C_453)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.16/1.92  tff(c_2356, plain, (![A_452, C_10, A_8, B_9]: (r2_hidden(k2_mcart_1(A_452), C_10) | ~r2_hidden(A_452, k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2354])).
% 5.16/1.92  tff(c_2839, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_2835, c_2356])).
% 5.16/1.92  tff(c_2847, plain, (r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2815, c_2839])).
% 5.16/1.92  tff(c_2849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2331, c_2847])).
% 5.16/1.92  tff(c_2850, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2813])).
% 5.16/1.92  tff(c_2852, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2850])).
% 5.16/1.92  tff(c_2862, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2852, c_2])).
% 5.16/1.92  tff(c_2886, plain, (![C_558, B_557, A_559, A_560, D_556]: (r2_hidden(k1_mcart_1(A_559), k3_zfmisc_1(A_560, B_557, C_558)) | ~r2_hidden(A_559, k4_zfmisc_1(A_560, B_557, C_558, D_556)))), inference(superposition, [status(thm), theory('equality')], [c_2372, c_14])).
% 5.16/1.92  tff(c_2901, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_2886])).
% 5.16/1.92  tff(c_2912, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_2901, c_2356])).
% 5.16/1.92  tff(c_2988, plain, (![A_571]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_571) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_571)))), inference(resolution, [status(thm)], [c_2912, c_4])).
% 5.16/1.92  tff(c_3020, plain, (![A_572]: (~r1_tarski(A_572, k2_mcart_1(k1_mcart_1('#skF_9'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_572)))), inference(resolution, [status(thm)], [c_2988, c_6])).
% 5.16/1.92  tff(c_3024, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2862, c_3020])).
% 5.16/1.92  tff(c_3028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3024])).
% 5.16/1.92  tff(c_3029, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2850])).
% 5.16/1.92  tff(c_2388, plain, (![A_470, B_468, A_471, C_469, D_467]: (r2_hidden(k2_mcart_1(A_470), D_467) | ~r2_hidden(A_470, k4_zfmisc_1(A_471, B_468, C_469, D_467)))), inference(superposition, [status(thm), theory('equality')], [c_2372, c_12])).
% 5.16/1.92  tff(c_2391, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_26, c_2388])).
% 5.16/1.92  tff(c_2404, plain, (![A_477]: (r2_hidden(k2_mcart_1('#skF_9'), A_477) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_477)))), inference(resolution, [status(thm)], [c_2391, c_4])).
% 5.16/1.92  tff(c_2428, plain, (![A_478]: (~r1_tarski(A_478, k2_mcart_1('#skF_9')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_478)))), inference(resolution, [status(thm)], [c_2404, c_6])).
% 5.16/1.92  tff(c_2433, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_2428])).
% 5.16/1.92  tff(c_3038, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3029, c_2433])).
% 5.16/1.92  tff(c_3043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_3038])).
% 5.16/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/1.92  
% 5.16/1.92  Inference rules
% 5.16/1.92  ----------------------
% 5.16/1.92  #Ref     : 0
% 5.16/1.92  #Sup     : 694
% 5.16/1.92  #Fact    : 0
% 5.16/1.92  #Define  : 0
% 5.16/1.92  #Split   : 50
% 5.16/1.92  #Chain   : 0
% 5.16/1.92  #Close   : 0
% 5.16/1.92  
% 5.16/1.92  Ordering : KBO
% 5.16/1.92  
% 5.16/1.92  Simplification rules
% 5.16/1.92  ----------------------
% 5.16/1.92  #Subsume      : 73
% 5.16/1.92  #Demod        : 417
% 5.16/1.92  #Tautology    : 103
% 5.16/1.92  #SimpNegUnit  : 27
% 5.16/1.92  #BackRed      : 148
% 5.16/1.92  
% 5.16/1.92  #Partial instantiations: 0
% 5.16/1.92  #Strategies tried      : 1
% 5.16/1.92  
% 5.16/1.92  Timing (in seconds)
% 5.16/1.92  ----------------------
% 5.16/1.92  Preprocessing        : 0.32
% 5.16/1.92  Parsing              : 0.17
% 5.16/1.92  CNF conversion       : 0.03
% 5.16/1.92  Main loop            : 0.79
% 5.16/1.92  Inferencing          : 0.27
% 5.16/1.92  Reduction            : 0.26
% 5.16/1.92  Demodulation         : 0.18
% 5.16/1.92  BG Simplification    : 0.04
% 5.16/1.92  Subsumption          : 0.14
% 5.16/1.92  Abstraction          : 0.05
% 5.16/1.92  MUC search           : 0.00
% 5.16/1.92  Cooper               : 0.00
% 5.16/1.92  Total                : 1.18
% 5.16/1.93  Index Insertion      : 0.00
% 5.16/1.93  Index Deletion       : 0.00
% 5.16/1.93  Index Matching       : 0.00
% 5.16/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
