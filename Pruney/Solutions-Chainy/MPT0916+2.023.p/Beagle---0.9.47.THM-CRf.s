%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:13 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 853 expanded)
%              Number of leaves         :   33 ( 288 expanded)
%              Depth                    :   12
%              Number of atoms          :  349 (2394 expanded)
%              Number of equality atoms :  104 ( 592 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1301,plain,(
    ! [A_239,B_240] :
      ( ~ r2_hidden('#skF_1'(A_239,B_240),B_240)
      | r1_tarski(A_239,B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1306,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_1301])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_34,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1339,plain,(
    ! [A_248,C_249,B_250] :
      ( r2_hidden(k2_mcart_1(A_248),C_249)
      | ~ r2_hidden(A_248,k2_zfmisc_1(B_250,C_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1441,plain,(
    ! [A_271,C_272,A_273,B_274] :
      ( r2_hidden(k2_mcart_1(A_271),C_272)
      | ~ r2_hidden(A_271,k3_zfmisc_1(A_273,B_274,C_272)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1339])).

tff(c_1460,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_1441])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_1321,plain,(
    ! [A_245,B_246,C_247] : k2_zfmisc_1(k2_zfmisc_1(A_245,B_246),C_247) = k3_zfmisc_1(A_245,B_246,C_247) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1883,plain,(
    ! [A_337,A_338,B_339,C_340] :
      ( r2_hidden(k1_mcart_1(A_337),k2_zfmisc_1(A_338,B_339))
      | ~ r2_hidden(A_337,k3_zfmisc_1(A_338,B_339,C_340)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_24])).

tff(c_1925,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_1883])).

tff(c_22,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1936,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1925,c_22])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1994,plain,(
    ! [B_344] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),B_344)
      | ~ r1_tarski('#skF_7',B_344) ) ),
    inference(resolution,[status(thm)],[c_1936,c_2])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_55,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_44])).

tff(c_32,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8')
    | ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_57,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_66,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_155,plain,(
    ! [A_70,B_71,C_72] : k2_zfmisc_1(k2_zfmisc_1(A_70,B_71),C_72) = k3_zfmisc_1(A_70,B_71,C_72) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_936,plain,(
    ! [A_192,A_193,B_194,C_195] :
      ( r2_hidden(k1_mcart_1(A_192),k2_zfmisc_1(A_193,B_194))
      | ~ r2_hidden(A_192,k3_zfmisc_1(A_193,B_194,C_195)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_24])).

tff(c_971,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_936])).

tff(c_980,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_971,c_22])).

tff(c_1035,plain,(
    ! [B_198] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),B_198)
      | ~ r1_tarski('#skF_7',B_198) ) ),
    inference(resolution,[status(thm)],[c_980,c_2])).

tff(c_86,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_399,plain,(
    ! [A_118,B_119,B_120] :
      ( r2_hidden('#skF_1'(A_118,B_119),B_120)
      | ~ r1_tarski(A_118,B_120)
      | r1_tarski(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_36,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_221,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_mcart_1(A_79,B_80,C_81,D_82) = k2_mcart_1(D_82)
      | ~ m1_subset_1(D_82,k3_zfmisc_1(A_79,B_80,C_81))
      | k1_xboole_0 = C_81
      | k1_xboole_0 = B_80
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_225,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_221])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [C_58,A_11] :
      ( ~ r2_hidden(C_58,k1_xboole_0)
      | ~ r2_hidden(C_58,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_255,plain,(
    ! [C_58,A_11] :
      ( ~ r2_hidden(C_58,'#skF_3')
      | ~ r2_hidden(C_58,A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_102])).

tff(c_529,plain,(
    ! [A_135,B_136,A_137] :
      ( ~ r2_hidden('#skF_1'(A_135,B_136),A_137)
      | ~ r1_tarski(A_135,'#skF_3')
      | r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_399,c_255])).

tff(c_539,plain,(
    ! [A_138,B_139] :
      ( ~ r1_tarski(A_138,'#skF_3')
      | r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_529])).

tff(c_552,plain,(
    ! [B_139] : r1_tarski('#skF_6',B_139) ),
    inference(resolution,[status(thm)],[c_55,c_539])).

tff(c_599,plain,(
    ! [A_149,A_150,B_151,C_152] :
      ( r2_hidden(k1_mcart_1(A_149),k2_zfmisc_1(A_150,B_151))
      | ~ r2_hidden(A_149,k3_zfmisc_1(A_150,B_151,C_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_24])).

tff(c_637,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_599])).

tff(c_647,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_637,c_24])).

tff(c_653,plain,(
    ! [B_2] :
      ( r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),B_2)
      | ~ r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_647,c_2])).

tff(c_659,plain,(
    ! [B_2] : r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_653])).

tff(c_694,plain,(
    ! [B_154] : r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),B_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_653])).

tff(c_702,plain,(
    ! [A_11] : ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),A_11) ),
    inference(resolution,[status(thm)],[c_694,c_255])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_702])).

tff(c_723,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_782,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k6_mcart_1(A_164,B_165,C_166,D_167) = k2_mcart_1(k1_mcart_1(D_167))
      | ~ m1_subset_1(D_167,k3_zfmisc_1(A_164,B_165,C_166))
      | k1_xboole_0 = C_166
      | k1_xboole_0 = B_165
      | k1_xboole_0 = A_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_785,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_782])).

tff(c_788,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_723,c_785])).

tff(c_791,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_788])).

tff(c_800,plain,(
    ! [C_58,A_11] :
      ( ~ r2_hidden(C_58,'#skF_4')
      | ~ r2_hidden(C_58,A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_102])).

tff(c_1041,plain,(
    ! [A_11] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_11)
      | ~ r1_tarski('#skF_7','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1035,c_800])).

tff(c_1056,plain,(
    ! [A_11] : ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1041])).

tff(c_1063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1056,c_980])).

tff(c_1065,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_788])).

tff(c_728,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k5_mcart_1(A_155,B_156,C_157,D_158) = k1_mcart_1(k1_mcart_1(D_158))
      | ~ m1_subset_1(D_158,k3_zfmisc_1(A_155,B_156,C_157))
      | k1_xboole_0 = C_157
      | k1_xboole_0 = B_156
      | k1_xboole_0 = A_155 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_731,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_728])).

tff(c_734,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_723,c_731])).

tff(c_1099,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_734])).

tff(c_1100,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_181,plain,(
    ! [A_74,C_75,A_76,B_77] :
      ( r2_hidden(k2_mcart_1(A_74),C_75)
      | ~ r2_hidden(A_74,k3_zfmisc_1(A_76,B_77,C_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_22])).

tff(c_196,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_181])).

tff(c_200,plain,(
    ! [B_78] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_78)
      | ~ r1_tarski('#skF_8',B_78) ) ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_232,plain,(
    ! [B_87,B_88] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_87)
      | ~ r1_tarski(B_88,B_87)
      | ~ r1_tarski('#skF_8',B_88) ) ),
    inference(resolution,[status(thm)],[c_200,c_2])).

tff(c_242,plain,
    ( r2_hidden(k2_mcart_1('#skF_9'),'#skF_5')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_232])).

tff(c_249,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_242])).

tff(c_736,plain,(
    ! [B_159] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_159)
      | ~ r1_tarski('#skF_5',B_159) ) ),
    inference(resolution,[status(thm)],[c_249,c_2])).

tff(c_753,plain,(
    ! [A_11] :
      ( ~ r2_hidden(k2_mcart_1('#skF_9'),A_11)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_736,c_102])).

tff(c_761,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_1103,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_761])).

tff(c_1114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1103])).

tff(c_1115,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_1229,plain,(
    ! [A_227,A_228,B_229,C_230] :
      ( r2_hidden(k1_mcart_1(A_227),k2_zfmisc_1(A_228,B_229))
      | ~ r2_hidden(A_227,k3_zfmisc_1(A_228,B_229,C_230)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_24])).

tff(c_1267,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_1229])).

tff(c_1269,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1267,c_24])).

tff(c_1275,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1269])).

tff(c_1277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1275])).

tff(c_1278,plain,(
    ! [A_11] : ~ r2_hidden(k2_mcart_1('#skF_9'),A_11) ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_1290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1278,c_249])).

tff(c_1292,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1354,plain,(
    ! [C_251,B_252,A_253] :
      ( r2_hidden(C_251,B_252)
      | ~ r2_hidden(C_251,A_253)
      | ~ r1_tarski(A_253,B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1368,plain,(
    ! [B_252] :
      ( r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),B_252)
      | ~ r1_tarski('#skF_6',B_252) ) ),
    inference(resolution,[status(thm)],[c_1292,c_1354])).

tff(c_1388,plain,(
    ! [A_259,B_260,C_261,D_262] :
      ( k7_mcart_1(A_259,B_260,C_261,D_262) = k2_mcart_1(D_262)
      | ~ m1_subset_1(D_262,k3_zfmisc_1(A_259,B_260,C_261))
      | k1_xboole_0 = C_261
      | k1_xboole_0 = B_260
      | k1_xboole_0 = A_259 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1392,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_1388])).

tff(c_1490,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1392])).

tff(c_1370,plain,(
    ! [A_254,B_255,C_256] :
      ( ~ r1_xboole_0(A_254,B_255)
      | ~ r2_hidden(C_256,B_255)
      | ~ r2_hidden(C_256,A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1373,plain,(
    ! [C_256,A_11] :
      ( ~ r2_hidden(C_256,k1_xboole_0)
      | ~ r2_hidden(C_256,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_1370])).

tff(c_1518,plain,(
    ! [C_287,A_288] :
      ( ~ r2_hidden(C_287,'#skF_3')
      | ~ r2_hidden(C_287,A_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1373])).

tff(c_1524,plain,(
    ! [A_288] :
      ( ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),A_288)
      | ~ r1_tarski('#skF_6','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1368,c_1518])).

tff(c_1537,plain,(
    ! [A_288] : ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),A_288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1524])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1537,c_1292])).

tff(c_1549,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1392])).

tff(c_1464,plain,(
    ! [A_275,B_276,C_277,D_278] :
      ( k6_mcart_1(A_275,B_276,C_277,D_278) = k2_mcart_1(k1_mcart_1(D_278))
      | ~ m1_subset_1(D_278,k3_zfmisc_1(A_275,B_276,C_277))
      | k1_xboole_0 = C_277
      | k1_xboole_0 = B_276
      | k1_xboole_0 = A_275 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1468,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_1464])).

tff(c_1580,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1549,c_1468])).

tff(c_1581,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1580])).

tff(c_1590,plain,(
    ! [C_256,A_11] :
      ( ~ r2_hidden(C_256,'#skF_4')
      | ~ r2_hidden(C_256,A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1373])).

tff(c_2002,plain,(
    ! [A_11] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_11)
      | ~ r1_tarski('#skF_7','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1994,c_1590])).

tff(c_2018,plain,(
    ! [A_11] : ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2002])).

tff(c_2026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2018,c_1936])).

tff(c_2028,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1580])).

tff(c_1548,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1392])).

tff(c_2030,plain,
    ( k1_xboole_0 = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_2028,c_1548])).

tff(c_2031,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2030])).

tff(c_1291,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1338,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1291])).

tff(c_2032,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_1338])).

tff(c_2035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_2032])).

tff(c_2036,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2030])).

tff(c_1469,plain,(
    ! [B_279] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_279)
      | ~ r1_tarski('#skF_8',B_279) ) ),
    inference(resolution,[status(thm)],[c_1460,c_2])).

tff(c_1485,plain,(
    ! [A_11] :
      ( ~ r2_hidden(k2_mcart_1('#skF_9'),A_11)
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1469,c_1373])).

tff(c_1489,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1485])).

tff(c_2042,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_1489])).

tff(c_2051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2042])).

tff(c_2052,plain,(
    ! [A_11] : ~ r2_hidden(k2_mcart_1('#skF_9'),A_11) ),
    inference(splitRight,[status(thm)],[c_1485])).

tff(c_2056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2052,c_1460])).

tff(c_2057,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1291])).

tff(c_2224,plain,(
    ! [A_370,B_371,C_372,D_373] :
      ( k7_mcart_1(A_370,B_371,C_372,D_373) = k2_mcart_1(D_373)
      | ~ m1_subset_1(D_373,k3_zfmisc_1(A_370,B_371,C_372))
      | k1_xboole_0 = C_372
      | k1_xboole_0 = B_371
      | k1_xboole_0 = A_370 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2228,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_2224])).

tff(c_2250,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2228])).

tff(c_2117,plain,(
    ! [C_359,B_360,A_361] :
      ( r2_hidden(C_359,B_360)
      | ~ r2_hidden(C_359,A_361)
      | ~ r1_tarski(A_361,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2183,plain,(
    ! [B_368] :
      ( r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),B_368)
      | ~ r1_tarski('#skF_6',B_368) ) ),
    inference(resolution,[status(thm)],[c_1292,c_2117])).

tff(c_2059,plain,(
    ! [A_345,B_346,C_347] :
      ( ~ r1_xboole_0(A_345,B_346)
      | ~ r2_hidden(C_347,B_346)
      | ~ r2_hidden(C_347,A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2062,plain,(
    ! [C_347,A_11] :
      ( ~ r2_hidden(C_347,k1_xboole_0)
      | ~ r2_hidden(C_347,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_2059])).

tff(c_2201,plain,(
    ! [A_11] :
      ( ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),A_11)
      | ~ r1_tarski('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2183,c_2062])).

tff(c_2223,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2201])).

tff(c_2251,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_2223])).

tff(c_2260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2251])).

tff(c_2262,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2228])).

tff(c_2267,plain,(
    ! [A_378,B_379,C_380,D_381] :
      ( k6_mcart_1(A_378,B_379,C_380,D_381) = k2_mcart_1(k1_mcart_1(D_381))
      | ~ m1_subset_1(D_381,k3_zfmisc_1(A_378,B_379,C_380))
      | k1_xboole_0 = C_380
      | k1_xboole_0 = B_379
      | k1_xboole_0 = A_378 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2270,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_2267])).

tff(c_2273,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2262,c_2270])).

tff(c_2448,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2273])).

tff(c_2339,plain,(
    ! [A_395,B_396,B_397] :
      ( r2_hidden('#skF_1'(A_395,B_396),B_397)
      | ~ r1_tarski(A_395,B_397)
      | r1_tarski(A_395,B_396) ) ),
    inference(resolution,[status(thm)],[c_6,c_2117])).

tff(c_2428,plain,(
    ! [A_408,B_409,A_410] :
      ( ~ r2_hidden('#skF_1'(A_408,B_409),A_410)
      | ~ r1_tarski(A_408,k1_xboole_0)
      | r1_tarski(A_408,B_409) ) ),
    inference(resolution,[status(thm)],[c_2339,c_2062])).

tff(c_2436,plain,(
    ! [A_1,B_2] :
      ( ~ r1_tarski(A_1,k1_xboole_0)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_2428])).

tff(c_2520,plain,(
    ! [A_418,B_419] :
      ( ~ r1_tarski(A_418,'#skF_4')
      | r1_tarski(A_418,B_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2436])).

tff(c_2533,plain,(
    ! [B_419] : r1_tarski('#skF_7',B_419) ),
    inference(resolution,[status(thm)],[c_56,c_2520])).

tff(c_2547,plain,(
    ! [A_421,A_422,B_423,C_424] :
      ( r2_hidden(k1_mcart_1(A_421),k2_zfmisc_1(A_422,B_423))
      | ~ r2_hidden(A_421,k3_zfmisc_1(A_422,B_423,C_424)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_24])).

tff(c_2589,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_2547])).

tff(c_2597,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2589,c_22])).

tff(c_2600,plain,(
    ! [B_2] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),B_2)
      | ~ r1_tarski('#skF_7',B_2) ) ),
    inference(resolution,[status(thm)],[c_2597,c_2])).

tff(c_2603,plain,(
    ! [B_2] : r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2600])).

tff(c_2632,plain,(
    ! [B_426] : r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),B_426) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2600])).

tff(c_2459,plain,(
    ! [C_347,A_11] :
      ( ~ r2_hidden(C_347,'#skF_4')
      | ~ r2_hidden(C_347,A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2062])).

tff(c_2638,plain,(
    ! [A_11] : ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),A_11) ),
    inference(resolution,[status(thm)],[c_2632,c_2459])).

tff(c_2654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_2638])).

tff(c_2655,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2273])).

tff(c_2657,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2655])).

tff(c_2749,plain,(
    ! [A_435,A_436,B_437,C_438] :
      ( r2_hidden(k1_mcart_1(A_435),k2_zfmisc_1(A_436,B_437))
      | ~ r2_hidden(A_435,k3_zfmisc_1(A_436,B_437,C_438)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_24])).

tff(c_2791,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_2749])).

tff(c_2797,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2791,c_22])).

tff(c_2803,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_2797])).

tff(c_2805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2057,c_2803])).

tff(c_2806,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2655])).

tff(c_2077,plain,(
    ! [A_350,C_351,B_352] :
      ( r2_hidden(k2_mcart_1(A_350),C_351)
      | ~ r2_hidden(A_350,k2_zfmisc_1(B_352,C_351)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2143,plain,(
    ! [A_363,C_364,A_365,B_366] :
      ( r2_hidden(k2_mcart_1(A_363),C_364)
      | ~ r2_hidden(A_363,k3_zfmisc_1(A_365,B_366,C_364)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2077])).

tff(c_2158,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_2143])).

tff(c_2162,plain,(
    ! [B_367] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_367)
      | ~ r1_tarski('#skF_8',B_367) ) ),
    inference(resolution,[status(thm)],[c_2158,c_2])).

tff(c_2232,plain,(
    ! [B_376,B_377] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_376)
      | ~ r1_tarski(B_377,B_376)
      | ~ r1_tarski('#skF_8',B_377) ) ),
    inference(resolution,[status(thm)],[c_2162,c_2])).

tff(c_2242,plain,
    ( r2_hidden(k2_mcart_1('#skF_9'),'#skF_5')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_2232])).

tff(c_2249,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_2242])).

tff(c_2275,plain,(
    ! [B_382] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_382)
      | ~ r1_tarski('#skF_5',B_382) ) ),
    inference(resolution,[status(thm)],[c_2249,c_2])).

tff(c_2293,plain,(
    ! [A_11] :
      ( ~ r2_hidden(k2_mcart_1('#skF_9'),A_11)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2275,c_2062])).

tff(c_2303,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2293])).

tff(c_2811,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2806,c_2303])).

tff(c_2823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_2811])).

tff(c_2824,plain,(
    ! [A_11] : ~ r2_hidden(k2_mcart_1('#skF_9'),A_11) ),
    inference(splitRight,[status(thm)],[c_2293])).

tff(c_2880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2824,c_2249])).

tff(c_2881,plain,(
    ! [A_11] : ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),A_11) ),
    inference(splitRight,[status(thm)],[c_2201])).

tff(c_2885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2881,c_1292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.95  
% 5.05/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 5.05/1.96  
% 5.05/1.96  %Foreground sorts:
% 5.05/1.96  
% 5.05/1.96  
% 5.05/1.96  %Background operators:
% 5.05/1.96  
% 5.05/1.96  
% 5.05/1.96  %Foreground operators:
% 5.05/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.05/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.05/1.96  tff('#skF_7', type, '#skF_7': $i).
% 5.05/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.05/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.05/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.05/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.05/1.96  tff('#skF_9', type, '#skF_9': $i).
% 5.05/1.96  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 5.05/1.96  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.05/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.05/1.96  tff('#skF_8', type, '#skF_8': $i).
% 5.05/1.96  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 5.05/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.96  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.05/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.05/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.05/1.96  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 5.05/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.05/1.96  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.05/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.05/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.05/1.96  
% 5.05/1.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.05/1.99  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 5.05/1.99  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.05/1.99  tff(f_58, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.05/1.99  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 5.05/1.99  tff(f_84, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 5.05/1.99  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.05/1.99  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.05/1.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.99  tff(c_1301, plain, (![A_239, B_240]: (~r2_hidden('#skF_1'(A_239, B_240), B_240) | r1_tarski(A_239, B_240))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.99  tff(c_1306, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_1301])).
% 5.05/1.99  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.99  tff(c_44, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.05/1.99  tff(c_54, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_44])).
% 5.05/1.99  tff(c_34, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.99  tff(c_20, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.05/1.99  tff(c_1339, plain, (![A_248, C_249, B_250]: (r2_hidden(k2_mcart_1(A_248), C_249) | ~r2_hidden(A_248, k2_zfmisc_1(B_250, C_249)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.05/1.99  tff(c_1441, plain, (![A_271, C_272, A_273, B_274]: (r2_hidden(k2_mcart_1(A_271), C_272) | ~r2_hidden(A_271, k3_zfmisc_1(A_273, B_274, C_272)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1339])).
% 5.05/1.99  tff(c_1460, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_34, c_1441])).
% 5.05/1.99  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.99  tff(c_56, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_44])).
% 5.05/1.99  tff(c_1321, plain, (![A_245, B_246, C_247]: (k2_zfmisc_1(k2_zfmisc_1(A_245, B_246), C_247)=k3_zfmisc_1(A_245, B_246, C_247))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.05/1.99  tff(c_24, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.05/1.99  tff(c_1883, plain, (![A_337, A_338, B_339, C_340]: (r2_hidden(k1_mcart_1(A_337), k2_zfmisc_1(A_338, B_339)) | ~r2_hidden(A_337, k3_zfmisc_1(A_338, B_339, C_340)))), inference(superposition, [status(thm), theory('equality')], [c_1321, c_24])).
% 5.05/1.99  tff(c_1925, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_1883])).
% 5.05/1.99  tff(c_22, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.05/1.99  tff(c_1936, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_1925, c_22])).
% 5.05/1.99  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.99  tff(c_1994, plain, (![B_344]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), B_344) | ~r1_tarski('#skF_7', B_344))), inference(resolution, [status(thm)], [c_1936, c_2])).
% 5.05/1.99  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.99  tff(c_55, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_44])).
% 5.05/1.99  tff(c_32, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8') | ~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.99  tff(c_57, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 5.05/1.99  tff(c_66, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.99  tff(c_71, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_66])).
% 5.05/1.99  tff(c_155, plain, (![A_70, B_71, C_72]: (k2_zfmisc_1(k2_zfmisc_1(A_70, B_71), C_72)=k3_zfmisc_1(A_70, B_71, C_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.05/1.99  tff(c_936, plain, (![A_192, A_193, B_194, C_195]: (r2_hidden(k1_mcart_1(A_192), k2_zfmisc_1(A_193, B_194)) | ~r2_hidden(A_192, k3_zfmisc_1(A_193, B_194, C_195)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_24])).
% 5.05/1.99  tff(c_971, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_936])).
% 5.05/1.99  tff(c_980, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_971, c_22])).
% 5.05/1.99  tff(c_1035, plain, (![B_198]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), B_198) | ~r1_tarski('#skF_7', B_198))), inference(resolution, [status(thm)], [c_980, c_2])).
% 5.05/1.99  tff(c_86, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.99  tff(c_399, plain, (![A_118, B_119, B_120]: (r2_hidden('#skF_1'(A_118, B_119), B_120) | ~r1_tarski(A_118, B_120) | r1_tarski(A_118, B_119))), inference(resolution, [status(thm)], [c_6, c_86])).
% 5.05/1.99  tff(c_36, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.99  tff(c_221, plain, (![A_79, B_80, C_81, D_82]: (k7_mcart_1(A_79, B_80, C_81, D_82)=k2_mcart_1(D_82) | ~m1_subset_1(D_82, k3_zfmisc_1(A_79, B_80, C_81)) | k1_xboole_0=C_81 | k1_xboole_0=B_80 | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.05/1.99  tff(c_225, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_221])).
% 5.05/1.99  tff(c_250, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_225])).
% 5.05/1.99  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.05/1.99  tff(c_99, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.05/1.99  tff(c_102, plain, (![C_58, A_11]: (~r2_hidden(C_58, k1_xboole_0) | ~r2_hidden(C_58, A_11))), inference(resolution, [status(thm)], [c_14, c_99])).
% 5.05/1.99  tff(c_255, plain, (![C_58, A_11]: (~r2_hidden(C_58, '#skF_3') | ~r2_hidden(C_58, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_102])).
% 5.05/1.99  tff(c_529, plain, (![A_135, B_136, A_137]: (~r2_hidden('#skF_1'(A_135, B_136), A_137) | ~r1_tarski(A_135, '#skF_3') | r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_399, c_255])).
% 5.05/1.99  tff(c_539, plain, (![A_138, B_139]: (~r1_tarski(A_138, '#skF_3') | r1_tarski(A_138, B_139))), inference(resolution, [status(thm)], [c_6, c_529])).
% 5.05/1.99  tff(c_552, plain, (![B_139]: (r1_tarski('#skF_6', B_139))), inference(resolution, [status(thm)], [c_55, c_539])).
% 5.05/1.99  tff(c_599, plain, (![A_149, A_150, B_151, C_152]: (r2_hidden(k1_mcart_1(A_149), k2_zfmisc_1(A_150, B_151)) | ~r2_hidden(A_149, k3_zfmisc_1(A_150, B_151, C_152)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_24])).
% 5.05/1.99  tff(c_637, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_599])).
% 5.05/1.99  tff(c_647, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_637, c_24])).
% 5.05/1.99  tff(c_653, plain, (![B_2]: (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), B_2) | ~r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_647, c_2])).
% 5.05/1.99  tff(c_659, plain, (![B_2]: (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_653])).
% 5.05/1.99  tff(c_694, plain, (![B_154]: (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), B_154))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_653])).
% 5.05/1.99  tff(c_702, plain, (![A_11]: (~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), A_11))), inference(resolution, [status(thm)], [c_694, c_255])).
% 5.05/1.99  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_659, c_702])).
% 5.05/1.99  tff(c_723, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_225])).
% 5.05/1.99  tff(c_782, plain, (![A_164, B_165, C_166, D_167]: (k6_mcart_1(A_164, B_165, C_166, D_167)=k2_mcart_1(k1_mcart_1(D_167)) | ~m1_subset_1(D_167, k3_zfmisc_1(A_164, B_165, C_166)) | k1_xboole_0=C_166 | k1_xboole_0=B_165 | k1_xboole_0=A_164)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.05/1.99  tff(c_785, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_782])).
% 5.05/1.99  tff(c_788, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_723, c_785])).
% 5.05/1.99  tff(c_791, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_788])).
% 5.05/1.99  tff(c_800, plain, (![C_58, A_11]: (~r2_hidden(C_58, '#skF_4') | ~r2_hidden(C_58, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_791, c_102])).
% 5.05/1.99  tff(c_1041, plain, (![A_11]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_11) | ~r1_tarski('#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_1035, c_800])).
% 5.05/1.99  tff(c_1056, plain, (![A_11]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1041])).
% 5.05/1.99  tff(c_1063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1056, c_980])).
% 5.05/1.99  tff(c_1065, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_788])).
% 5.05/1.99  tff(c_728, plain, (![A_155, B_156, C_157, D_158]: (k5_mcart_1(A_155, B_156, C_157, D_158)=k1_mcart_1(k1_mcart_1(D_158)) | ~m1_subset_1(D_158, k3_zfmisc_1(A_155, B_156, C_157)) | k1_xboole_0=C_157 | k1_xboole_0=B_156 | k1_xboole_0=A_155)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.05/1.99  tff(c_731, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_728])).
% 5.05/1.99  tff(c_734, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_723, c_731])).
% 5.05/1.99  tff(c_1099, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1065, c_734])).
% 5.05/1.99  tff(c_1100, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1099])).
% 5.05/1.99  tff(c_181, plain, (![A_74, C_75, A_76, B_77]: (r2_hidden(k2_mcart_1(A_74), C_75) | ~r2_hidden(A_74, k3_zfmisc_1(A_76, B_77, C_75)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_22])).
% 5.05/1.99  tff(c_196, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_34, c_181])).
% 5.05/1.99  tff(c_200, plain, (![B_78]: (r2_hidden(k2_mcart_1('#skF_9'), B_78) | ~r1_tarski('#skF_8', B_78))), inference(resolution, [status(thm)], [c_196, c_2])).
% 5.05/1.99  tff(c_232, plain, (![B_87, B_88]: (r2_hidden(k2_mcart_1('#skF_9'), B_87) | ~r1_tarski(B_88, B_87) | ~r1_tarski('#skF_8', B_88))), inference(resolution, [status(thm)], [c_200, c_2])).
% 5.05/1.99  tff(c_242, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_54, c_232])).
% 5.05/1.99  tff(c_249, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_242])).
% 5.05/1.99  tff(c_736, plain, (![B_159]: (r2_hidden(k2_mcart_1('#skF_9'), B_159) | ~r1_tarski('#skF_5', B_159))), inference(resolution, [status(thm)], [c_249, c_2])).
% 5.05/1.99  tff(c_753, plain, (![A_11]: (~r2_hidden(k2_mcart_1('#skF_9'), A_11) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_736, c_102])).
% 5.05/1.99  tff(c_761, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_753])).
% 5.05/1.99  tff(c_1103, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_761])).
% 5.05/1.99  tff(c_1114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_1103])).
% 5.05/1.99  tff(c_1115, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_1099])).
% 5.05/1.99  tff(c_1229, plain, (![A_227, A_228, B_229, C_230]: (r2_hidden(k1_mcart_1(A_227), k2_zfmisc_1(A_228, B_229)) | ~r2_hidden(A_227, k3_zfmisc_1(A_228, B_229, C_230)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_24])).
% 5.05/1.99  tff(c_1267, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_1229])).
% 5.05/1.99  tff(c_1269, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_1267, c_24])).
% 5.05/1.99  tff(c_1275, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1269])).
% 5.05/1.99  tff(c_1277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1275])).
% 5.05/1.99  tff(c_1278, plain, (![A_11]: (~r2_hidden(k2_mcart_1('#skF_9'), A_11))), inference(splitRight, [status(thm)], [c_753])).
% 5.05/1.99  tff(c_1290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1278, c_249])).
% 5.05/1.99  tff(c_1292, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 5.05/1.99  tff(c_1354, plain, (![C_251, B_252, A_253]: (r2_hidden(C_251, B_252) | ~r2_hidden(C_251, A_253) | ~r1_tarski(A_253, B_252))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.99  tff(c_1368, plain, (![B_252]: (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), B_252) | ~r1_tarski('#skF_6', B_252))), inference(resolution, [status(thm)], [c_1292, c_1354])).
% 5.05/1.99  tff(c_1388, plain, (![A_259, B_260, C_261, D_262]: (k7_mcart_1(A_259, B_260, C_261, D_262)=k2_mcart_1(D_262) | ~m1_subset_1(D_262, k3_zfmisc_1(A_259, B_260, C_261)) | k1_xboole_0=C_261 | k1_xboole_0=B_260 | k1_xboole_0=A_259)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.05/1.99  tff(c_1392, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_1388])).
% 5.05/1.99  tff(c_1490, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1392])).
% 5.05/1.99  tff(c_1370, plain, (![A_254, B_255, C_256]: (~r1_xboole_0(A_254, B_255) | ~r2_hidden(C_256, B_255) | ~r2_hidden(C_256, A_254))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.05/1.99  tff(c_1373, plain, (![C_256, A_11]: (~r2_hidden(C_256, k1_xboole_0) | ~r2_hidden(C_256, A_11))), inference(resolution, [status(thm)], [c_14, c_1370])).
% 5.05/1.99  tff(c_1518, plain, (![C_287, A_288]: (~r2_hidden(C_287, '#skF_3') | ~r2_hidden(C_287, A_288))), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1373])).
% 5.05/1.99  tff(c_1524, plain, (![A_288]: (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), A_288) | ~r1_tarski('#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_1368, c_1518])).
% 5.05/1.99  tff(c_1537, plain, (![A_288]: (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), A_288))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1524])).
% 5.05/1.99  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1537, c_1292])).
% 5.05/1.99  tff(c_1549, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1392])).
% 5.05/1.99  tff(c_1464, plain, (![A_275, B_276, C_277, D_278]: (k6_mcart_1(A_275, B_276, C_277, D_278)=k2_mcart_1(k1_mcart_1(D_278)) | ~m1_subset_1(D_278, k3_zfmisc_1(A_275, B_276, C_277)) | k1_xboole_0=C_277 | k1_xboole_0=B_276 | k1_xboole_0=A_275)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.05/1.99  tff(c_1468, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_1464])).
% 5.05/1.99  tff(c_1580, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1549, c_1468])).
% 5.05/1.99  tff(c_1581, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1580])).
% 5.05/1.99  tff(c_1590, plain, (![C_256, A_11]: (~r2_hidden(C_256, '#skF_4') | ~r2_hidden(C_256, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1373])).
% 5.05/1.99  tff(c_2002, plain, (![A_11]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_11) | ~r1_tarski('#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_1994, c_1590])).
% 5.05/1.99  tff(c_2018, plain, (![A_11]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2002])).
% 5.05/1.99  tff(c_2026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2018, c_1936])).
% 5.05/1.99  tff(c_2028, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1580])).
% 5.05/1.99  tff(c_1548, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_1392])).
% 5.05/1.99  tff(c_2030, plain, (k1_xboole_0='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_2028, c_1548])).
% 5.05/1.99  tff(c_2031, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_2030])).
% 5.05/1.99  tff(c_1291, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_32])).
% 5.05/1.99  tff(c_1338, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1291])).
% 5.05/1.99  tff(c_2032, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_1338])).
% 5.05/1.99  tff(c_2035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1460, c_2032])).
% 5.05/1.99  tff(c_2036, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2030])).
% 5.05/1.99  tff(c_1469, plain, (![B_279]: (r2_hidden(k2_mcart_1('#skF_9'), B_279) | ~r1_tarski('#skF_8', B_279))), inference(resolution, [status(thm)], [c_1460, c_2])).
% 5.05/1.99  tff(c_1485, plain, (![A_11]: (~r2_hidden(k2_mcart_1('#skF_9'), A_11) | ~r1_tarski('#skF_8', k1_xboole_0))), inference(resolution, [status(thm)], [c_1469, c_1373])).
% 5.05/1.99  tff(c_1489, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1485])).
% 5.05/1.99  tff(c_2042, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2036, c_1489])).
% 5.05/1.99  tff(c_2051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2042])).
% 5.05/1.99  tff(c_2052, plain, (![A_11]: (~r2_hidden(k2_mcart_1('#skF_9'), A_11))), inference(splitRight, [status(thm)], [c_1485])).
% 5.05/1.99  tff(c_2056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2052, c_1460])).
% 5.05/1.99  tff(c_2057, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_1291])).
% 5.05/1.99  tff(c_2224, plain, (![A_370, B_371, C_372, D_373]: (k7_mcart_1(A_370, B_371, C_372, D_373)=k2_mcart_1(D_373) | ~m1_subset_1(D_373, k3_zfmisc_1(A_370, B_371, C_372)) | k1_xboole_0=C_372 | k1_xboole_0=B_371 | k1_xboole_0=A_370)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.05/1.99  tff(c_2228, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_2224])).
% 5.05/1.99  tff(c_2250, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2228])).
% 5.05/1.99  tff(c_2117, plain, (![C_359, B_360, A_361]: (r2_hidden(C_359, B_360) | ~r2_hidden(C_359, A_361) | ~r1_tarski(A_361, B_360))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.99  tff(c_2183, plain, (![B_368]: (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), B_368) | ~r1_tarski('#skF_6', B_368))), inference(resolution, [status(thm)], [c_1292, c_2117])).
% 5.05/1.99  tff(c_2059, plain, (![A_345, B_346, C_347]: (~r1_xboole_0(A_345, B_346) | ~r2_hidden(C_347, B_346) | ~r2_hidden(C_347, A_345))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.05/1.99  tff(c_2062, plain, (![C_347, A_11]: (~r2_hidden(C_347, k1_xboole_0) | ~r2_hidden(C_347, A_11))), inference(resolution, [status(thm)], [c_14, c_2059])).
% 5.05/1.99  tff(c_2201, plain, (![A_11]: (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), A_11) | ~r1_tarski('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_2183, c_2062])).
% 5.05/1.99  tff(c_2223, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2201])).
% 5.05/1.99  tff(c_2251, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_2223])).
% 5.05/1.99  tff(c_2260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_2251])).
% 5.05/1.99  tff(c_2262, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2228])).
% 5.05/1.99  tff(c_2267, plain, (![A_378, B_379, C_380, D_381]: (k6_mcart_1(A_378, B_379, C_380, D_381)=k2_mcart_1(k1_mcart_1(D_381)) | ~m1_subset_1(D_381, k3_zfmisc_1(A_378, B_379, C_380)) | k1_xboole_0=C_380 | k1_xboole_0=B_379 | k1_xboole_0=A_378)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.05/1.99  tff(c_2270, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_2267])).
% 5.05/1.99  tff(c_2273, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2262, c_2270])).
% 5.05/1.99  tff(c_2448, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2273])).
% 5.05/1.99  tff(c_2339, plain, (![A_395, B_396, B_397]: (r2_hidden('#skF_1'(A_395, B_396), B_397) | ~r1_tarski(A_395, B_397) | r1_tarski(A_395, B_396))), inference(resolution, [status(thm)], [c_6, c_2117])).
% 5.05/1.99  tff(c_2428, plain, (![A_408, B_409, A_410]: (~r2_hidden('#skF_1'(A_408, B_409), A_410) | ~r1_tarski(A_408, k1_xboole_0) | r1_tarski(A_408, B_409))), inference(resolution, [status(thm)], [c_2339, c_2062])).
% 5.05/1.99  tff(c_2436, plain, (![A_1, B_2]: (~r1_tarski(A_1, k1_xboole_0) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_2428])).
% 5.05/1.99  tff(c_2520, plain, (![A_418, B_419]: (~r1_tarski(A_418, '#skF_4') | r1_tarski(A_418, B_419))), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2436])).
% 5.05/1.99  tff(c_2533, plain, (![B_419]: (r1_tarski('#skF_7', B_419))), inference(resolution, [status(thm)], [c_56, c_2520])).
% 5.05/1.99  tff(c_2547, plain, (![A_421, A_422, B_423, C_424]: (r2_hidden(k1_mcart_1(A_421), k2_zfmisc_1(A_422, B_423)) | ~r2_hidden(A_421, k3_zfmisc_1(A_422, B_423, C_424)))), inference(superposition, [status(thm), theory('equality')], [c_1321, c_24])).
% 5.05/1.99  tff(c_2589, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_2547])).
% 5.05/1.99  tff(c_2597, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_2589, c_22])).
% 5.05/1.99  tff(c_2600, plain, (![B_2]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), B_2) | ~r1_tarski('#skF_7', B_2))), inference(resolution, [status(thm)], [c_2597, c_2])).
% 5.05/1.99  tff(c_2603, plain, (![B_2]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2600])).
% 5.05/1.99  tff(c_2632, plain, (![B_426]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), B_426))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2600])).
% 5.05/1.99  tff(c_2459, plain, (![C_347, A_11]: (~r2_hidden(C_347, '#skF_4') | ~r2_hidden(C_347, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2062])).
% 5.05/1.99  tff(c_2638, plain, (![A_11]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), A_11))), inference(resolution, [status(thm)], [c_2632, c_2459])).
% 5.05/1.99  tff(c_2654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2603, c_2638])).
% 5.05/1.99  tff(c_2655, plain, (k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_2273])).
% 5.05/1.99  tff(c_2657, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitLeft, [status(thm)], [c_2655])).
% 5.05/1.99  tff(c_2749, plain, (![A_435, A_436, B_437, C_438]: (r2_hidden(k1_mcart_1(A_435), k2_zfmisc_1(A_436, B_437)) | ~r2_hidden(A_435, k3_zfmisc_1(A_436, B_437, C_438)))), inference(superposition, [status(thm), theory('equality')], [c_1321, c_24])).
% 5.05/1.99  tff(c_2791, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_2749])).
% 5.05/1.99  tff(c_2797, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_2791, c_22])).
% 5.05/1.99  tff(c_2803, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_2797])).
% 5.05/1.99  tff(c_2805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2057, c_2803])).
% 5.05/1.99  tff(c_2806, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2655])).
% 5.05/1.99  tff(c_2077, plain, (![A_350, C_351, B_352]: (r2_hidden(k2_mcart_1(A_350), C_351) | ~r2_hidden(A_350, k2_zfmisc_1(B_352, C_351)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.05/1.99  tff(c_2143, plain, (![A_363, C_364, A_365, B_366]: (r2_hidden(k2_mcart_1(A_363), C_364) | ~r2_hidden(A_363, k3_zfmisc_1(A_365, B_366, C_364)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2077])).
% 5.05/1.99  tff(c_2158, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_34, c_2143])).
% 5.05/1.99  tff(c_2162, plain, (![B_367]: (r2_hidden(k2_mcart_1('#skF_9'), B_367) | ~r1_tarski('#skF_8', B_367))), inference(resolution, [status(thm)], [c_2158, c_2])).
% 5.05/1.99  tff(c_2232, plain, (![B_376, B_377]: (r2_hidden(k2_mcart_1('#skF_9'), B_376) | ~r1_tarski(B_377, B_376) | ~r1_tarski('#skF_8', B_377))), inference(resolution, [status(thm)], [c_2162, c_2])).
% 5.05/1.99  tff(c_2242, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_54, c_2232])).
% 5.05/1.99  tff(c_2249, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_2242])).
% 5.05/1.99  tff(c_2275, plain, (![B_382]: (r2_hidden(k2_mcart_1('#skF_9'), B_382) | ~r1_tarski('#skF_5', B_382))), inference(resolution, [status(thm)], [c_2249, c_2])).
% 5.05/1.99  tff(c_2293, plain, (![A_11]: (~r2_hidden(k2_mcart_1('#skF_9'), A_11) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_2275, c_2062])).
% 5.05/1.99  tff(c_2303, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2293])).
% 5.05/1.99  tff(c_2811, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2806, c_2303])).
% 5.05/1.99  tff(c_2823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1306, c_2811])).
% 5.05/1.99  tff(c_2824, plain, (![A_11]: (~r2_hidden(k2_mcart_1('#skF_9'), A_11))), inference(splitRight, [status(thm)], [c_2293])).
% 5.05/1.99  tff(c_2880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2824, c_2249])).
% 5.05/1.99  tff(c_2881, plain, (![A_11]: (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), A_11))), inference(splitRight, [status(thm)], [c_2201])).
% 5.05/1.99  tff(c_2885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2881, c_1292])).
% 5.05/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.99  
% 5.05/1.99  Inference rules
% 5.05/1.99  ----------------------
% 5.05/1.99  #Ref     : 0
% 5.05/1.99  #Sup     : 658
% 5.05/1.99  #Fact    : 0
% 5.05/1.99  #Define  : 0
% 5.05/1.99  #Split   : 45
% 5.05/1.99  #Chain   : 0
% 5.05/1.99  #Close   : 0
% 5.05/1.99  
% 5.05/1.99  Ordering : KBO
% 5.05/1.99  
% 5.05/1.99  Simplification rules
% 5.05/1.99  ----------------------
% 5.05/1.99  #Subsume      : 118
% 5.05/1.99  #Demod        : 279
% 5.05/1.99  #Tautology    : 107
% 5.05/1.99  #SimpNegUnit  : 32
% 5.05/1.99  #BackRed      : 134
% 5.05/1.99  
% 5.05/1.99  #Partial instantiations: 0
% 5.05/1.99  #Strategies tried      : 1
% 5.05/1.99  
% 5.05/1.99  Timing (in seconds)
% 5.05/1.99  ----------------------
% 5.05/1.99  Preprocessing        : 0.34
% 5.05/1.99  Parsing              : 0.18
% 5.05/1.99  CNF conversion       : 0.03
% 5.40/1.99  Main loop            : 0.82
% 5.40/1.99  Inferencing          : 0.30
% 5.40/1.99  Reduction            : 0.25
% 5.40/1.99  Demodulation         : 0.17
% 5.40/1.99  BG Simplification    : 0.03
% 5.40/1.99  Subsumption          : 0.16
% 5.40/1.99  Abstraction          : 0.04
% 5.40/1.99  MUC search           : 0.00
% 5.40/1.99  Cooper               : 0.00
% 5.40/1.99  Total                : 1.24
% 5.40/1.99  Index Insertion      : 0.00
% 5.40/1.99  Index Deletion       : 0.00
% 5.40/1.99  Index Matching       : 0.00
% 5.40/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
