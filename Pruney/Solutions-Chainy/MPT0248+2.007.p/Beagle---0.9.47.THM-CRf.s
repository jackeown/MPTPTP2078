%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:05 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 176 expanded)
%              Number of leaves         :   31 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 425 expanded)
%              Number of equality atoms :   99 ( 377 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_88,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_48,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_68,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_68])).

tff(c_28,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1162,plain,(
    ! [B_117,C_118,A_119] :
      ( k2_tarski(B_117,C_118) = A_119
      | k1_tarski(C_118) = A_119
      | k1_tarski(B_117) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k2_tarski(B_117,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1190,plain,(
    ! [A_19,A_119] :
      ( k2_tarski(A_19,A_19) = A_119
      | k1_tarski(A_19) = A_119
      | k1_tarski(A_19) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_tarski(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1162])).

tff(c_3576,plain,(
    ! [A_177,A_178] :
      ( k1_tarski(A_177) = A_178
      | k1_tarski(A_177) = A_178
      | k1_tarski(A_177) = A_178
      | k1_xboole_0 = A_178
      | ~ r1_tarski(A_178,k1_tarski(A_177)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1190])).

tff(c_3592,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_71,c_3576])).

tff(c_3604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_66,c_66,c_66,c_3592])).

tff(c_3605,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3606,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3607,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_2') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_16])).

tff(c_3627,plain,(
    ! [A_184] : k2_tarski(A_184,A_184) = k1_tarski(A_184) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [B_26,C_27] : r1_tarski(k1_xboole_0,k2_tarski(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3621,plain,(
    ! [B_26,C_27] : r1_tarski('#skF_2',k2_tarski(B_26,C_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_42])).

tff(c_3632,plain,(
    ! [A_184] : r1_tarski('#skF_2',k1_tarski(A_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3627,c_3621])).

tff(c_3794,plain,(
    ! [A_204,B_205] :
      ( k3_xboole_0(A_204,B_205) = A_204
      | ~ r1_tarski(A_204,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3824,plain,(
    ! [A_184] : k3_xboole_0('#skF_2',k1_tarski(A_184)) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3632,c_3794])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3964,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_4])).

tff(c_4011,plain,(
    ! [A_225,C_226,B_227] :
      ( r1_xboole_0(A_225,C_226)
      | ~ r1_xboole_0(A_225,k2_xboole_0(B_227,C_226)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4082,plain,(
    ! [A_232] :
      ( r1_xboole_0(A_232,'#skF_3')
      | ~ r1_xboole_0(A_232,k1_tarski('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4011])).

tff(c_4132,plain,(
    ! [A_236] :
      ( r1_xboole_0(A_236,'#skF_3')
      | k3_xboole_0(A_236,k1_tarski('#skF_1')) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_3964,c_4082])).

tff(c_4137,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3824,c_4132])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3705,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_2'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_2])).

tff(c_4141,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4137,c_3705])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4145,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4141,c_10])).

tff(c_4148,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3607,c_4145])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3771,plain,(
    ! [A_200,B_201] :
      ( r1_tarski(A_200,B_201)
      | k4_xboole_0(A_200,B_201) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_6])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5335,plain,(
    ! [A_289,B_290] :
      ( k2_xboole_0(A_289,B_290) = B_290
      | k4_xboole_0(A_289,B_290) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_3771,c_12])).

tff(c_5375,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4148,c_5335])).

tff(c_5507,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_52])).

tff(c_5509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3605,c_5507])).

tff(c_5510,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5511,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5542,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5511,c_5511,c_50])).

tff(c_26,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5655,plain,(
    ! [A_310,B_311] : k3_tarski(k2_tarski(A_310,B_311)) = k2_xboole_0(A_310,B_311) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6453,plain,(
    ! [A_360,B_361] : k3_tarski(k2_tarski(A_360,B_361)) = k2_xboole_0(B_361,A_360) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5655])).

tff(c_44,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6506,plain,(
    ! [B_365,A_366] : k2_xboole_0(B_365,A_366) = k2_xboole_0(A_366,B_365) ),
    inference(superposition,[status(thm),theory(equality)],[c_6453,c_44])).

tff(c_5513,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5511,c_52])).

tff(c_6557,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6506,c_5513])).

tff(c_24,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6608,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6557,c_24])).

tff(c_6929,plain,(
    ! [B_381,C_382,A_383] :
      ( k2_tarski(B_381,C_382) = A_383
      | k1_tarski(C_382) = A_383
      | k1_tarski(B_381) = A_383
      | k1_xboole_0 = A_383
      | ~ r1_tarski(A_383,k2_tarski(B_381,C_382)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6960,plain,(
    ! [A_19,A_383] :
      ( k2_tarski(A_19,A_19) = A_383
      | k1_tarski(A_19) = A_383
      | k1_tarski(A_19) = A_383
      | k1_xboole_0 = A_383
      | ~ r1_tarski(A_383,k1_tarski(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6929])).

tff(c_10946,plain,(
    ! [A_480,A_481] :
      ( k1_tarski(A_480) = A_481
      | k1_tarski(A_480) = A_481
      | k1_tarski(A_480) = A_481
      | k1_xboole_0 = A_481
      | ~ r1_tarski(A_481,k1_tarski(A_480)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6960])).

tff(c_10959,plain,(
    ! [A_481] :
      ( k1_tarski('#skF_1') = A_481
      | k1_tarski('#skF_1') = A_481
      | k1_tarski('#skF_1') = A_481
      | k1_xboole_0 = A_481
      | ~ r1_tarski(A_481,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5511,c_10946])).

tff(c_11115,plain,(
    ! [A_484] :
      ( A_484 = '#skF_2'
      | A_484 = '#skF_2'
      | A_484 = '#skF_2'
      | k1_xboole_0 = A_484
      | ~ r1_tarski(A_484,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5511,c_5511,c_5511,c_10959])).

tff(c_11118,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6608,c_11115])).

tff(c_11132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5510,c_5542,c_5542,c_5542,c_11118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.56  
% 7.21/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.56  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.21/2.56  
% 7.21/2.56  %Foreground sorts:
% 7.21/2.56  
% 7.21/2.56  
% 7.21/2.56  %Background operators:
% 7.21/2.56  
% 7.21/2.56  
% 7.21/2.56  %Foreground operators:
% 7.21/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.21/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.21/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.21/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.21/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.21/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.21/2.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.21/2.56  tff('#skF_2', type, '#skF_2': $i).
% 7.21/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.56  tff('#skF_1', type, '#skF_1': $i).
% 7.21/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.21/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.21/2.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.21/2.56  
% 7.21/2.57  tff(f_107, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 7.21/2.57  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.21/2.57  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.21/2.57  tff(f_86, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 7.21/2.57  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.21/2.57  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.21/2.57  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.21/2.57  tff(f_61, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.21/2.57  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.21/2.57  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.21/2.57  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.21/2.57  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.21/2.57  tff(f_88, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.21/2.57  tff(c_48, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.21/2.57  tff(c_67, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 7.21/2.57  tff(c_46, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.21/2.57  tff(c_66, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_46])).
% 7.21/2.57  tff(c_52, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.21/2.57  tff(c_68, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.21/2.57  tff(c_71, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_68])).
% 7.21/2.57  tff(c_28, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.21/2.57  tff(c_1162, plain, (![B_117, C_118, A_119]: (k2_tarski(B_117, C_118)=A_119 | k1_tarski(C_118)=A_119 | k1_tarski(B_117)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k2_tarski(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.21/2.57  tff(c_1190, plain, (![A_19, A_119]: (k2_tarski(A_19, A_19)=A_119 | k1_tarski(A_19)=A_119 | k1_tarski(A_19)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1162])).
% 7.21/2.57  tff(c_3576, plain, (![A_177, A_178]: (k1_tarski(A_177)=A_178 | k1_tarski(A_177)=A_178 | k1_tarski(A_177)=A_178 | k1_xboole_0=A_178 | ~r1_tarski(A_178, k1_tarski(A_177)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1190])).
% 7.21/2.57  tff(c_3592, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_71, c_3576])).
% 7.21/2.57  tff(c_3604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_66, c_66, c_66, c_3592])).
% 7.21/2.57  tff(c_3605, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 7.21/2.57  tff(c_3606, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 7.21/2.57  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.21/2.57  tff(c_3607, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_2')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_3606, c_16])).
% 7.21/2.57  tff(c_3627, plain, (![A_184]: (k2_tarski(A_184, A_184)=k1_tarski(A_184))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.21/2.57  tff(c_42, plain, (![B_26, C_27]: (r1_tarski(k1_xboole_0, k2_tarski(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.21/2.57  tff(c_3621, plain, (![B_26, C_27]: (r1_tarski('#skF_2', k2_tarski(B_26, C_27)))), inference(demodulation, [status(thm), theory('equality')], [c_3606, c_42])).
% 7.21/2.57  tff(c_3632, plain, (![A_184]: (r1_tarski('#skF_2', k1_tarski(A_184)))), inference(superposition, [status(thm), theory('equality')], [c_3627, c_3621])).
% 7.21/2.57  tff(c_3794, plain, (![A_204, B_205]: (k3_xboole_0(A_204, B_205)=A_204 | ~r1_tarski(A_204, B_205))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.21/2.57  tff(c_3824, plain, (![A_184]: (k3_xboole_0('#skF_2', k1_tarski(A_184))='#skF_2')), inference(resolution, [status(thm)], [c_3632, c_3794])).
% 7.21/2.57  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.21/2.57  tff(c_3964, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3606, c_4])).
% 7.21/2.57  tff(c_4011, plain, (![A_225, C_226, B_227]: (r1_xboole_0(A_225, C_226) | ~r1_xboole_0(A_225, k2_xboole_0(B_227, C_226)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.21/2.57  tff(c_4082, plain, (![A_232]: (r1_xboole_0(A_232, '#skF_3') | ~r1_xboole_0(A_232, k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4011])).
% 7.21/2.57  tff(c_4132, plain, (![A_236]: (r1_xboole_0(A_236, '#skF_3') | k3_xboole_0(A_236, k1_tarski('#skF_1'))!='#skF_2')), inference(resolution, [status(thm)], [c_3964, c_4082])).
% 7.21/2.57  tff(c_4137, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3824, c_4132])).
% 7.21/2.57  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.21/2.57  tff(c_3705, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_2' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3606, c_2])).
% 7.21/2.57  tff(c_4141, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_4137, c_3705])).
% 7.21/2.57  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.21/2.57  tff(c_4145, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4141, c_10])).
% 7.21/2.57  tff(c_4148, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3607, c_4145])).
% 7.21/2.57  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.21/2.57  tff(c_3771, plain, (![A_200, B_201]: (r1_tarski(A_200, B_201) | k4_xboole_0(A_200, B_201)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3606, c_6])).
% 7.21/2.57  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.21/2.57  tff(c_5335, plain, (![A_289, B_290]: (k2_xboole_0(A_289, B_290)=B_290 | k4_xboole_0(A_289, B_290)!='#skF_2')), inference(resolution, [status(thm)], [c_3771, c_12])).
% 7.21/2.57  tff(c_5375, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4148, c_5335])).
% 7.21/2.57  tff(c_5507, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_52])).
% 7.21/2.57  tff(c_5509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3605, c_5507])).
% 7.21/2.57  tff(c_5510, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 7.21/2.57  tff(c_5511, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 7.21/2.57  tff(c_50, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.21/2.57  tff(c_5542, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5511, c_5511, c_50])).
% 7.21/2.57  tff(c_26, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.21/2.57  tff(c_5655, plain, (![A_310, B_311]: (k3_tarski(k2_tarski(A_310, B_311))=k2_xboole_0(A_310, B_311))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.21/2.57  tff(c_6453, plain, (![A_360, B_361]: (k3_tarski(k2_tarski(A_360, B_361))=k2_xboole_0(B_361, A_360))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5655])).
% 7.21/2.57  tff(c_44, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.21/2.57  tff(c_6506, plain, (![B_365, A_366]: (k2_xboole_0(B_365, A_366)=k2_xboole_0(A_366, B_365))), inference(superposition, [status(thm), theory('equality')], [c_6453, c_44])).
% 7.21/2.57  tff(c_5513, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5511, c_52])).
% 7.21/2.57  tff(c_6557, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6506, c_5513])).
% 7.21/2.57  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.21/2.57  tff(c_6608, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6557, c_24])).
% 7.21/2.57  tff(c_6929, plain, (![B_381, C_382, A_383]: (k2_tarski(B_381, C_382)=A_383 | k1_tarski(C_382)=A_383 | k1_tarski(B_381)=A_383 | k1_xboole_0=A_383 | ~r1_tarski(A_383, k2_tarski(B_381, C_382)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.21/2.57  tff(c_6960, plain, (![A_19, A_383]: (k2_tarski(A_19, A_19)=A_383 | k1_tarski(A_19)=A_383 | k1_tarski(A_19)=A_383 | k1_xboole_0=A_383 | ~r1_tarski(A_383, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6929])).
% 7.21/2.57  tff(c_10946, plain, (![A_480, A_481]: (k1_tarski(A_480)=A_481 | k1_tarski(A_480)=A_481 | k1_tarski(A_480)=A_481 | k1_xboole_0=A_481 | ~r1_tarski(A_481, k1_tarski(A_480)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6960])).
% 7.21/2.57  tff(c_10959, plain, (![A_481]: (k1_tarski('#skF_1')=A_481 | k1_tarski('#skF_1')=A_481 | k1_tarski('#skF_1')=A_481 | k1_xboole_0=A_481 | ~r1_tarski(A_481, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5511, c_10946])).
% 7.21/2.57  tff(c_11115, plain, (![A_484]: (A_484='#skF_2' | A_484='#skF_2' | A_484='#skF_2' | k1_xboole_0=A_484 | ~r1_tarski(A_484, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5511, c_5511, c_5511, c_10959])).
% 7.21/2.57  tff(c_11118, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6608, c_11115])).
% 7.21/2.57  tff(c_11132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5510, c_5542, c_5542, c_5542, c_11118])).
% 7.21/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.57  
% 7.21/2.57  Inference rules
% 7.21/2.57  ----------------------
% 7.21/2.57  #Ref     : 0
% 7.21/2.57  #Sup     : 2858
% 7.21/2.57  #Fact    : 0
% 7.21/2.57  #Define  : 0
% 7.21/2.57  #Split   : 13
% 7.21/2.57  #Chain   : 0
% 7.21/2.57  #Close   : 0
% 7.21/2.57  
% 7.21/2.57  Ordering : KBO
% 7.21/2.57  
% 7.21/2.57  Simplification rules
% 7.21/2.57  ----------------------
% 7.21/2.57  #Subsume      : 314
% 7.21/2.57  #Demod        : 1905
% 7.21/2.57  #Tautology    : 1935
% 7.21/2.57  #SimpNegUnit  : 66
% 7.21/2.57  #BackRed      : 4
% 7.21/2.57  
% 7.21/2.57  #Partial instantiations: 0
% 7.21/2.57  #Strategies tried      : 1
% 7.21/2.57  
% 7.21/2.57  Timing (in seconds)
% 7.21/2.57  ----------------------
% 7.21/2.58  Preprocessing        : 0.35
% 7.21/2.58  Parsing              : 0.19
% 7.21/2.58  CNF conversion       : 0.02
% 7.21/2.58  Main loop            : 1.43
% 7.21/2.58  Inferencing          : 0.43
% 7.21/2.58  Reduction            : 0.62
% 7.21/2.58  Demodulation         : 0.50
% 7.21/2.58  BG Simplification    : 0.04
% 7.21/2.58  Subsumption          : 0.22
% 7.21/2.58  Abstraction          : 0.05
% 7.21/2.58  MUC search           : 0.00
% 7.21/2.58  Cooper               : 0.00
% 7.21/2.58  Total                : 1.82
% 7.21/2.58  Index Insertion      : 0.00
% 7.21/2.58  Index Deletion       : 0.00
% 7.21/2.58  Index Matching       : 0.00
% 7.21/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
