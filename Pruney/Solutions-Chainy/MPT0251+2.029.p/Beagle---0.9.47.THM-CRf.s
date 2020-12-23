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
% DateTime   : Thu Dec  3 09:50:50 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 219 expanded)
%              Number of leaves         :   35 (  88 expanded)
%              Depth                    :   20
%              Number of atoms          :  103 ( 308 expanded)
%              Number of equality atoms :   47 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_84,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_74,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_202,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_210,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(k1_tarski(A_60),B_61) = k1_tarski(A_60)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_202,c_48])).

tff(c_52,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_563,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_570,plain,(
    ! [A_1,B_2,B_94] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_94)
      | ~ r1_tarski(A_1,B_94)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_563])).

tff(c_137,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141,plain,(
    ! [B_16] : k3_xboole_0(B_16,B_16) = B_16 ),
    inference(resolution,[status(thm)],[c_42,c_137])).

tff(c_330,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_339,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k4_xboole_0(B_16,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_330])).

tff(c_1601,plain,(
    ! [A_137,C_138,B_139] :
      ( ~ r2_hidden(A_137,C_138)
      | ~ r2_hidden(A_137,B_139)
      | ~ r2_hidden(A_137,k5_xboole_0(B_139,C_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4106,plain,(
    ! [A_215,B_216] :
      ( ~ r2_hidden(A_215,B_216)
      | ~ r2_hidden(A_215,B_216)
      | ~ r2_hidden(A_215,k4_xboole_0(B_216,B_216)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_1601])).

tff(c_4343,plain,(
    ! [A_219] :
      ( ~ r2_hidden(A_219,k1_xboole_0)
      | ~ r2_hidden(A_219,k1_xboole_0)
      | ~ r2_hidden(A_219,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4106])).

tff(c_4374,plain,(
    ! [B_220] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_220),k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_220) ) ),
    inference(resolution,[status(thm)],[c_6,c_4343])).

tff(c_4378,plain,(
    ! [B_2] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_570,c_4374])).

tff(c_4388,plain,(
    ! [B_221] : r1_tarski(k1_xboole_0,B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4378])).

tff(c_4448,plain,(
    ! [B_224] : k3_xboole_0(k1_xboole_0,B_224) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4388,c_48])).

tff(c_44,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4551,plain,(
    ! [B_227] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_4448,c_44])).

tff(c_4690,plain,(
    ! [B_227] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_4551,c_339])).

tff(c_4733,plain,(
    ! [B_227] : k4_xboole_0(k1_xboole_0,B_227) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4690])).

tff(c_56,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_158,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_215,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(B_66,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_158])).

tff(c_70,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_242,plain,(
    ! [B_67,A_68] : k2_xboole_0(B_67,A_68) = k2_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_70])).

tff(c_46,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_258,plain,(
    ! [A_68] : k2_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_46])).

tff(c_383,plain,(
    ! [A_82,B_83] : k4_xboole_0(k2_xboole_0(A_82,B_83),B_83) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_396,plain,(
    ! [A_68] : k4_xboole_0(k1_xboole_0,A_68) = k4_xboole_0(A_68,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_383])).

tff(c_4807,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4733,c_396])).

tff(c_5071,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4807,c_339])).

tff(c_365,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5243,plain,(
    ! [A_240,B_241,B_242] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_240,B_241),B_242),B_241)
      | r1_tarski(k3_xboole_0(A_240,B_241),B_242) ) ),
    inference(resolution,[status(thm)],[c_365,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5300,plain,(
    ! [A_243,B_244] : r1_tarski(k3_xboole_0(A_243,B_244),B_244) ),
    inference(resolution,[status(thm)],[c_5243,c_4])).

tff(c_5883,plain,(
    ! [A_258,B_259] : k3_xboole_0(k3_xboole_0(A_258,B_259),B_259) = k3_xboole_0(A_258,B_259) ),
    inference(resolution,[status(thm)],[c_5300,c_48])).

tff(c_5936,plain,(
    ! [A_258,B_259] : k5_xboole_0(k3_xboole_0(A_258,B_259),k3_xboole_0(A_258,B_259)) = k4_xboole_0(k3_xboole_0(A_258,B_259),B_259) ),
    inference(superposition,[status(thm),theory(equality)],[c_5883,c_44])).

tff(c_5980,plain,(
    ! [A_258,B_259] : k4_xboole_0(k3_xboole_0(A_258,B_259),B_259) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5071,c_5936])).

tff(c_6074,plain,(
    ! [A_263,B_264] : k4_xboole_0(k3_xboole_0(A_263,B_264),B_264) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5071,c_5936])).

tff(c_435,plain,(
    ! [A_85,B_86] : k2_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_441,plain,(
    ! [A_85,B_86] : k4_xboole_0(k2_xboole_0(A_85,B_86),k4_xboole_0(B_86,A_85)) = k4_xboole_0(A_85,k4_xboole_0(B_86,A_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_54])).

tff(c_6091,plain,(
    ! [B_264,A_263] : k4_xboole_0(k2_xboole_0(B_264,k3_xboole_0(A_263,B_264)),k1_xboole_0) = k4_xboole_0(B_264,k4_xboole_0(k3_xboole_0(A_263,B_264),B_264)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6074,c_441])).

tff(c_6169,plain,(
    ! [B_265,A_266] : k2_xboole_0(B_265,k3_xboole_0(A_266,B_265)) = B_265 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5980,c_52,c_6091])).

tff(c_6373,plain,(
    ! [B_269,A_270] :
      ( k2_xboole_0(B_269,k1_tarski(A_270)) = B_269
      | ~ r2_hidden(A_270,B_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_6169])).

tff(c_221,plain,(
    ! [B_66,A_65] : k2_xboole_0(B_66,A_65) = k2_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_70])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_241,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_72])).

tff(c_6440,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6373,c_241])).

tff(c_6492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.31  
% 6.27/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.31  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.60/2.31  
% 6.60/2.31  %Foreground sorts:
% 6.60/2.31  
% 6.60/2.31  
% 6.60/2.31  %Background operators:
% 6.60/2.31  
% 6.60/2.31  
% 6.60/2.31  %Foreground operators:
% 6.60/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.60/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.60/2.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.60/2.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.60/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.60/2.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.60/2.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.60/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.60/2.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.60/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.60/2.31  tff('#skF_5', type, '#skF_5': $i).
% 6.60/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.60/2.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.60/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.60/2.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.60/2.31  tff('#skF_4', type, '#skF_4': $i).
% 6.60/2.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.60/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.60/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.60/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.60/2.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.60/2.31  
% 6.60/2.33  tff(f_89, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 6.60/2.33  tff(f_82, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.60/2.33  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.60/2.33  tff(f_66, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.60/2.33  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.60/2.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.60/2.33  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.60/2.33  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.60/2.33  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.60/2.33  tff(f_84, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.60/2.33  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.60/2.33  tff(f_68, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.60/2.33  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.60/2.33  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.60/2.33  tff(c_74, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.60/2.33  tff(c_202, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.60/2.33  tff(c_48, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.60/2.33  tff(c_210, plain, (![A_60, B_61]: (k3_xboole_0(k1_tarski(A_60), B_61)=k1_tarski(A_60) | ~r2_hidden(A_60, B_61))), inference(resolution, [status(thm)], [c_202, c_48])).
% 6.60/2.33  tff(c_52, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.60/2.33  tff(c_42, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.60/2.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.60/2.33  tff(c_563, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.60/2.33  tff(c_570, plain, (![A_1, B_2, B_94]: (r2_hidden('#skF_1'(A_1, B_2), B_94) | ~r1_tarski(A_1, B_94) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_563])).
% 6.60/2.33  tff(c_137, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.60/2.33  tff(c_141, plain, (![B_16]: (k3_xboole_0(B_16, B_16)=B_16)), inference(resolution, [status(thm)], [c_42, c_137])).
% 6.60/2.33  tff(c_330, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.60/2.33  tff(c_339, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k4_xboole_0(B_16, B_16))), inference(superposition, [status(thm), theory('equality')], [c_141, c_330])).
% 6.60/2.33  tff(c_1601, plain, (![A_137, C_138, B_139]: (~r2_hidden(A_137, C_138) | ~r2_hidden(A_137, B_139) | ~r2_hidden(A_137, k5_xboole_0(B_139, C_138)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.60/2.33  tff(c_4106, plain, (![A_215, B_216]: (~r2_hidden(A_215, B_216) | ~r2_hidden(A_215, B_216) | ~r2_hidden(A_215, k4_xboole_0(B_216, B_216)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_1601])).
% 6.60/2.33  tff(c_4343, plain, (![A_219]: (~r2_hidden(A_219, k1_xboole_0) | ~r2_hidden(A_219, k1_xboole_0) | ~r2_hidden(A_219, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4106])).
% 6.60/2.33  tff(c_4374, plain, (![B_220]: (~r2_hidden('#skF_1'(k1_xboole_0, B_220), k1_xboole_0) | r1_tarski(k1_xboole_0, B_220))), inference(resolution, [status(thm)], [c_6, c_4343])).
% 6.60/2.33  tff(c_4378, plain, (![B_2]: (~r1_tarski(k1_xboole_0, k1_xboole_0) | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_570, c_4374])).
% 6.60/2.33  tff(c_4388, plain, (![B_221]: (r1_tarski(k1_xboole_0, B_221))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4378])).
% 6.60/2.33  tff(c_4448, plain, (![B_224]: (k3_xboole_0(k1_xboole_0, B_224)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4388, c_48])).
% 6.60/2.33  tff(c_44, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.60/2.33  tff(c_4551, plain, (![B_227]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_227))), inference(superposition, [status(thm), theory('equality')], [c_4448, c_44])).
% 6.60/2.33  tff(c_4690, plain, (![B_227]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_227))), inference(superposition, [status(thm), theory('equality')], [c_4551, c_339])).
% 6.60/2.33  tff(c_4733, plain, (![B_227]: (k4_xboole_0(k1_xboole_0, B_227)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4690])).
% 6.60/2.33  tff(c_56, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.60/2.33  tff(c_158, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.60/2.33  tff(c_215, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(B_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_56, c_158])).
% 6.60/2.33  tff(c_70, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.60/2.33  tff(c_242, plain, (![B_67, A_68]: (k2_xboole_0(B_67, A_68)=k2_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_215, c_70])).
% 6.60/2.33  tff(c_46, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.60/2.33  tff(c_258, plain, (![A_68]: (k2_xboole_0(k1_xboole_0, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_242, c_46])).
% 6.60/2.33  tff(c_383, plain, (![A_82, B_83]: (k4_xboole_0(k2_xboole_0(A_82, B_83), B_83)=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.33  tff(c_396, plain, (![A_68]: (k4_xboole_0(k1_xboole_0, A_68)=k4_xboole_0(A_68, A_68))), inference(superposition, [status(thm), theory('equality')], [c_258, c_383])).
% 6.60/2.33  tff(c_4807, plain, (![A_68]: (k4_xboole_0(A_68, A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4733, c_396])).
% 6.60/2.33  tff(c_5071, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4807, c_339])).
% 6.60/2.33  tff(c_365, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.60/2.33  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.60/2.33  tff(c_5243, plain, (![A_240, B_241, B_242]: (r2_hidden('#skF_1'(k3_xboole_0(A_240, B_241), B_242), B_241) | r1_tarski(k3_xboole_0(A_240, B_241), B_242))), inference(resolution, [status(thm)], [c_365, c_10])).
% 6.60/2.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.60/2.33  tff(c_5300, plain, (![A_243, B_244]: (r1_tarski(k3_xboole_0(A_243, B_244), B_244))), inference(resolution, [status(thm)], [c_5243, c_4])).
% 6.60/2.33  tff(c_5883, plain, (![A_258, B_259]: (k3_xboole_0(k3_xboole_0(A_258, B_259), B_259)=k3_xboole_0(A_258, B_259))), inference(resolution, [status(thm)], [c_5300, c_48])).
% 6.60/2.33  tff(c_5936, plain, (![A_258, B_259]: (k5_xboole_0(k3_xboole_0(A_258, B_259), k3_xboole_0(A_258, B_259))=k4_xboole_0(k3_xboole_0(A_258, B_259), B_259))), inference(superposition, [status(thm), theory('equality')], [c_5883, c_44])).
% 6.60/2.33  tff(c_5980, plain, (![A_258, B_259]: (k4_xboole_0(k3_xboole_0(A_258, B_259), B_259)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5071, c_5936])).
% 6.60/2.33  tff(c_6074, plain, (![A_263, B_264]: (k4_xboole_0(k3_xboole_0(A_263, B_264), B_264)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5071, c_5936])).
% 6.60/2.33  tff(c_435, plain, (![A_85, B_86]: (k2_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.60/2.33  tff(c_54, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.33  tff(c_441, plain, (![A_85, B_86]: (k4_xboole_0(k2_xboole_0(A_85, B_86), k4_xboole_0(B_86, A_85))=k4_xboole_0(A_85, k4_xboole_0(B_86, A_85)))), inference(superposition, [status(thm), theory('equality')], [c_435, c_54])).
% 6.60/2.33  tff(c_6091, plain, (![B_264, A_263]: (k4_xboole_0(k2_xboole_0(B_264, k3_xboole_0(A_263, B_264)), k1_xboole_0)=k4_xboole_0(B_264, k4_xboole_0(k3_xboole_0(A_263, B_264), B_264)))), inference(superposition, [status(thm), theory('equality')], [c_6074, c_441])).
% 6.60/2.33  tff(c_6169, plain, (![B_265, A_266]: (k2_xboole_0(B_265, k3_xboole_0(A_266, B_265))=B_265)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5980, c_52, c_6091])).
% 6.60/2.33  tff(c_6373, plain, (![B_269, A_270]: (k2_xboole_0(B_269, k1_tarski(A_270))=B_269 | ~r2_hidden(A_270, B_269))), inference(superposition, [status(thm), theory('equality')], [c_210, c_6169])).
% 6.60/2.33  tff(c_221, plain, (![B_66, A_65]: (k2_xboole_0(B_66, A_65)=k2_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_215, c_70])).
% 6.60/2.33  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.60/2.33  tff(c_241, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_72])).
% 6.60/2.33  tff(c_6440, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6373, c_241])).
% 6.60/2.33  tff(c_6492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_6440])).
% 6.60/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.33  
% 6.60/2.33  Inference rules
% 6.60/2.33  ----------------------
% 6.60/2.33  #Ref     : 0
% 6.60/2.33  #Sup     : 1545
% 6.60/2.33  #Fact    : 0
% 6.60/2.33  #Define  : 0
% 6.60/2.33  #Split   : 3
% 6.60/2.33  #Chain   : 0
% 6.60/2.33  #Close   : 0
% 6.60/2.33  
% 6.60/2.33  Ordering : KBO
% 6.60/2.33  
% 6.60/2.33  Simplification rules
% 6.60/2.33  ----------------------
% 6.60/2.33  #Subsume      : 223
% 6.60/2.33  #Demod        : 2053
% 6.60/2.33  #Tautology    : 934
% 6.60/2.33  #SimpNegUnit  : 0
% 6.60/2.33  #BackRed      : 25
% 6.60/2.33  
% 6.60/2.33  #Partial instantiations: 0
% 6.60/2.33  #Strategies tried      : 1
% 6.60/2.33  
% 6.60/2.33  Timing (in seconds)
% 6.60/2.33  ----------------------
% 6.60/2.33  Preprocessing        : 0.36
% 6.60/2.33  Parsing              : 0.18
% 6.60/2.33  CNF conversion       : 0.03
% 6.60/2.33  Main loop            : 1.21
% 6.60/2.33  Inferencing          : 0.36
% 6.60/2.34  Reduction            : 0.57
% 6.60/2.34  Demodulation         : 0.48
% 6.60/2.34  BG Simplification    : 0.04
% 6.60/2.34  Subsumption          : 0.18
% 6.60/2.34  Abstraction          : 0.07
% 6.60/2.34  MUC search           : 0.00
% 6.60/2.34  Cooper               : 0.00
% 6.60/2.34  Total                : 1.61
% 6.60/2.34  Index Insertion      : 0.00
% 6.60/2.34  Index Deletion       : 0.00
% 6.60/2.34  Index Matching       : 0.00
% 6.60/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
