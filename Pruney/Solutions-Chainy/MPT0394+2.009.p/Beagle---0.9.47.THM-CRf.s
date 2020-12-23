%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:22 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 138 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 166 expanded)
%              Number of equality atoms :   60 ( 105 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_98,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_70,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,(
    ! [A_47] : k3_xboole_0(k1_xboole_0,A_47) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_218,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_245,plain,(
    ! [A_67] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_218])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_259,plain,(
    ! [B_17] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_18])).

tff(c_275,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_259])).

tff(c_230,plain,(
    ! [A_47] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_218])).

tff(c_278,plain,(
    ! [A_47] : k4_xboole_0(k1_xboole_0,A_47) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_230])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_321,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,k3_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_341,plain,(
    ! [A_13,C_71] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_71,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_321])).

tff(c_345,plain,(
    ! [C_72] : ~ r2_hidden(C_72,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_369,plain,(
    ! [A_77] : r1_xboole_0(A_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_345])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_377,plain,(
    ! [A_78] : k4_xboole_0(A_78,k1_xboole_0) = A_78 ),
    inference(resolution,[status(thm)],[c_369,c_20])).

tff(c_387,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k3_xboole_0(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_18])).

tff(c_397,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_387])).

tff(c_117,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(A_48,B_49)
      | k4_xboole_0(A_48,B_49) != A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    ! [B_38] : ~ r1_xboole_0(k1_tarski(B_38),k1_tarski(B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_121,plain,(
    ! [B_38] : k4_xboole_0(k1_tarski(B_38),k1_tarski(B_38)) != k1_tarski(B_38) ),
    inference(resolution,[status(thm)],[c_117,c_36])).

tff(c_400,plain,(
    ! [B_38] : k1_tarski(B_38) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_121])).

tff(c_40,plain,(
    ! [A_41] : k1_setfam_1(k1_tarski(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_569,plain,(
    ! [A_95,B_96,C_97,D_98] : k2_xboole_0(k1_enumset1(A_95,B_96,C_97),k1_tarski(D_98)) = k2_enumset1(A_95,B_96,C_97,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_578,plain,(
    ! [A_30,B_31,D_98] : k2_xboole_0(k2_tarski(A_30,B_31),k1_tarski(D_98)) = k2_enumset1(A_30,A_30,B_31,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_569])).

tff(c_2649,plain,(
    ! [A_181,B_182,D_183] : k2_xboole_0(k2_tarski(A_181,B_182),k1_tarski(D_183)) = k1_enumset1(A_181,B_182,D_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_578])).

tff(c_2658,plain,(
    ! [A_29,D_183] : k2_xboole_0(k1_tarski(A_29),k1_tarski(D_183)) = k1_enumset1(A_29,A_29,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2649])).

tff(c_2661,plain,(
    ! [A_29,D_183] : k2_xboole_0(k1_tarski(A_29),k1_tarski(D_183)) = k2_tarski(A_29,D_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2658])).

tff(c_720,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0(k1_setfam_1(A_105),k1_setfam_1(B_106)) = k1_setfam_1(k2_xboole_0(A_105,B_106))
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_767,plain,(
    ! [A_105,A_41] :
      ( k1_setfam_1(k2_xboole_0(A_105,k1_tarski(A_41))) = k3_xboole_0(k1_setfam_1(A_105),A_41)
      | k1_tarski(A_41) = k1_xboole_0
      | k1_xboole_0 = A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_720])).

tff(c_4353,plain,(
    ! [A_213,A_214] :
      ( k1_setfam_1(k2_xboole_0(A_213,k1_tarski(A_214))) = k3_xboole_0(k1_setfam_1(A_213),A_214)
      | k1_xboole_0 = A_213 ) ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_767])).

tff(c_4368,plain,(
    ! [A_29,D_183] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_29)),D_183) = k1_setfam_1(k2_tarski(A_29,D_183))
      | k1_tarski(A_29) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_4353])).

tff(c_4384,plain,(
    ! [A_29,D_183] :
      ( k1_setfam_1(k2_tarski(A_29,D_183)) = k3_xboole_0(A_29,D_183)
      | k1_tarski(A_29) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4368])).

tff(c_4385,plain,(
    ! [A_29,D_183] : k1_setfam_1(k2_tarski(A_29,D_183)) = k3_xboole_0(A_29,D_183) ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_4384])).

tff(c_42,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_43,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_4388,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4385,c_43])).

tff(c_4391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4388])).

tff(c_4393,plain,(
    ! [A_215] : ~ r1_xboole_0(A_215,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_4399,plain,(
    ! [A_216] : k4_xboole_0(A_216,k1_xboole_0) != A_216 ),
    inference(resolution,[status(thm)],[c_22,c_4393])).

tff(c_4405,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_4399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/2.04  
% 4.94/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/2.04  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.94/2.04  
% 4.94/2.04  %Foreground sorts:
% 4.94/2.04  
% 4.94/2.04  
% 4.94/2.04  %Background operators:
% 4.94/2.04  
% 4.94/2.04  
% 4.94/2.04  %Foreground operators:
% 4.94/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.94/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.94/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.94/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/2.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.94/2.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.94/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.94/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.94/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.94/2.04  tff('#skF_3', type, '#skF_3': $i).
% 4.94/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/2.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.94/2.04  tff('#skF_4', type, '#skF_4': $i).
% 4.94/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.94/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.94/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.94/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.94/2.04  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.94/2.04  
% 4.94/2.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.94/2.06  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.94/2.06  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.94/2.06  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.94/2.06  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.94/2.06  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.94/2.06  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.94/2.06  tff(f_86, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 4.94/2.06  tff(f_98, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.94/2.06  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.94/2.06  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.94/2.06  tff(f_79, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.94/2.06  tff(f_71, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.94/2.06  tff(f_96, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 4.94/2.06  tff(f_101, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.94/2.06  tff(c_70, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.94/2.06  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.94/2.06  tff(c_86, plain, (![A_47]: (k3_xboole_0(k1_xboole_0, A_47)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_14])).
% 4.94/2.06  tff(c_218, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.94/2.06  tff(c_245, plain, (![A_67]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_67))), inference(superposition, [status(thm), theory('equality')], [c_86, c_218])).
% 4.94/2.06  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.94/2.06  tff(c_259, plain, (![B_17]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_17))), inference(superposition, [status(thm), theory('equality')], [c_245, c_18])).
% 4.94/2.06  tff(c_275, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_259])).
% 4.94/2.06  tff(c_230, plain, (![A_47]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_47))), inference(superposition, [status(thm), theory('equality')], [c_86, c_218])).
% 4.94/2.06  tff(c_278, plain, (![A_47]: (k4_xboole_0(k1_xboole_0, A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_230])).
% 4.94/2.06  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/2.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.94/2.06  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.94/2.06  tff(c_321, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.94/2.06  tff(c_341, plain, (![A_13, C_71]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_321])).
% 4.94/2.06  tff(c_345, plain, (![C_72]: (~r2_hidden(C_72, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_341])).
% 4.94/2.06  tff(c_369, plain, (![A_77]: (r1_xboole_0(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_345])).
% 4.94/2.06  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/2.06  tff(c_377, plain, (![A_78]: (k4_xboole_0(A_78, k1_xboole_0)=A_78)), inference(resolution, [status(thm)], [c_369, c_20])).
% 4.94/2.06  tff(c_387, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k3_xboole_0(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_377, c_18])).
% 4.94/2.06  tff(c_397, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_387])).
% 4.94/2.06  tff(c_117, plain, (![A_48, B_49]: (r1_xboole_0(A_48, B_49) | k4_xboole_0(A_48, B_49)!=A_48)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/2.06  tff(c_36, plain, (![B_38]: (~r1_xboole_0(k1_tarski(B_38), k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.94/2.06  tff(c_121, plain, (![B_38]: (k4_xboole_0(k1_tarski(B_38), k1_tarski(B_38))!=k1_tarski(B_38))), inference(resolution, [status(thm)], [c_117, c_36])).
% 4.94/2.06  tff(c_400, plain, (![B_38]: (k1_tarski(B_38)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_397, c_121])).
% 4.94/2.06  tff(c_40, plain, (![A_41]: (k1_setfam_1(k1_tarski(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.94/2.06  tff(c_30, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.94/2.06  tff(c_28, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.94/2.06  tff(c_32, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.94/2.06  tff(c_569, plain, (![A_95, B_96, C_97, D_98]: (k2_xboole_0(k1_enumset1(A_95, B_96, C_97), k1_tarski(D_98))=k2_enumset1(A_95, B_96, C_97, D_98))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.94/2.06  tff(c_578, plain, (![A_30, B_31, D_98]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_tarski(D_98))=k2_enumset1(A_30, A_30, B_31, D_98))), inference(superposition, [status(thm), theory('equality')], [c_30, c_569])).
% 4.94/2.06  tff(c_2649, plain, (![A_181, B_182, D_183]: (k2_xboole_0(k2_tarski(A_181, B_182), k1_tarski(D_183))=k1_enumset1(A_181, B_182, D_183))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_578])).
% 4.94/2.06  tff(c_2658, plain, (![A_29, D_183]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(D_183))=k1_enumset1(A_29, A_29, D_183))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2649])).
% 4.94/2.06  tff(c_2661, plain, (![A_29, D_183]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(D_183))=k2_tarski(A_29, D_183))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2658])).
% 4.94/2.06  tff(c_720, plain, (![A_105, B_106]: (k3_xboole_0(k1_setfam_1(A_105), k1_setfam_1(B_106))=k1_setfam_1(k2_xboole_0(A_105, B_106)) | k1_xboole_0=B_106 | k1_xboole_0=A_105)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.94/2.06  tff(c_767, plain, (![A_105, A_41]: (k1_setfam_1(k2_xboole_0(A_105, k1_tarski(A_41)))=k3_xboole_0(k1_setfam_1(A_105), A_41) | k1_tarski(A_41)=k1_xboole_0 | k1_xboole_0=A_105)), inference(superposition, [status(thm), theory('equality')], [c_40, c_720])).
% 4.94/2.06  tff(c_4353, plain, (![A_213, A_214]: (k1_setfam_1(k2_xboole_0(A_213, k1_tarski(A_214)))=k3_xboole_0(k1_setfam_1(A_213), A_214) | k1_xboole_0=A_213)), inference(negUnitSimplification, [status(thm)], [c_400, c_767])).
% 4.94/2.06  tff(c_4368, plain, (![A_29, D_183]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_29)), D_183)=k1_setfam_1(k2_tarski(A_29, D_183)) | k1_tarski(A_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2661, c_4353])).
% 4.94/2.06  tff(c_4384, plain, (![A_29, D_183]: (k1_setfam_1(k2_tarski(A_29, D_183))=k3_xboole_0(A_29, D_183) | k1_tarski(A_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4368])).
% 4.94/2.06  tff(c_4385, plain, (![A_29, D_183]: (k1_setfam_1(k2_tarski(A_29, D_183))=k3_xboole_0(A_29, D_183))), inference(negUnitSimplification, [status(thm)], [c_400, c_4384])).
% 4.94/2.06  tff(c_42, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.94/2.06  tff(c_43, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 4.94/2.06  tff(c_4388, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4385, c_43])).
% 4.94/2.06  tff(c_4391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4388])).
% 4.94/2.06  tff(c_4393, plain, (![A_215]: (~r1_xboole_0(A_215, k1_xboole_0))), inference(splitRight, [status(thm)], [c_341])).
% 4.94/2.06  tff(c_4399, plain, (![A_216]: (k4_xboole_0(A_216, k1_xboole_0)!=A_216)), inference(resolution, [status(thm)], [c_22, c_4393])).
% 4.94/2.06  tff(c_4405, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_278, c_4399])).
% 4.94/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/2.06  
% 4.94/2.06  Inference rules
% 4.94/2.06  ----------------------
% 4.94/2.06  #Ref     : 1
% 4.94/2.06  #Sup     : 1127
% 4.94/2.06  #Fact    : 0
% 4.94/2.06  #Define  : 0
% 4.94/2.06  #Split   : 1
% 4.94/2.06  #Chain   : 0
% 4.94/2.06  #Close   : 0
% 4.94/2.06  
% 4.94/2.06  Ordering : KBO
% 4.94/2.06  
% 4.94/2.06  Simplification rules
% 4.94/2.06  ----------------------
% 4.94/2.06  #Subsume      : 344
% 4.94/2.06  #Demod        : 704
% 4.94/2.06  #Tautology    : 548
% 4.94/2.06  #SimpNegUnit  : 10
% 4.94/2.06  #BackRed      : 3
% 4.94/2.06  
% 4.94/2.06  #Partial instantiations: 0
% 4.94/2.06  #Strategies tried      : 1
% 4.94/2.06  
% 4.94/2.06  Timing (in seconds)
% 4.94/2.06  ----------------------
% 4.94/2.06  Preprocessing        : 0.34
% 4.94/2.06  Parsing              : 0.18
% 4.94/2.06  CNF conversion       : 0.02
% 4.94/2.06  Main loop            : 0.90
% 4.94/2.06  Inferencing          : 0.29
% 4.94/2.06  Reduction            : 0.38
% 4.94/2.06  Demodulation         : 0.31
% 4.94/2.06  BG Simplification    : 0.03
% 4.94/2.06  Subsumption          : 0.14
% 4.94/2.06  Abstraction          : 0.05
% 4.94/2.07  MUC search           : 0.00
% 4.94/2.07  Cooper               : 0.00
% 4.94/2.07  Total                : 1.27
% 4.94/2.07  Index Insertion      : 0.00
% 4.94/2.07  Index Deletion       : 0.00
% 4.94/2.07  Index Matching       : 0.00
% 4.94/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
