%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:14 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 180 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :   95 ( 219 expanded)
%              Number of equality atoms :   46 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_78,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_76,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_810,plain,(
    ! [A_119,B_120,C_121] :
      ( r1_tarski(k2_tarski(A_119,B_120),C_121)
      | ~ r2_hidden(B_120,C_121)
      | ~ r2_hidden(A_119,C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_836,plain,(
    ! [A_119,B_120,C_121] :
      ( k3_xboole_0(k2_tarski(A_119,B_120),C_121) = k2_tarski(A_119,B_120)
      | ~ r2_hidden(B_120,C_121)
      | ~ r2_hidden(A_119,C_121) ) ),
    inference(resolution,[status(thm)],[c_810,c_50])).

tff(c_48,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_460,plain,(
    ! [B_72,C_73,A_74] :
      ( r2_hidden(B_72,C_73)
      | ~ r1_tarski(k2_tarski(A_74,B_72),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_472,plain,(
    ! [B_75,A_76] : r2_hidden(B_75,k2_tarski(A_76,B_75)) ),
    inference(resolution,[status(thm)],[c_44,c_460])).

tff(c_475,plain,(
    ! [B_26,A_25] : r2_hidden(B_26,k2_tarski(B_26,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_472])).

tff(c_166,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_276,plain,(
    ! [B_62,A_63] : k3_tarski(k2_tarski(B_62,A_63)) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_166])).

tff(c_66,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_300,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_66])).

tff(c_316,plain,(
    ! [A_65] : k2_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_48])).

tff(c_619,plain,(
    ! [A_102,B_103] : k2_xboole_0(A_102,k4_xboole_0(B_103,A_102)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_626,plain,(
    ! [B_103] : k4_xboole_0(B_103,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_316])).

tff(c_644,plain,(
    ! [B_103] : k4_xboole_0(B_103,k1_xboole_0) = B_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_626])).

tff(c_52,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_157,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_181,plain,(
    ! [A_57] : k3_xboole_0(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_157])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_186,plain,(
    ! [A_57] : k3_xboole_0(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_2])).

tff(c_387,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_396,plain,(
    ! [A_57] : k5_xboole_0(A_57,k1_xboole_0) = k4_xboole_0(A_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_387])).

tff(c_650,plain,(
    ! [A_57] : k5_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_396])).

tff(c_164,plain,(
    ! [A_22] : k3_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_157])).

tff(c_402,plain,(
    ! [A_22] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_387])).

tff(c_708,plain,(
    ! [A_106] : k4_xboole_0(k1_xboole_0,A_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_402])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_766,plain,(
    ! [D_113,A_114] :
      ( ~ r2_hidden(D_113,A_114)
      | ~ r2_hidden(D_113,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_24])).

tff(c_778,plain,(
    ! [B_26] : ~ r2_hidden(B_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_475,c_766])).

tff(c_1722,plain,(
    ! [A_184,B_185,C_186] :
      ( r2_hidden('#skF_3'(A_184,B_185,C_186),A_184)
      | r2_hidden('#skF_4'(A_184,B_185,C_186),C_186)
      | k4_xboole_0(A_184,B_185) = C_186 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1778,plain,(
    ! [A_187,B_188] :
      ( r2_hidden('#skF_3'(A_187,B_188,k1_xboole_0),A_187)
      | k4_xboole_0(A_187,B_188) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1722,c_778])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3006,plain,(
    ! [A_254,B_255,B_256] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_254,B_255),B_256,k1_xboole_0),B_255)
      | k4_xboole_0(k3_xboole_0(A_254,B_255),B_256) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1778,c_6])).

tff(c_36,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),B_10)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3012,plain,(
    ! [A_254,B_255] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_254,B_255),B_255,k1_xboole_0),k1_xboole_0)
      | k4_xboole_0(k3_xboole_0(A_254,B_255),B_255) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3006,c_36])).

tff(c_3079,plain,(
    ! [A_257,B_258] : k4_xboole_0(k3_xboole_0(A_257,B_258),B_258) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_778,c_3012])).

tff(c_54,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3109,plain,(
    ! [B_258,A_257] : k2_xboole_0(B_258,k3_xboole_0(A_257,B_258)) = k2_xboole_0(B_258,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3079,c_54])).

tff(c_3190,plain,(
    ! [B_262,A_263] : k2_xboole_0(B_262,k3_xboole_0(A_263,B_262)) = B_262 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3109])).

tff(c_3470,plain,(
    ! [C_271,A_272,B_273] :
      ( k2_xboole_0(C_271,k2_tarski(A_272,B_273)) = C_271
      | ~ r2_hidden(B_273,C_271)
      | ~ r2_hidden(A_272,C_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_3190])).

tff(c_282,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_66])).

tff(c_74,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_299,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_5','#skF_7')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_74])).

tff(c_3484,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3470,c_299])).

tff(c_3523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_3484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:39:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.80  
% 4.34/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.80  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 4.34/1.80  
% 4.34/1.80  %Foreground sorts:
% 4.34/1.80  
% 4.34/1.80  
% 4.34/1.80  %Background operators:
% 4.34/1.80  
% 4.34/1.80  
% 4.34/1.80  %Foreground operators:
% 4.34/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.34/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.34/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.34/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.34/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.34/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.34/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.34/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.34/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.34/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.34/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.34/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.34/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.34/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.34/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.34/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.34/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.34/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.34/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.34/1.80  
% 4.56/1.82  tff(f_89, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 4.56/1.82  tff(f_82, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.56/1.82  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.56/1.82  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.56/1.82  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.56/1.82  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.56/1.82  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.56/1.82  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.56/1.82  tff(f_62, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.56/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.56/1.82  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.56/1.82  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.56/1.82  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.56/1.82  tff(c_78, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.82  tff(c_76, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.82  tff(c_810, plain, (![A_119, B_120, C_121]: (r1_tarski(k2_tarski(A_119, B_120), C_121) | ~r2_hidden(B_120, C_121) | ~r2_hidden(A_119, C_121))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.56/1.82  tff(c_50, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.56/1.82  tff(c_836, plain, (![A_119, B_120, C_121]: (k3_xboole_0(k2_tarski(A_119, B_120), C_121)=k2_tarski(A_119, B_120) | ~r2_hidden(B_120, C_121) | ~r2_hidden(A_119, C_121))), inference(resolution, [status(thm)], [c_810, c_50])).
% 4.56/1.82  tff(c_48, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.82  tff(c_56, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.56/1.82  tff(c_44, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.56/1.82  tff(c_460, plain, (![B_72, C_73, A_74]: (r2_hidden(B_72, C_73) | ~r1_tarski(k2_tarski(A_74, B_72), C_73))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.56/1.82  tff(c_472, plain, (![B_75, A_76]: (r2_hidden(B_75, k2_tarski(A_76, B_75)))), inference(resolution, [status(thm)], [c_44, c_460])).
% 4.56/1.82  tff(c_475, plain, (![B_26, A_25]: (r2_hidden(B_26, k2_tarski(B_26, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_472])).
% 4.56/1.82  tff(c_166, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/1.82  tff(c_276, plain, (![B_62, A_63]: (k3_tarski(k2_tarski(B_62, A_63))=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_56, c_166])).
% 4.56/1.82  tff(c_66, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/1.82  tff(c_300, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_276, c_66])).
% 4.56/1.82  tff(c_316, plain, (![A_65]: (k2_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_300, c_48])).
% 4.56/1.82  tff(c_619, plain, (![A_102, B_103]: (k2_xboole_0(A_102, k4_xboole_0(B_103, A_102))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.82  tff(c_626, plain, (![B_103]: (k4_xboole_0(B_103, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_103))), inference(superposition, [status(thm), theory('equality')], [c_619, c_316])).
% 4.56/1.82  tff(c_644, plain, (![B_103]: (k4_xboole_0(B_103, k1_xboole_0)=B_103)), inference(demodulation, [status(thm), theory('equality')], [c_316, c_626])).
% 4.56/1.82  tff(c_52, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.56/1.82  tff(c_157, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.56/1.82  tff(c_181, plain, (![A_57]: (k3_xboole_0(k1_xboole_0, A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_157])).
% 4.56/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.82  tff(c_186, plain, (![A_57]: (k3_xboole_0(A_57, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_181, c_2])).
% 4.56/1.82  tff(c_387, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.56/1.82  tff(c_396, plain, (![A_57]: (k5_xboole_0(A_57, k1_xboole_0)=k4_xboole_0(A_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_186, c_387])).
% 4.56/1.82  tff(c_650, plain, (![A_57]: (k5_xboole_0(A_57, k1_xboole_0)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_644, c_396])).
% 4.56/1.82  tff(c_164, plain, (![A_22]: (k3_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_157])).
% 4.56/1.82  tff(c_402, plain, (![A_22]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_22))), inference(superposition, [status(thm), theory('equality')], [c_164, c_387])).
% 4.56/1.82  tff(c_708, plain, (![A_106]: (k4_xboole_0(k1_xboole_0, A_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_650, c_402])).
% 4.56/1.82  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.56/1.82  tff(c_766, plain, (![D_113, A_114]: (~r2_hidden(D_113, A_114) | ~r2_hidden(D_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_708, c_24])).
% 4.56/1.82  tff(c_778, plain, (![B_26]: (~r2_hidden(B_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_475, c_766])).
% 4.56/1.82  tff(c_1722, plain, (![A_184, B_185, C_186]: (r2_hidden('#skF_3'(A_184, B_185, C_186), A_184) | r2_hidden('#skF_4'(A_184, B_185, C_186), C_186) | k4_xboole_0(A_184, B_185)=C_186)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.56/1.82  tff(c_1778, plain, (![A_187, B_188]: (r2_hidden('#skF_3'(A_187, B_188, k1_xboole_0), A_187) | k4_xboole_0(A_187, B_188)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1722, c_778])).
% 4.56/1.82  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.56/1.82  tff(c_3006, plain, (![A_254, B_255, B_256]: (r2_hidden('#skF_3'(k3_xboole_0(A_254, B_255), B_256, k1_xboole_0), B_255) | k4_xboole_0(k3_xboole_0(A_254, B_255), B_256)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1778, c_6])).
% 4.56/1.82  tff(c_36, plain, (![A_9, B_10, C_11]: (~r2_hidden('#skF_3'(A_9, B_10, C_11), B_10) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.56/1.82  tff(c_3012, plain, (![A_254, B_255]: (r2_hidden('#skF_4'(k3_xboole_0(A_254, B_255), B_255, k1_xboole_0), k1_xboole_0) | k4_xboole_0(k3_xboole_0(A_254, B_255), B_255)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3006, c_36])).
% 4.56/1.82  tff(c_3079, plain, (![A_257, B_258]: (k4_xboole_0(k3_xboole_0(A_257, B_258), B_258)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_778, c_3012])).
% 4.56/1.82  tff(c_54, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.82  tff(c_3109, plain, (![B_258, A_257]: (k2_xboole_0(B_258, k3_xboole_0(A_257, B_258))=k2_xboole_0(B_258, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3079, c_54])).
% 4.56/1.82  tff(c_3190, plain, (![B_262, A_263]: (k2_xboole_0(B_262, k3_xboole_0(A_263, B_262))=B_262)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3109])).
% 4.56/1.82  tff(c_3470, plain, (![C_271, A_272, B_273]: (k2_xboole_0(C_271, k2_tarski(A_272, B_273))=C_271 | ~r2_hidden(B_273, C_271) | ~r2_hidden(A_272, C_271))), inference(superposition, [status(thm), theory('equality')], [c_836, c_3190])).
% 4.56/1.82  tff(c_282, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_276, c_66])).
% 4.56/1.82  tff(c_74, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.82  tff(c_299, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_5', '#skF_7'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_74])).
% 4.56/1.82  tff(c_3484, plain, (~r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3470, c_299])).
% 4.56/1.82  tff(c_3523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_3484])).
% 4.56/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.82  
% 4.56/1.82  Inference rules
% 4.56/1.82  ----------------------
% 4.56/1.82  #Ref     : 0
% 4.56/1.82  #Sup     : 811
% 4.56/1.82  #Fact    : 0
% 4.56/1.82  #Define  : 0
% 4.56/1.82  #Split   : 0
% 4.56/1.82  #Chain   : 0
% 4.56/1.82  #Close   : 0
% 4.56/1.82  
% 4.56/1.82  Ordering : KBO
% 4.56/1.82  
% 4.56/1.82  Simplification rules
% 4.56/1.82  ----------------------
% 4.56/1.82  #Subsume      : 187
% 4.56/1.82  #Demod        : 317
% 4.56/1.82  #Tautology    : 313
% 4.56/1.82  #SimpNegUnit  : 34
% 4.56/1.82  #BackRed      : 4
% 4.56/1.82  
% 4.56/1.82  #Partial instantiations: 0
% 4.56/1.82  #Strategies tried      : 1
% 4.56/1.82  
% 4.56/1.82  Timing (in seconds)
% 4.56/1.82  ----------------------
% 4.56/1.82  Preprocessing        : 0.32
% 4.56/1.82  Parsing              : 0.16
% 4.56/1.82  CNF conversion       : 0.02
% 4.56/1.82  Main loop            : 0.73
% 4.56/1.82  Inferencing          : 0.23
% 4.56/1.82  Reduction            : 0.28
% 4.56/1.82  Demodulation         : 0.22
% 4.56/1.82  BG Simplification    : 0.03
% 4.56/1.82  Subsumption          : 0.14
% 4.56/1.82  Abstraction          : 0.03
% 4.56/1.82  MUC search           : 0.00
% 4.56/1.82  Cooper               : 0.00
% 4.56/1.82  Total                : 1.08
% 4.56/1.82  Index Insertion      : 0.00
% 4.56/1.82  Index Deletion       : 0.00
% 4.56/1.82  Index Matching       : 0.00
% 4.56/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
