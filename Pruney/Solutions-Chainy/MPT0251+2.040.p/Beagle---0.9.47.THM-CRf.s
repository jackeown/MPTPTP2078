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
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 131 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :   78 ( 143 expanded)
%              Number of equality atoms :   42 (  93 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_133,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_178,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_133])).

tff(c_44,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_205,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_44])).

tff(c_221,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_20])).

tff(c_418,plain,(
    ! [A_81,B_82] : k2_xboole_0(A_81,k4_xboole_0(B_82,A_81)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_428,plain,(
    ! [B_82] : k4_xboole_0(B_82,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_221])).

tff(c_446,plain,(
    ! [B_82] : k4_xboole_0(B_82,k1_xboole_0) = B_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_428])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_107,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_16,c_103])).

tff(c_352,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,k3_xboole_0(A_72,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_361,plain,(
    ! [B_75,C_76] :
      ( ~ r1_xboole_0(B_75,B_75)
      | ~ r2_hidden(C_76,B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_352])).

tff(c_366,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_361])).

tff(c_372,plain,(
    ! [B_78] : r1_tarski(k1_xboole_0,B_78) ),
    inference(resolution,[status(thm)],[c_6,c_366])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_379,plain,(
    ! [B_78] : k3_xboole_0(k1_xboole_0,B_78) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_372,c_22])).

tff(c_513,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_581,plain,(
    ! [B_90] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_513])).

tff(c_525,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k4_xboole_0(B_12,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_513])).

tff(c_587,plain,(
    ! [B_90] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_525])).

tff(c_603,plain,(
    ! [B_90] : k4_xboole_0(k1_xboole_0,B_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_587])).

tff(c_300,plain,(
    ! [A_67,B_68] : k4_xboole_0(k2_xboole_0(A_67,B_68),B_68) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_309,plain,(
    ! [A_63] : k4_xboole_0(k1_xboole_0,A_63) = k4_xboole_0(A_63,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_300])).

tff(c_617,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_309])).

tff(c_667,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_525])).

tff(c_168,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tarski(A_56),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1104,plain,(
    ! [A_129,B_130] :
      ( k3_xboole_0(k1_tarski(A_129),B_130) = k1_tarski(A_129)
      | ~ r2_hidden(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_168,c_22])).

tff(c_18,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1123,plain,(
    ! [A_129,B_130] :
      ( k5_xboole_0(k1_tarski(A_129),k1_tarski(A_129)) = k4_xboole_0(k1_tarski(A_129),B_130)
      | ~ r2_hidden(A_129,B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_18])).

tff(c_1346,plain,(
    ! [A_141,B_142] :
      ( k4_xboole_0(k1_tarski(A_141),B_142) = k1_xboole_0
      | ~ r2_hidden(A_141,B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_1123])).

tff(c_24,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1371,plain,(
    ! [B_142,A_141] :
      ( k2_xboole_0(B_142,k1_tarski(A_141)) = k2_xboole_0(B_142,k1_xboole_0)
      | ~ r2_hidden(A_141,B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_24])).

tff(c_1504,plain,(
    ! [B_145,A_146] :
      ( k2_xboole_0(B_145,k1_tarski(A_146)) = B_145
      | ~ r2_hidden(A_146,B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1371])).

tff(c_184,plain,(
    ! [B_61,A_60] : k2_xboole_0(B_61,A_60) = k2_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_44])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_204,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_46])).

tff(c_1539,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1504,c_204])).

tff(c_1587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.13/1.51  
% 3.13/1.51  %Foreground sorts:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Background operators:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Foreground operators:
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.13/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.13/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.13/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.51  
% 3.13/1.52  tff(f_87, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.13/1.52  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.13/1.52  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.13/1.52  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.13/1.52  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.13/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.13/1.52  tff(f_66, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.13/1.52  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.52  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.13/1.52  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.13/1.52  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.13/1.52  tff(f_64, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.13/1.52  tff(f_80, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.13/1.52  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.13/1.52  tff(c_20, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.52  tff(c_30, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.52  tff(c_133, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.52  tff(c_178, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(B_61, A_60))), inference(superposition, [status(thm), theory('equality')], [c_30, c_133])).
% 3.13/1.52  tff(c_44, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.52  tff(c_205, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_178, c_44])).
% 3.13/1.52  tff(c_221, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_205, c_20])).
% 3.13/1.52  tff(c_418, plain, (![A_81, B_82]: (k2_xboole_0(A_81, k4_xboole_0(B_82, A_81))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.52  tff(c_428, plain, (![B_82]: (k4_xboole_0(B_82, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_82))), inference(superposition, [status(thm), theory('equality')], [c_418, c_221])).
% 3.13/1.52  tff(c_446, plain, (![B_82]: (k4_xboole_0(B_82, k1_xboole_0)=B_82)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_428])).
% 3.13/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.52  tff(c_28, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.52  tff(c_16, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.52  tff(c_103, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.52  tff(c_107, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_16, c_103])).
% 3.13/1.52  tff(c_352, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, k3_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.13/1.52  tff(c_361, plain, (![B_75, C_76]: (~r1_xboole_0(B_75, B_75) | ~r2_hidden(C_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_107, c_352])).
% 3.13/1.52  tff(c_366, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_361])).
% 3.13/1.52  tff(c_372, plain, (![B_78]: (r1_tarski(k1_xboole_0, B_78))), inference(resolution, [status(thm)], [c_6, c_366])).
% 3.13/1.52  tff(c_22, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.52  tff(c_379, plain, (![B_78]: (k3_xboole_0(k1_xboole_0, B_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_372, c_22])).
% 3.13/1.52  tff(c_513, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.52  tff(c_581, plain, (![B_90]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_90))), inference(superposition, [status(thm), theory('equality')], [c_379, c_513])).
% 3.13/1.52  tff(c_525, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k4_xboole_0(B_12, B_12))), inference(superposition, [status(thm), theory('equality')], [c_107, c_513])).
% 3.13/1.52  tff(c_587, plain, (![B_90]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_90))), inference(superposition, [status(thm), theory('equality')], [c_581, c_525])).
% 3.13/1.52  tff(c_603, plain, (![B_90]: (k4_xboole_0(k1_xboole_0, B_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_446, c_587])).
% 3.13/1.52  tff(c_300, plain, (![A_67, B_68]: (k4_xboole_0(k2_xboole_0(A_67, B_68), B_68)=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.52  tff(c_309, plain, (![A_63]: (k4_xboole_0(k1_xboole_0, A_63)=k4_xboole_0(A_63, A_63))), inference(superposition, [status(thm), theory('equality')], [c_221, c_300])).
% 3.13/1.52  tff(c_617, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_603, c_309])).
% 3.13/1.52  tff(c_667, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_617, c_525])).
% 3.13/1.52  tff(c_168, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), B_57) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.13/1.52  tff(c_1104, plain, (![A_129, B_130]: (k3_xboole_0(k1_tarski(A_129), B_130)=k1_tarski(A_129) | ~r2_hidden(A_129, B_130))), inference(resolution, [status(thm)], [c_168, c_22])).
% 3.13/1.52  tff(c_18, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.52  tff(c_1123, plain, (![A_129, B_130]: (k5_xboole_0(k1_tarski(A_129), k1_tarski(A_129))=k4_xboole_0(k1_tarski(A_129), B_130) | ~r2_hidden(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_1104, c_18])).
% 3.13/1.52  tff(c_1346, plain, (![A_141, B_142]: (k4_xboole_0(k1_tarski(A_141), B_142)=k1_xboole_0 | ~r2_hidden(A_141, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_667, c_1123])).
% 3.13/1.52  tff(c_24, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.52  tff(c_1371, plain, (![B_142, A_141]: (k2_xboole_0(B_142, k1_tarski(A_141))=k2_xboole_0(B_142, k1_xboole_0) | ~r2_hidden(A_141, B_142))), inference(superposition, [status(thm), theory('equality')], [c_1346, c_24])).
% 3.13/1.52  tff(c_1504, plain, (![B_145, A_146]: (k2_xboole_0(B_145, k1_tarski(A_146))=B_145 | ~r2_hidden(A_146, B_145))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1371])).
% 3.13/1.52  tff(c_184, plain, (![B_61, A_60]: (k2_xboole_0(B_61, A_60)=k2_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_178, c_44])).
% 3.13/1.52  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.13/1.52  tff(c_204, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_46])).
% 3.13/1.52  tff(c_1539, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1504, c_204])).
% 3.13/1.52  tff(c_1587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1539])).
% 3.13/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  Inference rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Ref     : 0
% 3.13/1.52  #Sup     : 357
% 3.13/1.52  #Fact    : 0
% 3.13/1.52  #Define  : 0
% 3.13/1.52  #Split   : 0
% 3.13/1.52  #Chain   : 0
% 3.13/1.52  #Close   : 0
% 3.13/1.52  
% 3.13/1.52  Ordering : KBO
% 3.13/1.52  
% 3.13/1.52  Simplification rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Subsume      : 25
% 3.13/1.52  #Demod        : 244
% 3.13/1.52  #Tautology    : 262
% 3.13/1.52  #SimpNegUnit  : 2
% 3.13/1.52  #BackRed      : 6
% 3.13/1.52  
% 3.13/1.52  #Partial instantiations: 0
% 3.13/1.52  #Strategies tried      : 1
% 3.13/1.52  
% 3.13/1.52  Timing (in seconds)
% 3.13/1.52  ----------------------
% 3.13/1.53  Preprocessing        : 0.30
% 3.13/1.53  Parsing              : 0.16
% 3.13/1.53  CNF conversion       : 0.02
% 3.13/1.53  Main loop            : 0.40
% 3.13/1.53  Inferencing          : 0.15
% 3.13/1.53  Reduction            : 0.15
% 3.13/1.53  Demodulation         : 0.12
% 3.13/1.53  BG Simplification    : 0.02
% 3.13/1.53  Subsumption          : 0.06
% 3.13/1.53  Abstraction          : 0.02
% 3.13/1.53  MUC search           : 0.00
% 3.13/1.53  Cooper               : 0.00
% 3.13/1.53  Total                : 0.73
% 3.13/1.53  Index Insertion      : 0.00
% 3.13/1.53  Index Deletion       : 0.00
% 3.13/1.53  Index Matching       : 0.00
% 3.13/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
