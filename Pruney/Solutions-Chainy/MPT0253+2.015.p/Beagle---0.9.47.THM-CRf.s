%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:16 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   77 (  98 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 140 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_64,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_62,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_300,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_873,plain,(
    ! [A_157,B_158,B_159] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_157,B_158),B_159),A_157)
      | r1_tarski(k4_xboole_0(A_157,B_158),B_159) ) ),
    inference(resolution,[status(thm)],[c_300,c_12])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_316,plain,(
    ! [A_6,B_7,B_76] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_76),B_7)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_76) ) ),
    inference(resolution,[status(thm)],[c_300,c_10])).

tff(c_912,plain,(
    ! [A_160,B_161] : r1_tarski(k4_xboole_0(A_160,A_160),B_161) ),
    inference(resolution,[status(thm)],[c_873,c_316])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_133])).

tff(c_324,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_336,plain,(
    ! [B_81] : k5_xboole_0(B_81,B_81) = k4_xboole_0(B_81,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_324])).

tff(c_40,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_343,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_40])).

tff(c_364,plain,(
    ! [D_82] :
      ( ~ r2_hidden(D_82,k1_xboole_0)
      | ~ r2_hidden(D_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_10])).

tff(c_541,plain,(
    ! [B_110] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_110),k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_364])).

tff(c_548,plain,(
    ! [B_111] : r1_tarski(k1_xboole_0,B_111) ),
    inference(resolution,[status(thm)],[c_6,c_541])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_554,plain,(
    ! [B_111] :
      ( k1_xboole_0 = B_111
      | ~ r1_tarski(B_111,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_548,c_26])).

tff(c_944,plain,(
    ! [A_160] : k4_xboole_0(A_160,A_160) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_912,c_554])).

tff(c_333,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_324])).

tff(c_956,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_333])).

tff(c_515,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(k2_tarski(A_105,B_106),C_107)
      | ~ r2_hidden(B_106,C_107)
      | ~ r2_hidden(A_105,C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2329,plain,(
    ! [A_290,B_291,C_292] :
      ( k3_xboole_0(k2_tarski(A_290,B_291),C_292) = k2_tarski(A_290,B_291)
      | ~ r2_hidden(B_291,C_292)
      | ~ r2_hidden(A_290,C_292) ) ),
    inference(resolution,[status(thm)],[c_515,c_36])).

tff(c_32,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2335,plain,(
    ! [A_290,B_291,C_292] :
      ( k5_xboole_0(k2_tarski(A_290,B_291),k2_tarski(A_290,B_291)) = k4_xboole_0(k2_tarski(A_290,B_291),C_292)
      | ~ r2_hidden(B_291,C_292)
      | ~ r2_hidden(A_290,C_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2329,c_32])).

tff(c_2362,plain,(
    ! [A_293,B_294,C_295] :
      ( k4_xboole_0(k2_tarski(A_293,B_294),C_295) = k1_xboole_0
      | ~ r2_hidden(B_294,C_295)
      | ~ r2_hidden(A_293,C_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_2335])).

tff(c_38,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2476,plain,(
    ! [C_295,A_293,B_294] :
      ( k2_xboole_0(C_295,k2_tarski(A_293,B_294)) = k2_xboole_0(C_295,k1_xboole_0)
      | ~ r2_hidden(B_294,C_295)
      | ~ r2_hidden(A_293,C_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2362,c_38])).

tff(c_2526,plain,(
    ! [C_296,A_297,B_298] :
      ( k2_xboole_0(C_296,k2_tarski(A_297,B_298)) = C_296
      | ~ r2_hidden(B_298,C_296)
      | ~ r2_hidden(A_297,C_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2476])).

tff(c_42,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_118,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_156,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_118])).

tff(c_52,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_162,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_52])).

tff(c_60,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_179,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_60])).

tff(c_2536,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2526,c_179])).

tff(c_2579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.72  
% 3.92/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.72  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.92/1.72  
% 3.92/1.72  %Foreground sorts:
% 3.92/1.72  
% 3.92/1.72  
% 3.92/1.72  %Background operators:
% 3.92/1.72  
% 3.92/1.72  
% 3.92/1.72  %Foreground operators:
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.92/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.92/1.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.92/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.92/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.92/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.92/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.92/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.92/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.92/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.92/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.92/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.92/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.92/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.92/1.72  
% 3.92/1.73  tff(f_85, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 3.92/1.73  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.92/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.92/1.73  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.92/1.73  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.92/1.73  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.92/1.73  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.92/1.73  tff(f_60, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.92/1.73  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.92/1.73  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.92/1.73  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.92/1.73  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.92/1.73  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.73  tff(c_62, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.73  tff(c_34, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.73  tff(c_300, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.73  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.92/1.73  tff(c_873, plain, (![A_157, B_158, B_159]: (r2_hidden('#skF_1'(k4_xboole_0(A_157, B_158), B_159), A_157) | r1_tarski(k4_xboole_0(A_157, B_158), B_159))), inference(resolution, [status(thm)], [c_300, c_12])).
% 3.92/1.73  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.92/1.73  tff(c_316, plain, (![A_6, B_7, B_76]: (~r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_76), B_7) | r1_tarski(k4_xboole_0(A_6, B_7), B_76))), inference(resolution, [status(thm)], [c_300, c_10])).
% 3.92/1.73  tff(c_912, plain, (![A_160, B_161]: (r1_tarski(k4_xboole_0(A_160, A_160), B_161))), inference(resolution, [status(thm)], [c_873, c_316])).
% 3.92/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.73  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.92/1.73  tff(c_133, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/1.73  tff(c_137, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_133])).
% 3.92/1.73  tff(c_324, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.92/1.73  tff(c_336, plain, (![B_81]: (k5_xboole_0(B_81, B_81)=k4_xboole_0(B_81, B_81))), inference(superposition, [status(thm), theory('equality')], [c_137, c_324])).
% 3.92/1.73  tff(c_40, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.92/1.73  tff(c_343, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_336, c_40])).
% 3.92/1.73  tff(c_364, plain, (![D_82]: (~r2_hidden(D_82, k1_xboole_0) | ~r2_hidden(D_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_343, c_10])).
% 3.92/1.73  tff(c_541, plain, (![B_110]: (~r2_hidden('#skF_1'(k1_xboole_0, B_110), k1_xboole_0) | r1_tarski(k1_xboole_0, B_110))), inference(resolution, [status(thm)], [c_6, c_364])).
% 3.92/1.73  tff(c_548, plain, (![B_111]: (r1_tarski(k1_xboole_0, B_111))), inference(resolution, [status(thm)], [c_6, c_541])).
% 3.92/1.73  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.92/1.73  tff(c_554, plain, (![B_111]: (k1_xboole_0=B_111 | ~r1_tarski(B_111, k1_xboole_0))), inference(resolution, [status(thm)], [c_548, c_26])).
% 3.92/1.73  tff(c_944, plain, (![A_160]: (k4_xboole_0(A_160, A_160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_912, c_554])).
% 3.92/1.73  tff(c_333, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_137, c_324])).
% 3.92/1.73  tff(c_956, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_944, c_333])).
% 3.92/1.73  tff(c_515, plain, (![A_105, B_106, C_107]: (r1_tarski(k2_tarski(A_105, B_106), C_107) | ~r2_hidden(B_106, C_107) | ~r2_hidden(A_105, C_107))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.92/1.73  tff(c_36, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/1.73  tff(c_2329, plain, (![A_290, B_291, C_292]: (k3_xboole_0(k2_tarski(A_290, B_291), C_292)=k2_tarski(A_290, B_291) | ~r2_hidden(B_291, C_292) | ~r2_hidden(A_290, C_292))), inference(resolution, [status(thm)], [c_515, c_36])).
% 3.92/1.73  tff(c_32, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.92/1.73  tff(c_2335, plain, (![A_290, B_291, C_292]: (k5_xboole_0(k2_tarski(A_290, B_291), k2_tarski(A_290, B_291))=k4_xboole_0(k2_tarski(A_290, B_291), C_292) | ~r2_hidden(B_291, C_292) | ~r2_hidden(A_290, C_292))), inference(superposition, [status(thm), theory('equality')], [c_2329, c_32])).
% 3.92/1.73  tff(c_2362, plain, (![A_293, B_294, C_295]: (k4_xboole_0(k2_tarski(A_293, B_294), C_295)=k1_xboole_0 | ~r2_hidden(B_294, C_295) | ~r2_hidden(A_293, C_295))), inference(demodulation, [status(thm), theory('equality')], [c_956, c_2335])).
% 3.92/1.73  tff(c_38, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.92/1.73  tff(c_2476, plain, (![C_295, A_293, B_294]: (k2_xboole_0(C_295, k2_tarski(A_293, B_294))=k2_xboole_0(C_295, k1_xboole_0) | ~r2_hidden(B_294, C_295) | ~r2_hidden(A_293, C_295))), inference(superposition, [status(thm), theory('equality')], [c_2362, c_38])).
% 3.92/1.73  tff(c_2526, plain, (![C_296, A_297, B_298]: (k2_xboole_0(C_296, k2_tarski(A_297, B_298))=C_296 | ~r2_hidden(B_298, C_296) | ~r2_hidden(A_297, C_296))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2476])).
% 3.92/1.73  tff(c_42, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.92/1.73  tff(c_118, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.92/1.73  tff(c_156, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_42, c_118])).
% 3.92/1.73  tff(c_52, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.92/1.73  tff(c_162, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_156, c_52])).
% 3.92/1.73  tff(c_60, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.73  tff(c_179, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_60])).
% 3.92/1.73  tff(c_2536, plain, (~r2_hidden('#skF_6', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2526, c_179])).
% 3.92/1.73  tff(c_2579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2536])).
% 3.92/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.73  
% 3.92/1.73  Inference rules
% 3.92/1.73  ----------------------
% 3.92/1.73  #Ref     : 0
% 3.92/1.73  #Sup     : 591
% 3.92/1.73  #Fact    : 0
% 3.92/1.73  #Define  : 0
% 3.92/1.73  #Split   : 4
% 3.92/1.73  #Chain   : 0
% 3.92/1.73  #Close   : 0
% 3.92/1.73  
% 3.92/1.73  Ordering : KBO
% 3.92/1.73  
% 3.92/1.73  Simplification rules
% 3.92/1.73  ----------------------
% 3.92/1.73  #Subsume      : 200
% 3.92/1.73  #Demod        : 258
% 3.92/1.73  #Tautology    : 239
% 3.92/1.73  #SimpNegUnit  : 15
% 3.92/1.73  #BackRed      : 3
% 3.92/1.73  
% 3.92/1.73  #Partial instantiations: 0
% 3.92/1.73  #Strategies tried      : 1
% 3.92/1.73  
% 3.92/1.73  Timing (in seconds)
% 3.92/1.73  ----------------------
% 3.92/1.74  Preprocessing        : 0.33
% 3.92/1.74  Parsing              : 0.17
% 3.92/1.74  CNF conversion       : 0.03
% 3.92/1.74  Main loop            : 0.63
% 3.92/1.74  Inferencing          : 0.22
% 3.92/1.74  Reduction            : 0.21
% 3.92/1.74  Demodulation         : 0.15
% 3.92/1.74  BG Simplification    : 0.02
% 3.92/1.74  Subsumption          : 0.14
% 3.92/1.74  Abstraction          : 0.03
% 3.92/1.74  MUC search           : 0.00
% 3.92/1.74  Cooper               : 0.00
% 3.92/1.74  Total                : 1.00
% 3.92/1.74  Index Insertion      : 0.00
% 3.92/1.74  Index Deletion       : 0.00
% 3.92/1.74  Index Matching       : 0.00
% 3.92/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
