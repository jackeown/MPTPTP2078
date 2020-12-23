%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 9.46s
% Output     : CNFRefutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 110 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 134 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_60,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1765,plain,(
    ! [A_174,B_175,C_176] :
      ( ~ r2_hidden('#skF_2'(A_174,B_175,C_176),B_175)
      | r2_hidden('#skF_3'(A_174,B_175,C_176),C_176)
      | k4_xboole_0(A_174,B_175) = C_176 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1772,plain,(
    ! [A_8,C_10] :
      ( r2_hidden('#skF_3'(A_8,A_8,C_10),C_10)
      | k4_xboole_0(A_8,A_8) = C_10 ) ),
    inference(resolution,[status(thm)],[c_26,c_1765])).

tff(c_87,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_109,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_36])).

tff(c_543,plain,(
    ! [A_86,B_87] : k2_xboole_0(A_86,k4_xboole_0(B_87,A_86)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_563,plain,(
    ! [B_87] : k4_xboole_0(B_87,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_109])).

tff(c_577,plain,(
    ! [B_87] : k4_xboole_0(B_87,k1_xboole_0) = B_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_563])).

tff(c_42,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [B_44,A_45] : r1_tarski(B_44,k2_xboole_0(A_45,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_42])).

tff(c_181,plain,(
    ! [A_48,B_49] :
      ( r2_hidden(A_48,B_49)
      | ~ r1_tarski(k1_tarski(A_48),B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_190,plain,(
    ! [A_48,B_24] : r2_hidden(A_48,k2_xboole_0(k1_tarski(A_48),B_24)) ),
    inference(resolution,[status(thm)],[c_42,c_181])).

tff(c_857,plain,(
    ! [C_108,B_109,A_110] :
      ( r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1322,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden(A_141,B_142)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_141),B_143),B_142) ) ),
    inference(resolution,[status(thm)],[c_190,c_857])).

tff(c_1360,plain,(
    ! [A_141,A_45,B_143] : r2_hidden(A_141,k2_xboole_0(A_45,k2_xboole_0(k1_tarski(A_141),B_143))) ),
    inference(resolution,[status(thm)],[c_105,c_1322])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_312,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_332,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_312])).

tff(c_715,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_736,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_715])).

tff(c_331,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = A_23 ),
    inference(resolution,[status(thm)],[c_42,c_312])).

tff(c_730,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k5_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_715])).

tff(c_920,plain,(
    ! [A_116,B_117] : k4_xboole_0(A_116,k2_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_730])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2636,plain,(
    ! [D_229,A_230,B_231] :
      ( ~ r2_hidden(D_229,k2_xboole_0(A_230,B_231))
      | ~ r2_hidden(D_229,k4_xboole_0(A_230,A_230)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_12])).

tff(c_2735,plain,(
    ! [A_234,A_235] : ~ r2_hidden(A_234,k4_xboole_0(A_235,A_235)) ),
    inference(resolution,[status(thm)],[c_1360,c_2636])).

tff(c_2788,plain,(
    ! [A_236] : ~ r2_hidden(A_236,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_2735])).

tff(c_2819,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1772,c_2788])).

tff(c_395,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_tarski(A_70),B_71)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1230,plain,(
    ! [A_137,B_138] :
      ( k3_xboole_0(k1_tarski(A_137),B_138) = k1_tarski(A_137)
      | ~ r2_hidden(A_137,B_138) ) ),
    inference(resolution,[status(thm)],[c_395,c_38])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1236,plain,(
    ! [A_137,B_138] :
      ( k5_xboole_0(k1_tarski(A_137),k1_tarski(A_137)) = k4_xboole_0(k1_tarski(A_137),B_138)
      | ~ r2_hidden(A_137,B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_34])).

tff(c_1273,plain,(
    ! [A_137,B_138] :
      ( k4_xboole_0(k1_tarski(A_137),k1_tarski(A_137)) = k4_xboole_0(k1_tarski(A_137),B_138)
      | ~ r2_hidden(A_137,B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_1236])).

tff(c_18594,plain,(
    ! [A_487,B_488] :
      ( k4_xboole_0(k1_tarski(A_487),B_488) = k1_xboole_0
      | ~ r2_hidden(A_487,B_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_1273])).

tff(c_40,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18788,plain,(
    ! [B_488,A_487] :
      ( k2_xboole_0(B_488,k1_tarski(A_487)) = k2_xboole_0(B_488,k1_xboole_0)
      | ~ r2_hidden(A_487,B_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18594,c_40])).

tff(c_18865,plain,(
    ! [B_489,A_490] :
      ( k2_xboole_0(B_489,k1_tarski(A_490)) = B_489
      | ~ r2_hidden(A_490,B_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18788])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_19171,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18865,c_62])).

tff(c_19280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_19171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:19:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.46/3.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.80  
% 9.46/3.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.80  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 9.46/3.80  
% 9.46/3.80  %Foreground sorts:
% 9.46/3.80  
% 9.46/3.80  
% 9.46/3.80  %Background operators:
% 9.46/3.80  
% 9.46/3.80  
% 9.46/3.80  %Foreground operators:
% 9.46/3.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.46/3.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.46/3.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.46/3.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.46/3.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.46/3.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.46/3.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.46/3.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.46/3.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.46/3.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.46/3.80  tff('#skF_5', type, '#skF_5': $i).
% 9.46/3.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.46/3.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.46/3.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.46/3.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.46/3.80  tff('#skF_4', type, '#skF_4': $i).
% 9.46/3.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.46/3.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.46/3.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.46/3.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.46/3.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.46/3.80  
% 9.46/3.82  tff(f_81, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 9.46/3.82  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.46/3.82  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.46/3.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.46/3.82  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.46/3.82  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.46/3.82  tff(f_74, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.46/3.82  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.46/3.82  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.46/3.82  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.46/3.82  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.46/3.82  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.82  tff(c_36, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.46/3.82  tff(c_26, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_2'(A_8, B_9, C_10), A_8) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.46/3.82  tff(c_1765, plain, (![A_174, B_175, C_176]: (~r2_hidden('#skF_2'(A_174, B_175, C_176), B_175) | r2_hidden('#skF_3'(A_174, B_175, C_176), C_176) | k4_xboole_0(A_174, B_175)=C_176)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.46/3.82  tff(c_1772, plain, (![A_8, C_10]: (r2_hidden('#skF_3'(A_8, A_8, C_10), C_10) | k4_xboole_0(A_8, A_8)=C_10)), inference(resolution, [status(thm)], [c_26, c_1765])).
% 9.46/3.82  tff(c_87, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.46/3.82  tff(c_109, plain, (![A_45]: (k2_xboole_0(k1_xboole_0, A_45)=A_45)), inference(superposition, [status(thm), theory('equality')], [c_87, c_36])).
% 9.46/3.82  tff(c_543, plain, (![A_86, B_87]: (k2_xboole_0(A_86, k4_xboole_0(B_87, A_86))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.46/3.82  tff(c_563, plain, (![B_87]: (k4_xboole_0(B_87, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_87))), inference(superposition, [status(thm), theory('equality')], [c_543, c_109])).
% 9.46/3.82  tff(c_577, plain, (![B_87]: (k4_xboole_0(B_87, k1_xboole_0)=B_87)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_563])).
% 9.46/3.82  tff(c_42, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.46/3.82  tff(c_105, plain, (![B_44, A_45]: (r1_tarski(B_44, k2_xboole_0(A_45, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_42])).
% 9.46/3.82  tff(c_181, plain, (![A_48, B_49]: (r2_hidden(A_48, B_49) | ~r1_tarski(k1_tarski(A_48), B_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.46/3.82  tff(c_190, plain, (![A_48, B_24]: (r2_hidden(A_48, k2_xboole_0(k1_tarski(A_48), B_24)))), inference(resolution, [status(thm)], [c_42, c_181])).
% 9.46/3.82  tff(c_857, plain, (![C_108, B_109, A_110]: (r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.46/3.82  tff(c_1322, plain, (![A_141, B_142, B_143]: (r2_hidden(A_141, B_142) | ~r1_tarski(k2_xboole_0(k1_tarski(A_141), B_143), B_142))), inference(resolution, [status(thm)], [c_190, c_857])).
% 9.46/3.82  tff(c_1360, plain, (![A_141, A_45, B_143]: (r2_hidden(A_141, k2_xboole_0(A_45, k2_xboole_0(k1_tarski(A_141), B_143))))), inference(resolution, [status(thm)], [c_105, c_1322])).
% 9.46/3.82  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.46/3.82  tff(c_312, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.46/3.82  tff(c_332, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_312])).
% 9.46/3.82  tff(c_715, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.46/3.82  tff(c_736, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_332, c_715])).
% 9.46/3.82  tff(c_331, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k2_xboole_0(A_23, B_24))=A_23)), inference(resolution, [status(thm)], [c_42, c_312])).
% 9.46/3.82  tff(c_730, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k5_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_331, c_715])).
% 9.46/3.82  tff(c_920, plain, (![A_116, B_117]: (k4_xboole_0(A_116, k2_xboole_0(A_116, B_117))=k4_xboole_0(A_116, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_730])).
% 9.46/3.82  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.46/3.82  tff(c_2636, plain, (![D_229, A_230, B_231]: (~r2_hidden(D_229, k2_xboole_0(A_230, B_231)) | ~r2_hidden(D_229, k4_xboole_0(A_230, A_230)))), inference(superposition, [status(thm), theory('equality')], [c_920, c_12])).
% 9.46/3.82  tff(c_2735, plain, (![A_234, A_235]: (~r2_hidden(A_234, k4_xboole_0(A_235, A_235)))), inference(resolution, [status(thm)], [c_1360, c_2636])).
% 9.46/3.82  tff(c_2788, plain, (![A_236]: (~r2_hidden(A_236, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_577, c_2735])).
% 9.46/3.82  tff(c_2819, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1772, c_2788])).
% 9.46/3.82  tff(c_395, plain, (![A_70, B_71]: (r1_tarski(k1_tarski(A_70), B_71) | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.46/3.82  tff(c_38, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.46/3.82  tff(c_1230, plain, (![A_137, B_138]: (k3_xboole_0(k1_tarski(A_137), B_138)=k1_tarski(A_137) | ~r2_hidden(A_137, B_138))), inference(resolution, [status(thm)], [c_395, c_38])).
% 9.46/3.82  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.46/3.82  tff(c_1236, plain, (![A_137, B_138]: (k5_xboole_0(k1_tarski(A_137), k1_tarski(A_137))=k4_xboole_0(k1_tarski(A_137), B_138) | ~r2_hidden(A_137, B_138))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_34])).
% 9.46/3.82  tff(c_1273, plain, (![A_137, B_138]: (k4_xboole_0(k1_tarski(A_137), k1_tarski(A_137))=k4_xboole_0(k1_tarski(A_137), B_138) | ~r2_hidden(A_137, B_138))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_1236])).
% 9.46/3.82  tff(c_18594, plain, (![A_487, B_488]: (k4_xboole_0(k1_tarski(A_487), B_488)=k1_xboole_0 | ~r2_hidden(A_487, B_488))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_1273])).
% 9.46/3.82  tff(c_40, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.46/3.82  tff(c_18788, plain, (![B_488, A_487]: (k2_xboole_0(B_488, k1_tarski(A_487))=k2_xboole_0(B_488, k1_xboole_0) | ~r2_hidden(A_487, B_488))), inference(superposition, [status(thm), theory('equality')], [c_18594, c_40])).
% 9.46/3.82  tff(c_18865, plain, (![B_489, A_490]: (k2_xboole_0(B_489, k1_tarski(A_490))=B_489 | ~r2_hidden(A_490, B_489))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18788])).
% 9.46/3.82  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.46/3.82  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.82  tff(c_62, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 9.46/3.82  tff(c_19171, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18865, c_62])).
% 9.46/3.82  tff(c_19280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_19171])).
% 9.46/3.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.46/3.82  
% 9.46/3.82  Inference rules
% 9.46/3.82  ----------------------
% 9.46/3.82  #Ref     : 0
% 9.46/3.82  #Sup     : 4810
% 9.46/3.82  #Fact    : 0
% 9.46/3.82  #Define  : 0
% 9.46/3.82  #Split   : 2
% 9.46/3.82  #Chain   : 0
% 9.46/3.82  #Close   : 0
% 9.46/3.82  
% 9.46/3.82  Ordering : KBO
% 9.46/3.82  
% 9.46/3.82  Simplification rules
% 9.46/3.82  ----------------------
% 9.46/3.82  #Subsume      : 1245
% 9.46/3.82  #Demod        : 6695
% 9.46/3.82  #Tautology    : 2531
% 9.46/3.82  #SimpNegUnit  : 76
% 9.46/3.82  #BackRed      : 34
% 9.46/3.82  
% 9.46/3.82  #Partial instantiations: 0
% 9.46/3.82  #Strategies tried      : 1
% 9.46/3.82  
% 9.46/3.82  Timing (in seconds)
% 9.46/3.82  ----------------------
% 9.46/3.82  Preprocessing        : 0.34
% 9.46/3.82  Parsing              : 0.18
% 9.46/3.82  CNF conversion       : 0.02
% 9.46/3.82  Main loop            : 2.73
% 9.46/3.82  Inferencing          : 0.58
% 9.46/3.82  Reduction            : 1.46
% 9.46/3.82  Demodulation         : 1.26
% 9.46/3.82  BG Simplification    : 0.06
% 9.46/3.82  Subsumption          : 0.51
% 9.46/3.82  Abstraction          : 0.11
% 9.46/3.82  MUC search           : 0.00
% 9.46/3.82  Cooper               : 0.00
% 9.46/3.82  Total                : 3.10
% 9.46/3.82  Index Insertion      : 0.00
% 9.46/3.82  Index Deletion       : 0.00
% 9.46/3.82  Index Matching       : 0.00
% 9.46/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
