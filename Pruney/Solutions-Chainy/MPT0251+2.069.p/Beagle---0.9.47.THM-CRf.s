%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   65 (  83 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 106 expanded)
%              Number of equality atoms :   36 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

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

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_818,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden('#skF_2'(A_136,B_137,C_138),A_136)
      | r2_hidden('#skF_3'(A_136,B_137,C_138),C_138)
      | k4_xboole_0(A_136,B_137) = C_138 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),B_9)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_869,plain,(
    ! [A_136,C_138] :
      ( r2_hidden('#skF_3'(A_136,A_136,C_138),C_138)
      | k4_xboole_0(A_136,A_136) = C_138 ) ),
    inference(resolution,[status(thm)],[c_818,c_24])).

tff(c_915,plain,(
    ! [A_141,C_142] :
      ( r2_hidden('#skF_3'(A_141,A_141,C_142),C_142)
      | k4_xboole_0(A_141,A_141) = C_142 ) ),
    inference(resolution,[status(thm)],[c_818,c_24])).

tff(c_83,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_99,plain,(
    ! [A_43] : k2_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_36])).

tff(c_345,plain,(
    ! [A_76,B_77] : k2_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_352,plain,(
    ! [B_77] : k4_xboole_0(B_77,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_99])).

tff(c_368,plain,(
    ! [B_78] : k4_xboole_0(B_78,k1_xboole_0) = B_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_352])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_377,plain,(
    ! [D_13,B_78] :
      ( ~ r2_hidden(D_13,k1_xboole_0)
      | ~ r2_hidden(D_13,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_12])).

tff(c_999,plain,(
    ! [A_147,B_148] :
      ( ~ r2_hidden('#skF_3'(A_147,A_147,k1_xboole_0),B_148)
      | k4_xboole_0(A_147,A_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_915,c_377])).

tff(c_1017,plain,(
    ! [A_136] : k4_xboole_0(A_136,A_136) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_869,c_999])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_213,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_220,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_213])).

tff(c_315,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_327,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_315])).

tff(c_248,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_tarski(A_57),B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_542,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(k1_tarski(A_97),B_98) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_248,c_38])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_548,plain,(
    ! [A_97,B_98] :
      ( k5_xboole_0(k1_tarski(A_97),k1_tarski(A_97)) = k4_xboole_0(k1_tarski(A_97),B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_34])).

tff(c_561,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(k1_tarski(A_97),k1_tarski(A_97)) = k4_xboole_0(k1_tarski(A_97),B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_548])).

tff(c_2152,plain,(
    ! [A_211,B_212] :
      ( k4_xboole_0(k1_tarski(A_211),B_212) = k1_xboole_0
      | ~ r2_hidden(A_211,B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_561])).

tff(c_42,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2200,plain,(
    ! [B_212,A_211] :
      ( k2_xboole_0(B_212,k1_tarski(A_211)) = k2_xboole_0(B_212,k1_xboole_0)
      | ~ r2_hidden(A_211,B_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_42])).

tff(c_2236,plain,(
    ! [B_213,A_214] :
      ( k2_xboole_0(B_213,k1_tarski(A_214)) = B_213
      | ~ r2_hidden(A_214,B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2200])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_2256,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2236,c_62])).

tff(c_2283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:00:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.64  
% 3.66/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.64  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.66/1.64  
% 3.66/1.64  %Foreground sorts:
% 3.66/1.64  
% 3.66/1.64  
% 3.66/1.64  %Background operators:
% 3.66/1.64  
% 3.66/1.64  
% 3.66/1.64  %Foreground operators:
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.66/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.66/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.66/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.66/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.66/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.66/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.66/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.66/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.66/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.66/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.64  
% 3.66/1.65  tff(f_81, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.66/1.65  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.66/1.65  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.66/1.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.66/1.65  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.66/1.65  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.66/1.65  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.66/1.65  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.66/1.65  tff(f_74, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.66/1.65  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.66/1.65  tff(c_36, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.66/1.65  tff(c_818, plain, (![A_136, B_137, C_138]: (r2_hidden('#skF_2'(A_136, B_137, C_138), A_136) | r2_hidden('#skF_3'(A_136, B_137, C_138), C_138) | k4_xboole_0(A_136, B_137)=C_138)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.65  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), B_9) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.65  tff(c_869, plain, (![A_136, C_138]: (r2_hidden('#skF_3'(A_136, A_136, C_138), C_138) | k4_xboole_0(A_136, A_136)=C_138)), inference(resolution, [status(thm)], [c_818, c_24])).
% 3.66/1.65  tff(c_915, plain, (![A_141, C_142]: (r2_hidden('#skF_3'(A_141, A_141, C_142), C_142) | k4_xboole_0(A_141, A_141)=C_142)), inference(resolution, [status(thm)], [c_818, c_24])).
% 3.66/1.65  tff(c_83, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.66/1.65  tff(c_99, plain, (![A_43]: (k2_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_83, c_36])).
% 3.66/1.65  tff(c_345, plain, (![A_76, B_77]: (k2_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.66/1.65  tff(c_352, plain, (![B_77]: (k4_xboole_0(B_77, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_77))), inference(superposition, [status(thm), theory('equality')], [c_345, c_99])).
% 3.66/1.65  tff(c_368, plain, (![B_78]: (k4_xboole_0(B_78, k1_xboole_0)=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_352])).
% 3.66/1.65  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.65  tff(c_377, plain, (![D_13, B_78]: (~r2_hidden(D_13, k1_xboole_0) | ~r2_hidden(D_13, B_78))), inference(superposition, [status(thm), theory('equality')], [c_368, c_12])).
% 3.66/1.65  tff(c_999, plain, (![A_147, B_148]: (~r2_hidden('#skF_3'(A_147, A_147, k1_xboole_0), B_148) | k4_xboole_0(A_147, A_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_915, c_377])).
% 3.66/1.65  tff(c_1017, plain, (![A_136]: (k4_xboole_0(A_136, A_136)=k1_xboole_0)), inference(resolution, [status(thm)], [c_869, c_999])).
% 3.66/1.65  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.66/1.65  tff(c_213, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.66/1.65  tff(c_220, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_213])).
% 3.66/1.65  tff(c_315, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.66/1.65  tff(c_327, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_220, c_315])).
% 3.66/1.65  tff(c_248, plain, (![A_57, B_58]: (r1_tarski(k1_tarski(A_57), B_58) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.66/1.65  tff(c_38, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.66/1.65  tff(c_542, plain, (![A_97, B_98]: (k3_xboole_0(k1_tarski(A_97), B_98)=k1_tarski(A_97) | ~r2_hidden(A_97, B_98))), inference(resolution, [status(thm)], [c_248, c_38])).
% 3.66/1.65  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.66/1.65  tff(c_548, plain, (![A_97, B_98]: (k5_xboole_0(k1_tarski(A_97), k1_tarski(A_97))=k4_xboole_0(k1_tarski(A_97), B_98) | ~r2_hidden(A_97, B_98))), inference(superposition, [status(thm), theory('equality')], [c_542, c_34])).
% 3.66/1.65  tff(c_561, plain, (![A_97, B_98]: (k4_xboole_0(k1_tarski(A_97), k1_tarski(A_97))=k4_xboole_0(k1_tarski(A_97), B_98) | ~r2_hidden(A_97, B_98))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_548])).
% 3.66/1.65  tff(c_2152, plain, (![A_211, B_212]: (k4_xboole_0(k1_tarski(A_211), B_212)=k1_xboole_0 | ~r2_hidden(A_211, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_561])).
% 3.66/1.65  tff(c_42, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.66/1.65  tff(c_2200, plain, (![B_212, A_211]: (k2_xboole_0(B_212, k1_tarski(A_211))=k2_xboole_0(B_212, k1_xboole_0) | ~r2_hidden(A_211, B_212))), inference(superposition, [status(thm), theory('equality')], [c_2152, c_42])).
% 3.66/1.65  tff(c_2236, plain, (![B_213, A_214]: (k2_xboole_0(B_213, k1_tarski(A_214))=B_213 | ~r2_hidden(A_214, B_213))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2200])).
% 3.66/1.65  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.66/1.65  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.66/1.65  tff(c_62, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 3.66/1.65  tff(c_2256, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2236, c_62])).
% 3.66/1.65  tff(c_2283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2256])).
% 3.66/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.65  
% 3.66/1.65  Inference rules
% 3.66/1.65  ----------------------
% 3.66/1.65  #Ref     : 0
% 3.66/1.65  #Sup     : 497
% 3.66/1.65  #Fact    : 0
% 3.66/1.65  #Define  : 0
% 3.66/1.65  #Split   : 3
% 3.66/1.65  #Chain   : 0
% 3.66/1.65  #Close   : 0
% 3.66/1.66  
% 3.66/1.66  Ordering : KBO
% 3.66/1.66  
% 3.66/1.66  Simplification rules
% 3.66/1.66  ----------------------
% 3.66/1.66  #Subsume      : 123
% 3.66/1.66  #Demod        : 195
% 3.66/1.66  #Tautology    : 214
% 3.66/1.66  #SimpNegUnit  : 1
% 3.66/1.66  #BackRed      : 4
% 3.66/1.66  
% 3.66/1.66  #Partial instantiations: 0
% 3.66/1.66  #Strategies tried      : 1
% 3.66/1.66  
% 3.66/1.66  Timing (in seconds)
% 3.66/1.66  ----------------------
% 3.66/1.66  Preprocessing        : 0.33
% 3.66/1.66  Parsing              : 0.17
% 3.66/1.66  CNF conversion       : 0.02
% 3.66/1.66  Main loop            : 0.56
% 3.66/1.66  Inferencing          : 0.20
% 3.66/1.66  Reduction            : 0.17
% 3.66/1.66  Demodulation         : 0.12
% 3.66/1.66  BG Simplification    : 0.03
% 3.66/1.66  Subsumption          : 0.13
% 3.66/1.66  Abstraction          : 0.03
% 3.66/1.66  MUC search           : 0.00
% 3.66/1.66  Cooper               : 0.00
% 3.66/1.66  Total                : 0.92
% 3.66/1.66  Index Insertion      : 0.00
% 3.66/1.66  Index Deletion       : 0.00
% 3.66/1.66  Index Matching       : 0.00
% 3.66/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
