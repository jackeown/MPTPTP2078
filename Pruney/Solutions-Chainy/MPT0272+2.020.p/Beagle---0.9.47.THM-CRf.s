%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:08 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   47 (  48 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  52 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(k1_tarski(A_25),B_26)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,(
    ! [A_54,B_55] :
      ( ~ r1_xboole_0(A_54,B_55)
      | k3_xboole_0(A_54,B_55) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_129])).

tff(c_216,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(k1_tarski(A_70),B_71) = k1_xboole_0
      | r2_hidden(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [A_70,B_71] :
      ( k5_xboole_0(k1_tarski(A_70),k1_xboole_0) = k4_xboole_0(k1_tarski(A_70),B_71)
      | r2_hidden(A_70,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_14])).

tff(c_391,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(k1_tarski(A_95),B_96) = k1_tarski(A_95)
      | r2_hidden(A_95,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_417,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_34])).

tff(c_18,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_337,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(k2_tarski(A_80,B_81),C_82)
      | ~ r2_hidden(B_81,C_82)
      | ~ r2_hidden(A_80,C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_450,plain,(
    ! [A_101,C_102] :
      ( r1_tarski(k1_tarski(A_101),C_102)
      | ~ r2_hidden(A_101,C_102)
      | ~ r2_hidden(A_101,C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_337])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_460,plain,(
    ! [A_104,C_105] :
      ( k4_xboole_0(k1_tarski(A_104),C_105) = k1_xboole_0
      | ~ r2_hidden(A_104,C_105) ) ),
    inference(resolution,[status(thm)],[c_450,c_12])).

tff(c_36,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_479,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_36])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:46:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.33  
% 2.10/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.10/1.33  
% 2.10/1.33  %Foreground sorts:
% 2.10/1.33  
% 2.10/1.33  
% 2.10/1.33  %Background operators:
% 2.10/1.33  
% 2.10/1.33  
% 2.10/1.33  %Foreground operators:
% 2.10/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.10/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.10/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.33  
% 2.40/1.34  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.40/1.34  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.40/1.34  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.40/1.34  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.40/1.34  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.40/1.34  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.40/1.34  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.40/1.34  tff(f_76, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.40/1.34  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.40/1.34  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.40/1.34  tff(c_26, plain, (![A_25, B_26]: (r1_xboole_0(k1_tarski(A_25), B_26) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.40/1.34  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.34  tff(c_129, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.34  tff(c_141, plain, (![A_54, B_55]: (~r1_xboole_0(A_54, B_55) | k3_xboole_0(A_54, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_129])).
% 2.40/1.34  tff(c_216, plain, (![A_70, B_71]: (k3_xboole_0(k1_tarski(A_70), B_71)=k1_xboole_0 | r2_hidden(A_70, B_71))), inference(resolution, [status(thm)], [c_26, c_141])).
% 2.40/1.34  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.34  tff(c_228, plain, (![A_70, B_71]: (k5_xboole_0(k1_tarski(A_70), k1_xboole_0)=k4_xboole_0(k1_tarski(A_70), B_71) | r2_hidden(A_70, B_71))), inference(superposition, [status(thm), theory('equality')], [c_216, c_14])).
% 2.40/1.34  tff(c_391, plain, (![A_95, B_96]: (k4_xboole_0(k1_tarski(A_95), B_96)=k1_tarski(A_95) | r2_hidden(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_228])).
% 2.40/1.34  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.40/1.34  tff(c_417, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_391, c_34])).
% 2.40/1.34  tff(c_18, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.34  tff(c_337, plain, (![A_80, B_81, C_82]: (r1_tarski(k2_tarski(A_80, B_81), C_82) | ~r2_hidden(B_81, C_82) | ~r2_hidden(A_80, C_82))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.40/1.34  tff(c_450, plain, (![A_101, C_102]: (r1_tarski(k1_tarski(A_101), C_102) | ~r2_hidden(A_101, C_102) | ~r2_hidden(A_101, C_102))), inference(superposition, [status(thm), theory('equality')], [c_18, c_337])).
% 2.40/1.34  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.40/1.34  tff(c_460, plain, (![A_104, C_105]: (k4_xboole_0(k1_tarski(A_104), C_105)=k1_xboole_0 | ~r2_hidden(A_104, C_105))), inference(resolution, [status(thm)], [c_450, c_12])).
% 2.40/1.34  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.40/1.34  tff(c_479, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_460, c_36])).
% 2.40/1.34  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_417, c_479])).
% 2.40/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  Inference rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Ref     : 0
% 2.40/1.34  #Sup     : 105
% 2.40/1.34  #Fact    : 2
% 2.40/1.34  #Define  : 0
% 2.40/1.34  #Split   : 1
% 2.40/1.34  #Chain   : 0
% 2.40/1.34  #Close   : 0
% 2.40/1.34  
% 2.40/1.34  Ordering : KBO
% 2.40/1.34  
% 2.40/1.34  Simplification rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Subsume      : 24
% 2.40/1.34  #Demod        : 10
% 2.40/1.34  #Tautology    : 48
% 2.40/1.34  #SimpNegUnit  : 2
% 2.40/1.34  #BackRed      : 0
% 2.40/1.34  
% 2.40/1.34  #Partial instantiations: 0
% 2.40/1.34  #Strategies tried      : 1
% 2.40/1.34  
% 2.40/1.34  Timing (in seconds)
% 2.40/1.34  ----------------------
% 2.40/1.35  Preprocessing        : 0.32
% 2.40/1.35  Parsing              : 0.18
% 2.40/1.35  CNF conversion       : 0.02
% 2.40/1.35  Main loop            : 0.24
% 2.40/1.35  Inferencing          : 0.10
% 2.40/1.35  Reduction            : 0.07
% 2.40/1.35  Demodulation         : 0.05
% 2.40/1.35  BG Simplification    : 0.01
% 2.40/1.35  Subsumption          : 0.04
% 2.40/1.35  Abstraction          : 0.02
% 2.40/1.35  MUC search           : 0.00
% 2.40/1.35  Cooper               : 0.00
% 2.40/1.35  Total                : 0.59
% 2.40/1.35  Index Insertion      : 0.00
% 2.40/1.35  Index Deletion       : 0.00
% 2.40/1.35  Index Matching       : 0.00
% 2.40/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
