%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:50 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   49 (  51 expanded)
%              Number of leaves         :   31 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_226,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_xboole_0(k2_tarski(A_84,C_85),B_86)
      | r2_hidden(C_85,B_86)
      | r2_hidden(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_259,plain,(
    ! [A_95,C_96,B_97] :
      ( k3_xboole_0(k2_tarski(A_95,C_96),B_97) = k1_xboole_0
      | r2_hidden(C_96,B_97)
      | r2_hidden(A_95,B_97) ) ),
    inference(resolution,[status(thm)],[c_226,c_110])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_271,plain,(
    ! [B_97,A_95,C_96] :
      ( k4_xboole_0(B_97,k2_tarski(A_95,C_96)) = k5_xboole_0(B_97,k1_xboole_0)
      | r2_hidden(C_96,B_97)
      | r2_hidden(A_95,B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_120])).

tff(c_364,plain,(
    ! [B_107,A_108,C_109] :
      ( k4_xboole_0(B_107,k2_tarski(A_108,C_109)) = B_107
      | r2_hidden(C_109,B_107)
      | r2_hidden(A_108,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_271])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')),k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_37,plain,(
    k4_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_374,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_37])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:42:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.25  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.25  
% 2.09/1.25  %Foreground sorts:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Background operators:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Foreground operators:
% 2.09/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.25  
% 2.09/1.26  tff(f_90, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 2.09/1.26  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.09/1.26  tff(f_79, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.09/1.26  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.09/1.26  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.09/1.26  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.09/1.26  tff(f_53, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.09/1.26  tff(c_36, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.26  tff(c_34, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.26  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.26  tff(c_226, plain, (![A_84, C_85, B_86]: (r1_xboole_0(k2_tarski(A_84, C_85), B_86) | r2_hidden(C_85, B_86) | r2_hidden(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.09/1.26  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.26  tff(c_99, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.26  tff(c_110, plain, (![A_55, B_56]: (~r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_99])).
% 2.09/1.26  tff(c_259, plain, (![A_95, C_96, B_97]: (k3_xboole_0(k2_tarski(A_95, C_96), B_97)=k1_xboole_0 | r2_hidden(C_96, B_97) | r2_hidden(A_95, B_97))), inference(resolution, [status(thm)], [c_226, c_110])).
% 2.09/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.26  tff(c_111, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.26  tff(c_120, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_111])).
% 2.09/1.26  tff(c_271, plain, (![B_97, A_95, C_96]: (k4_xboole_0(B_97, k2_tarski(A_95, C_96))=k5_xboole_0(B_97, k1_xboole_0) | r2_hidden(C_96, B_97) | r2_hidden(A_95, B_97))), inference(superposition, [status(thm), theory('equality')], [c_259, c_120])).
% 2.09/1.26  tff(c_364, plain, (![B_107, A_108, C_109]: (k4_xboole_0(B_107, k2_tarski(A_108, C_109))=B_107 | r2_hidden(C_109, B_107) | r2_hidden(A_108, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_271])).
% 2.09/1.26  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.26  tff(c_32, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4')), k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.26  tff(c_37, plain, (k4_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 2.09/1.26  tff(c_374, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_364, c_37])).
% 2.09/1.26  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_374])).
% 2.09/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  Inference rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Ref     : 0
% 2.09/1.26  #Sup     : 85
% 2.09/1.26  #Fact    : 0
% 2.09/1.26  #Define  : 0
% 2.09/1.26  #Split   : 0
% 2.09/1.26  #Chain   : 0
% 2.09/1.26  #Close   : 0
% 2.09/1.26  
% 2.09/1.26  Ordering : KBO
% 2.09/1.26  
% 2.09/1.26  Simplification rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Subsume      : 19
% 2.09/1.26  #Demod        : 8
% 2.09/1.26  #Tautology    : 42
% 2.09/1.26  #SimpNegUnit  : 1
% 2.09/1.26  #BackRed      : 0
% 2.09/1.26  
% 2.09/1.26  #Partial instantiations: 0
% 2.09/1.26  #Strategies tried      : 1
% 2.09/1.26  
% 2.09/1.26  Timing (in seconds)
% 2.09/1.26  ----------------------
% 2.09/1.27  Preprocessing        : 0.30
% 2.09/1.27  Parsing              : 0.16
% 2.09/1.27  CNF conversion       : 0.02
% 2.09/1.27  Main loop            : 0.20
% 2.09/1.27  Inferencing          : 0.08
% 2.09/1.27  Reduction            : 0.07
% 2.09/1.27  Demodulation         : 0.05
% 2.09/1.27  BG Simplification    : 0.01
% 2.09/1.27  Subsumption          : 0.03
% 2.09/1.27  Abstraction          : 0.01
% 2.09/1.27  MUC search           : 0.00
% 2.09/1.27  Cooper               : 0.00
% 2.09/1.27  Total                : 0.53
% 2.09/1.27  Index Insertion      : 0.00
% 2.09/1.27  Index Deletion       : 0.00
% 2.09/1.27  Index Matching       : 0.00
% 2.09/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
