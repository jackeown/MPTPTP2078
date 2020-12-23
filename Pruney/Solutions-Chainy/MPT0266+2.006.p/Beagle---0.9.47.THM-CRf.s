%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:27 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   64 (  86 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 (  83 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_60,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_54,axiom,(
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

tff(c_74,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_161,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ! [E_30,B_25,C_26] : r2_hidden(E_30,k1_enumset1(E_30,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_167,plain,(
    ! [A_75,B_76] : r2_hidden(A_75,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_42])).

tff(c_14,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden(A_5,B_6)
      | ~ r2_hidden(A_5,C_7)
      | r2_hidden(A_5,k5_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_402,plain,(
    ! [A_110,B_111,C_112] : k5_xboole_0(k5_xboole_0(A_110,B_111),C_112) = k5_xboole_0(A_110,k5_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_419,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k5_xboole_0(B_111,k5_xboole_0(A_110,B_111))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_30])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_549,plain,(
    ! [A_116,B_117] : k5_xboole_0(k5_xboole_0(A_116,B_117),k2_xboole_0(A_116,B_117)) = k3_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_598,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_19,A_19)) = k3_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_549])).

tff(c_606,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_598])).

tff(c_435,plain,(
    ! [A_19,C_112] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_112)) = k5_xboole_0(k1_xboole_0,C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_402])).

tff(c_741,plain,(
    ! [A_122,C_123] : k5_xboole_0(A_122,k5_xboole_0(A_122,C_123)) = C_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_435])).

tff(c_797,plain,(
    ! [B_111,A_110] : k5_xboole_0(B_111,k5_xboole_0(A_110,B_111)) = k5_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_741])).

tff(c_834,plain,(
    ! [B_124,A_125] : k5_xboole_0(B_124,k5_xboole_0(A_125,B_124)) = A_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_797])).

tff(c_740,plain,(
    ! [A_19,C_112] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_112)) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_435])).

tff(c_843,plain,(
    ! [B_124,A_125] : k5_xboole_0(B_124,A_125) = k5_xboole_0(A_125,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_740])).

tff(c_76,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_197,plain,(
    ! [A_81,B_82] : r1_xboole_0(k3_xboole_0(A_81,B_82),k5_xboole_0(A_81,B_82)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_200,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_197])).

tff(c_295,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,B_96)
      | ~ r2_hidden(C_97,A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_304,plain,(
    ! [C_97] :
      ( ~ r2_hidden(C_97,k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'))
      | ~ r2_hidden(C_97,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_200,c_295])).

tff(c_1475,plain,(
    ! [C_145] :
      ( ~ r2_hidden(C_145,k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')))
      | ~ r2_hidden(C_145,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_304])).

tff(c_1792,plain,(
    ! [A_157] :
      ( r2_hidden(A_157,'#skF_6')
      | ~ r2_hidden(A_157,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1475])).

tff(c_1808,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_167,c_1792])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.58  
% 3.28/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.59  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.28/1.59  
% 3.28/1.59  %Foreground sorts:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Background operators:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Foreground operators:
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.28/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.28/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.28/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.28/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.28/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.59  
% 3.60/1.60  tff(f_100, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 3.60/1.60  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.60/1.60  tff(f_81, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.60/1.60  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.60/1.60  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.60/1.60  tff(f_60, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.60/1.60  tff(f_62, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.60/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.60/1.60  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.60/1.60  tff(f_64, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.60/1.60  tff(f_56, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.60/1.60  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.60/1.60  tff(c_74, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.60/1.60  tff(c_161, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.60/1.60  tff(c_42, plain, (![E_30, B_25, C_26]: (r2_hidden(E_30, k1_enumset1(E_30, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.60/1.60  tff(c_167, plain, (![A_75, B_76]: (r2_hidden(A_75, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_42])).
% 3.60/1.60  tff(c_14, plain, (![A_5, B_6, C_7]: (r2_hidden(A_5, B_6) | ~r2_hidden(A_5, C_7) | r2_hidden(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.60/1.60  tff(c_26, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.60/1.60  tff(c_402, plain, (![A_110, B_111, C_112]: (k5_xboole_0(k5_xboole_0(A_110, B_111), C_112)=k5_xboole_0(A_110, k5_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.60/1.60  tff(c_30, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.60/1.60  tff(c_419, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k5_xboole_0(B_111, k5_xboole_0(A_110, B_111)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_402, c_30])).
% 3.60/1.60  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.60/1.60  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.60/1.60  tff(c_549, plain, (![A_116, B_117]: (k5_xboole_0(k5_xboole_0(A_116, B_117), k2_xboole_0(A_116, B_117))=k3_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.60/1.60  tff(c_598, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_19, A_19))=k3_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_30, c_549])).
% 3.60/1.60  tff(c_606, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_598])).
% 3.60/1.60  tff(c_435, plain, (![A_19, C_112]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_112))=k5_xboole_0(k1_xboole_0, C_112))), inference(superposition, [status(thm), theory('equality')], [c_30, c_402])).
% 3.60/1.60  tff(c_741, plain, (![A_122, C_123]: (k5_xboole_0(A_122, k5_xboole_0(A_122, C_123))=C_123)), inference(demodulation, [status(thm), theory('equality')], [c_606, c_435])).
% 3.60/1.60  tff(c_797, plain, (![B_111, A_110]: (k5_xboole_0(B_111, k5_xboole_0(A_110, B_111))=k5_xboole_0(A_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_419, c_741])).
% 3.60/1.60  tff(c_834, plain, (![B_124, A_125]: (k5_xboole_0(B_124, k5_xboole_0(A_125, B_124))=A_125)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_797])).
% 3.60/1.60  tff(c_740, plain, (![A_19, C_112]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_112))=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_606, c_435])).
% 3.60/1.60  tff(c_843, plain, (![B_124, A_125]: (k5_xboole_0(B_124, A_125)=k5_xboole_0(A_125, B_124))), inference(superposition, [status(thm), theory('equality')], [c_834, c_740])).
% 3.60/1.60  tff(c_76, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.60/1.60  tff(c_197, plain, (![A_81, B_82]: (r1_xboole_0(k3_xboole_0(A_81, B_82), k5_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.60/1.60  tff(c_200, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_197])).
% 3.60/1.60  tff(c_295, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, B_96) | ~r2_hidden(C_97, A_95))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.60/1.60  tff(c_304, plain, (![C_97]: (~r2_hidden(C_97, k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')) | ~r2_hidden(C_97, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_200, c_295])).
% 3.60/1.60  tff(c_1475, plain, (![C_145]: (~r2_hidden(C_145, k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))) | ~r2_hidden(C_145, k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_304])).
% 3.60/1.60  tff(c_1792, plain, (![A_157]: (r2_hidden(A_157, '#skF_6') | ~r2_hidden(A_157, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_14, c_1475])).
% 3.60/1.60  tff(c_1808, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_167, c_1792])).
% 3.60/1.60  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1808])).
% 3.60/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.60  
% 3.60/1.60  Inference rules
% 3.60/1.60  ----------------------
% 3.60/1.60  #Ref     : 0
% 3.60/1.60  #Sup     : 435
% 3.60/1.60  #Fact    : 0
% 3.60/1.60  #Define  : 0
% 3.60/1.60  #Split   : 0
% 3.60/1.60  #Chain   : 0
% 3.60/1.60  #Close   : 0
% 3.60/1.60  
% 3.60/1.60  Ordering : KBO
% 3.60/1.60  
% 3.60/1.60  Simplification rules
% 3.60/1.60  ----------------------
% 3.60/1.60  #Subsume      : 11
% 3.60/1.60  #Demod        : 228
% 3.60/1.60  #Tautology    : 256
% 3.60/1.60  #SimpNegUnit  : 1
% 3.60/1.60  #BackRed      : 6
% 3.60/1.60  
% 3.60/1.60  #Partial instantiations: 0
% 3.60/1.60  #Strategies tried      : 1
% 3.60/1.60  
% 3.60/1.60  Timing (in seconds)
% 3.60/1.60  ----------------------
% 3.60/1.60  Preprocessing        : 0.35
% 3.60/1.60  Parsing              : 0.19
% 3.60/1.60  CNF conversion       : 0.02
% 3.60/1.60  Main loop            : 0.46
% 3.60/1.60  Inferencing          : 0.15
% 3.60/1.60  Reduction            : 0.18
% 3.60/1.60  Demodulation         : 0.15
% 3.60/1.60  BG Simplification    : 0.03
% 3.60/1.60  Subsumption          : 0.08
% 3.60/1.60  Abstraction          : 0.03
% 3.60/1.60  MUC search           : 0.00
% 3.60/1.60  Cooper               : 0.00
% 3.60/1.60  Total                : 0.85
% 3.60/1.60  Index Insertion      : 0.00
% 3.60/1.60  Index Deletion       : 0.00
% 3.60/1.60  Index Matching       : 0.00
% 3.60/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
