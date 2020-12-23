%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:35 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 (  81 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_97,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(k1_tarski(A_28),B_29)
      | r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_109,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_127,plain,(
    ! [B_49,A_50] : r2_hidden(B_49,k2_tarski(A_50,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_26])).

tff(c_136,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_127])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_153,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_198,plain,(
    ! [B_60,A_61] : k3_tarski(k2_tarski(B_60,A_61)) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_153])).

tff(c_56,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_204,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_56])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_224,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k1_tarski('#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_60])).

tff(c_311,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_313,plain,
    ( k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_224,c_311])).

tff(c_324,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_313])).

tff(c_16,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_337,plain,(
    ! [A_8] :
      ( r1_xboole_0(A_8,k1_tarski('#skF_4'))
      | ~ r1_xboole_0(A_8,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_16])).

tff(c_355,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,B_80)
      | ~ r2_hidden(C_81,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_372,plain,(
    ! [C_84,A_85] :
      ( ~ r2_hidden(C_84,k1_tarski('#skF_4'))
      | ~ r2_hidden(C_84,A_85)
      | ~ r1_xboole_0(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_337,c_355])).

tff(c_385,plain,(
    ! [A_86] :
      ( ~ r2_hidden('#skF_4',A_86)
      | ~ r1_xboole_0(A_86,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_136,c_372])).

tff(c_411,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_385])).

tff(c_418,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_411])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:28:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.21/1.29  
% 2.21/1.29  %Foreground sorts:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Background operators:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Foreground operators:
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.21/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.21/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.29  
% 2.21/1.30  tff(f_102, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.21/1.30  tff(f_95, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.21/1.30  tff(f_86, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.30  tff(f_88, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.21/1.30  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.21/1.30  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.21/1.30  tff(f_69, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.21/1.30  tff(f_97, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.21/1.30  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.30  tff(f_65, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.21/1.30  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.21/1.30  tff(c_58, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.21/1.30  tff(c_54, plain, (![A_28, B_29]: (r1_xboole_0(k1_tarski(A_28), B_29) | r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.21/1.30  tff(c_48, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.30  tff(c_109, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.21/1.30  tff(c_26, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.21/1.30  tff(c_127, plain, (![B_49, A_50]: (r2_hidden(B_49, k2_tarski(A_50, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_26])).
% 2.21/1.30  tff(c_136, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_127])).
% 2.21/1.30  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.30  tff(c_22, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.30  tff(c_153, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.30  tff(c_198, plain, (![B_60, A_61]: (k3_tarski(k2_tarski(B_60, A_61))=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_22, c_153])).
% 2.21/1.30  tff(c_56, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.30  tff(c_204, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_198, c_56])).
% 2.21/1.30  tff(c_60, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.21/1.30  tff(c_224, plain, (r1_tarski(k2_xboole_0('#skF_5', k1_tarski('#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_60])).
% 2.21/1.30  tff(c_311, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.30  tff(c_313, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_224, c_311])).
% 2.21/1.30  tff(c_324, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_313])).
% 2.21/1.30  tff(c_16, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.30  tff(c_337, plain, (![A_8]: (r1_xboole_0(A_8, k1_tarski('#skF_4')) | ~r1_xboole_0(A_8, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_16])).
% 2.21/1.30  tff(c_355, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, B_80) | ~r2_hidden(C_81, A_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.30  tff(c_372, plain, (![C_84, A_85]: (~r2_hidden(C_84, k1_tarski('#skF_4')) | ~r2_hidden(C_84, A_85) | ~r1_xboole_0(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_337, c_355])).
% 2.21/1.30  tff(c_385, plain, (![A_86]: (~r2_hidden('#skF_4', A_86) | ~r1_xboole_0(A_86, '#skF_5'))), inference(resolution, [status(thm)], [c_136, c_372])).
% 2.21/1.30  tff(c_411, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_136, c_385])).
% 2.21/1.30  tff(c_418, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_411])).
% 2.21/1.30  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_418])).
% 2.21/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  Inference rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Ref     : 0
% 2.21/1.30  #Sup     : 86
% 2.21/1.30  #Fact    : 0
% 2.21/1.30  #Define  : 0
% 2.21/1.30  #Split   : 1
% 2.21/1.30  #Chain   : 0
% 2.21/1.30  #Close   : 0
% 2.21/1.30  
% 2.21/1.30  Ordering : KBO
% 2.21/1.30  
% 2.21/1.30  Simplification rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Subsume      : 5
% 2.21/1.30  #Demod        : 21
% 2.21/1.30  #Tautology    : 49
% 2.21/1.30  #SimpNegUnit  : 1
% 2.21/1.30  #BackRed      : 2
% 2.21/1.30  
% 2.21/1.30  #Partial instantiations: 0
% 2.21/1.30  #Strategies tried      : 1
% 2.21/1.30  
% 2.21/1.30  Timing (in seconds)
% 2.21/1.30  ----------------------
% 2.21/1.31  Preprocessing        : 0.31
% 2.21/1.31  Parsing              : 0.16
% 2.21/1.31  CNF conversion       : 0.02
% 2.21/1.31  Main loop            : 0.23
% 2.21/1.31  Inferencing          : 0.07
% 2.21/1.31  Reduction            : 0.08
% 2.21/1.31  Demodulation         : 0.06
% 2.21/1.31  BG Simplification    : 0.02
% 2.21/1.31  Subsumption          : 0.05
% 2.21/1.31  Abstraction          : 0.01
% 2.21/1.31  MUC search           : 0.00
% 2.21/1.31  Cooper               : 0.00
% 2.21/1.31  Total                : 0.58
% 2.21/1.31  Index Insertion      : 0.00
% 2.21/1.31  Index Deletion       : 0.00
% 2.21/1.31  Index Matching       : 0.00
% 2.21/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
