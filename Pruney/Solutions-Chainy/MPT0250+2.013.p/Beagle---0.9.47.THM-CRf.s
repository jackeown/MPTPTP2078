%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  53 expanded)
%              Number of leaves         :   30 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  48 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_70,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_121,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_139,plain,(
    ! [A_67,B_68] : r2_hidden(A_67,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_34])).

tff(c_148,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_139])).

tff(c_26,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_213,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_165])).

tff(c_68,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_219,plain,(
    ! [B_80,A_79] : k2_xboole_0(B_80,A_79) = k2_xboole_0(A_79,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_68])).

tff(c_72,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_239,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_72])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_316,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_239,c_20])).

tff(c_319,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_316])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_339,plain,(
    ! [D_87] :
      ( ~ r2_hidden(D_87,k1_tarski('#skF_5'))
      | r2_hidden(D_87,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_4])).

tff(c_343,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_148,c_339])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.19/1.29  
% 2.19/1.29  %Foreground sorts:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Background operators:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Foreground operators:
% 2.19/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.19/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.19/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.29  
% 2.19/1.30  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.19/1.30  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.30  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.19/1.30  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.19/1.30  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.19/1.30  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.19/1.30  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.19/1.30  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.19/1.30  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.19/1.30  tff(c_70, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.30  tff(c_54, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.19/1.30  tff(c_121, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.30  tff(c_34, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.30  tff(c_139, plain, (![A_67, B_68]: (r2_hidden(A_67, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_34])).
% 2.19/1.30  tff(c_148, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_139])).
% 2.19/1.30  tff(c_26, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.30  tff(c_28, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.30  tff(c_165, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.19/1.30  tff(c_213, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_28, c_165])).
% 2.19/1.30  tff(c_68, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.19/1.30  tff(c_219, plain, (![B_80, A_79]: (k2_xboole_0(B_80, A_79)=k2_xboole_0(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_213, c_68])).
% 2.19/1.30  tff(c_72, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.30  tff(c_239, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_72])).
% 2.19/1.30  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.30  tff(c_316, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_239, c_20])).
% 2.19/1.30  tff(c_319, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_316])).
% 2.19/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.30  tff(c_339, plain, (![D_87]: (~r2_hidden(D_87, k1_tarski('#skF_5')) | r2_hidden(D_87, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_4])).
% 2.19/1.30  tff(c_343, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_148, c_339])).
% 2.19/1.30  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_343])).
% 2.19/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  Inference rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Ref     : 0
% 2.19/1.30  #Sup     : 67
% 2.19/1.30  #Fact    : 0
% 2.19/1.30  #Define  : 0
% 2.19/1.30  #Split   : 0
% 2.19/1.30  #Chain   : 0
% 2.19/1.30  #Close   : 0
% 2.19/1.30  
% 2.19/1.30  Ordering : KBO
% 2.19/1.30  
% 2.19/1.30  Simplification rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Subsume      : 2
% 2.19/1.30  #Demod        : 20
% 2.19/1.30  #Tautology    : 47
% 2.19/1.30  #SimpNegUnit  : 1
% 2.19/1.30  #BackRed      : 2
% 2.19/1.30  
% 2.19/1.30  #Partial instantiations: 0
% 2.19/1.30  #Strategies tried      : 1
% 2.19/1.30  
% 2.19/1.30  Timing (in seconds)
% 2.19/1.30  ----------------------
% 2.19/1.30  Preprocessing        : 0.35
% 2.19/1.30  Parsing              : 0.17
% 2.19/1.30  CNF conversion       : 0.03
% 2.19/1.30  Main loop            : 0.21
% 2.19/1.30  Inferencing          : 0.06
% 2.19/1.30  Reduction            : 0.08
% 2.19/1.30  Demodulation         : 0.06
% 2.19/1.30  BG Simplification    : 0.02
% 2.19/1.30  Subsumption          : 0.04
% 2.19/1.30  Abstraction          : 0.02
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.58
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
