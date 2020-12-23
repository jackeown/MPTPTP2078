%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:12 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  77 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_62,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_64,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_65,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64])).

tff(c_100,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_xboole_0(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_100])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6])).

tff(c_48,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_146,plain,(
    ! [A_62,B_63] : r2_hidden(A_62,k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_28])).

tff(c_155,plain,(
    ! [A_66] : r2_hidden(A_66,k1_tarski(A_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_146])).

tff(c_158,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_155])).

tff(c_22,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_164,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_173,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_195,plain,(
    ! [A_75,C_76,B_77] :
      ( ~ r2_hidden(A_75,C_76)
      | ~ r2_hidden(A_75,B_77)
      | ~ r2_hidden(A_75,k5_xboole_0(B_77,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_248,plain,(
    ! [A_91,A_92] :
      ( ~ r2_hidden(A_91,A_92)
      | ~ r2_hidden(A_91,A_92)
      | ~ r2_hidden(A_91,k4_xboole_0(A_92,A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_195])).

tff(c_272,plain,(
    ! [A_97] :
      ( ~ r2_hidden(A_97,k1_xboole_0)
      | ~ r2_hidden(A_97,k1_xboole_0)
      | ~ r2_hidden(A_97,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_248])).

tff(c_274,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_158,c_272])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.28/1.26  
% 2.28/1.26  %Foreground sorts:
% 2.28/1.26  
% 2.28/1.26  
% 2.28/1.26  %Background operators:
% 2.28/1.26  
% 2.28/1.26  
% 2.28/1.26  %Foreground operators:
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.28/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.28/1.26  
% 2.28/1.28  tff(f_77, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.28/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.28/1.28  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.28/1.28  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.28/1.28  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.28/1.28  tff(f_57, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.28/1.28  tff(f_42, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.28/1.28  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.28/1.28  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.28/1.28  tff(c_62, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.28/1.28  tff(c_64, plain, (r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.28/1.28  tff(c_65, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64])).
% 2.28/1.28  tff(c_100, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.28  tff(c_104, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_100])).
% 2.28/1.28  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.28  tff(c_108, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_104, c_6])).
% 2.28/1.28  tff(c_48, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.28  tff(c_128, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.28/1.28  tff(c_28, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.28/1.28  tff(c_146, plain, (![A_62, B_63]: (r2_hidden(A_62, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_28])).
% 2.28/1.28  tff(c_155, plain, (![A_66]: (r2_hidden(A_66, k1_tarski(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_146])).
% 2.28/1.28  tff(c_158, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_155])).
% 2.28/1.28  tff(c_22, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.28  tff(c_164, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.28/1.28  tff(c_173, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_164])).
% 2.28/1.28  tff(c_195, plain, (![A_75, C_76, B_77]: (~r2_hidden(A_75, C_76) | ~r2_hidden(A_75, B_77) | ~r2_hidden(A_75, k5_xboole_0(B_77, C_76)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.28  tff(c_248, plain, (![A_91, A_92]: (~r2_hidden(A_91, A_92) | ~r2_hidden(A_91, A_92) | ~r2_hidden(A_91, k4_xboole_0(A_92, A_92)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_195])).
% 2.28/1.28  tff(c_272, plain, (![A_97]: (~r2_hidden(A_97, k1_xboole_0) | ~r2_hidden(A_97, k1_xboole_0) | ~r2_hidden(A_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_248])).
% 2.28/1.28  tff(c_274, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_272])).
% 2.28/1.28  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_274])).
% 2.28/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  Inference rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Ref     : 0
% 2.28/1.28  #Sup     : 52
% 2.28/1.28  #Fact    : 0
% 2.28/1.28  #Define  : 0
% 2.28/1.28  #Split   : 0
% 2.28/1.28  #Chain   : 0
% 2.28/1.28  #Close   : 0
% 2.28/1.28  
% 2.28/1.28  Ordering : KBO
% 2.28/1.28  
% 2.28/1.28  Simplification rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Subsume      : 0
% 2.28/1.28  #Demod        : 11
% 2.28/1.28  #Tautology    : 39
% 2.28/1.28  #SimpNegUnit  : 0
% 2.28/1.28  #BackRed      : 2
% 2.28/1.28  
% 2.28/1.28  #Partial instantiations: 0
% 2.28/1.28  #Strategies tried      : 1
% 2.28/1.28  
% 2.28/1.28  Timing (in seconds)
% 2.28/1.28  ----------------------
% 2.28/1.28  Preprocessing        : 0.34
% 2.28/1.28  Parsing              : 0.17
% 2.28/1.28  CNF conversion       : 0.03
% 2.28/1.28  Main loop            : 0.19
% 2.28/1.28  Inferencing          : 0.06
% 2.28/1.28  Reduction            : 0.06
% 2.28/1.28  Demodulation         : 0.05
% 2.28/1.28  BG Simplification    : 0.02
% 2.28/1.28  Subsumption          : 0.03
% 2.28/1.28  Abstraction          : 0.01
% 2.28/1.28  MUC search           : 0.00
% 2.28/1.28  Cooper               : 0.00
% 2.28/1.28  Total                : 0.56
% 2.28/1.28  Index Insertion      : 0.00
% 2.28/1.28  Index Deletion       : 0.00
% 2.28/1.28  Index Matching       : 0.00
% 2.28/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
