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
% DateTime   : Thu Dec  3 09:51:01 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   32 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  57 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_89,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_74,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_321,plain,(
    ! [A_103,B_104] : k3_tarski(k2_tarski(A_103,B_104)) = k2_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_336,plain,(
    ! [B_105,A_106] : k3_tarski(k2_tarski(B_105,A_106)) = k2_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_321])).

tff(c_72,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_342,plain,(
    ! [B_105,A_106] : k2_xboole_0(B_105,A_106) = k2_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_72])).

tff(c_76,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_360,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_76])).

tff(c_590,plain,(
    ! [B_125,A_126] :
      ( B_125 = A_126
      | ~ r1_tarski(B_125,A_126)
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_594,plain,
    ( k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_360,c_590])).

tff(c_608,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_594])).

tff(c_361,plain,(
    ! [B_109,A_110] : k2_xboole_0(B_109,A_110) = k2_xboole_0(A_110,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_72])).

tff(c_394,plain,(
    ! [A_110,B_109] : r1_tarski(A_110,k2_xboole_0(B_109,A_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_28])).

tff(c_672,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_394])).

tff(c_263,plain,(
    ! [A_92,B_93] : k1_enumset1(A_92,A_92,B_93) = k2_tarski(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [E_37,A_31,C_33] : r2_hidden(E_37,k1_enumset1(A_31,E_37,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_272,plain,(
    ! [A_92,B_93] : r2_hidden(A_92,k2_tarski(A_92,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_40])).

tff(c_742,plain,(
    ! [C_129,B_130,A_131] :
      ( r2_hidden(C_129,B_130)
      | ~ r2_hidden(C_129,A_131)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_761,plain,(
    ! [A_132,B_133,B_134] :
      ( r2_hidden(A_132,B_133)
      | ~ r1_tarski(k2_tarski(A_132,B_134),B_133) ) ),
    inference(resolution,[status(thm)],[c_272,c_742])).

tff(c_764,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_672,c_761])).

tff(c_786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.49  
% 2.98/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.50  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.98/1.50  
% 2.98/1.50  %Foreground sorts:
% 2.98/1.50  
% 2.98/1.50  
% 2.98/1.50  %Background operators:
% 2.98/1.50  
% 2.98/1.50  
% 2.98/1.50  %Foreground operators:
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.98/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.98/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.98/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.98/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.50  
% 3.11/1.51  tff(f_94, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.11/1.51  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.11/1.51  tff(f_60, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.11/1.51  tff(f_89, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.11/1.51  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.11/1.51  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.11/1.51  tff(f_75, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.11/1.51  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.11/1.51  tff(c_74, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.11/1.51  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.11/1.51  tff(c_34, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.51  tff(c_321, plain, (![A_103, B_104]: (k3_tarski(k2_tarski(A_103, B_104))=k2_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.51  tff(c_336, plain, (![B_105, A_106]: (k3_tarski(k2_tarski(B_105, A_106))=k2_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_34, c_321])).
% 3.11/1.51  tff(c_72, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.51  tff(c_342, plain, (![B_105, A_106]: (k2_xboole_0(B_105, A_106)=k2_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_336, c_72])).
% 3.11/1.51  tff(c_76, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.11/1.51  tff(c_360, plain, (r1_tarski(k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_76])).
% 3.11/1.51  tff(c_590, plain, (![B_125, A_126]: (B_125=A_126 | ~r1_tarski(B_125, A_126) | ~r1_tarski(A_126, B_125))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.11/1.51  tff(c_594, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_360, c_590])).
% 3.11/1.51  tff(c_608, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_594])).
% 3.11/1.51  tff(c_361, plain, (![B_109, A_110]: (k2_xboole_0(B_109, A_110)=k2_xboole_0(A_110, B_109))), inference(superposition, [status(thm), theory('equality')], [c_336, c_72])).
% 3.11/1.51  tff(c_394, plain, (![A_110, B_109]: (r1_tarski(A_110, k2_xboole_0(B_109, A_110)))), inference(superposition, [status(thm), theory('equality')], [c_361, c_28])).
% 3.11/1.51  tff(c_672, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_608, c_394])).
% 3.11/1.51  tff(c_263, plain, (![A_92, B_93]: (k1_enumset1(A_92, A_92, B_93)=k2_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.11/1.51  tff(c_40, plain, (![E_37, A_31, C_33]: (r2_hidden(E_37, k1_enumset1(A_31, E_37, C_33)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.11/1.51  tff(c_272, plain, (![A_92, B_93]: (r2_hidden(A_92, k2_tarski(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_263, c_40])).
% 3.11/1.51  tff(c_742, plain, (![C_129, B_130, A_131]: (r2_hidden(C_129, B_130) | ~r2_hidden(C_129, A_131) | ~r1_tarski(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.11/1.51  tff(c_761, plain, (![A_132, B_133, B_134]: (r2_hidden(A_132, B_133) | ~r1_tarski(k2_tarski(A_132, B_134), B_133))), inference(resolution, [status(thm)], [c_272, c_742])).
% 3.11/1.51  tff(c_764, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_672, c_761])).
% 3.11/1.51  tff(c_786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_764])).
% 3.11/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.51  
% 3.11/1.51  Inference rules
% 3.11/1.51  ----------------------
% 3.11/1.51  #Ref     : 0
% 3.11/1.51  #Sup     : 173
% 3.11/1.51  #Fact    : 0
% 3.11/1.51  #Define  : 0
% 3.11/1.51  #Split   : 0
% 3.11/1.51  #Chain   : 0
% 3.11/1.51  #Close   : 0
% 3.11/1.51  
% 3.11/1.51  Ordering : KBO
% 3.11/1.51  
% 3.11/1.51  Simplification rules
% 3.11/1.51  ----------------------
% 3.11/1.51  #Subsume      : 1
% 3.11/1.51  #Demod        : 73
% 3.11/1.51  #Tautology    : 136
% 3.11/1.51  #SimpNegUnit  : 1
% 3.11/1.51  #BackRed      : 2
% 3.11/1.51  
% 3.11/1.51  #Partial instantiations: 0
% 3.11/1.51  #Strategies tried      : 1
% 3.11/1.51  
% 3.11/1.51  Timing (in seconds)
% 3.11/1.51  ----------------------
% 3.11/1.51  Preprocessing        : 0.35
% 3.11/1.51  Parsing              : 0.18
% 3.11/1.51  CNF conversion       : 0.03
% 3.11/1.52  Main loop            : 0.39
% 3.11/1.52  Inferencing          : 0.14
% 3.11/1.52  Reduction            : 0.15
% 3.11/1.52  Demodulation         : 0.11
% 3.11/1.52  BG Simplification    : 0.02
% 3.11/1.52  Subsumption          : 0.07
% 3.11/1.52  Abstraction          : 0.02
% 3.11/1.52  MUC search           : 0.00
% 3.11/1.52  Cooper               : 0.00
% 3.11/1.52  Total                : 0.78
% 3.11/1.52  Index Insertion      : 0.00
% 3.11/1.52  Index Deletion       : 0.00
% 3.11/1.52  Index Matching       : 0.00
% 3.11/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
