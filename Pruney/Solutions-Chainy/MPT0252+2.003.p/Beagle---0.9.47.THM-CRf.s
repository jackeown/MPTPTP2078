%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:01 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  60 expanded)
%              Number of equality atoms :   17 (  28 expanded)
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

tff(f_44,axiom,(
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

tff(c_210,plain,(
    ! [A_92,B_93] : k3_tarski(k2_tarski(A_92,B_93)) = k2_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_263,plain,(
    ! [A_102,B_103] : k3_tarski(k2_tarski(A_102,B_103)) = k2_xboole_0(B_103,A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_210])).

tff(c_72,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_269,plain,(
    ! [B_103,A_102] : k2_xboole_0(B_103,A_102) = k2_xboole_0(A_102,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_72])).

tff(c_76,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_286,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_76])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_369,plain,
    ( k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_286,c_14])).

tff(c_372,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_369])).

tff(c_225,plain,(
    ! [A_94,B_95] : k1_enumset1(A_94,A_94,B_95) = k2_tarski(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [E_37,A_31,B_32] : r2_hidden(E_37,k1_enumset1(A_31,B_32,E_37)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_234,plain,(
    ! [B_95,A_94] : r2_hidden(B_95,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_38])).

tff(c_522,plain,(
    ! [C_119,B_120,A_121] :
      ( r2_hidden(C_119,B_120)
      | ~ r2_hidden(C_119,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_541,plain,(
    ! [B_122,B_123,A_124] :
      ( r2_hidden(B_122,B_123)
      | ~ r1_tarski(k2_tarski(A_124,B_122),B_123) ) ),
    inference(resolution,[status(thm)],[c_234,c_522])).

tff(c_576,plain,(
    ! [B_126,A_127,B_128] : r2_hidden(B_126,k2_xboole_0(k2_tarski(A_127,B_126),B_128)) ),
    inference(resolution,[status(thm)],[c_28,c_541])).

tff(c_628,plain,(
    ! [B_132,A_133,B_134] : r2_hidden(B_132,k2_xboole_0(k2_tarski(B_132,A_133),B_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_576])).

tff(c_665,plain,(
    ! [B_138,B_139,A_140] : r2_hidden(B_138,k2_xboole_0(B_139,k2_tarski(B_138,A_140))) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_628])).

tff(c_670,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_665])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.52  
% 2.80/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.53  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.93/1.53  
% 2.93/1.53  %Foreground sorts:
% 2.93/1.53  
% 2.93/1.53  
% 2.93/1.53  %Background operators:
% 2.93/1.53  
% 2.93/1.53  
% 2.93/1.53  %Foreground operators:
% 2.93/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.93/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.93/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.93/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.93/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.93/1.53  
% 2.93/1.54  tff(f_94, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.93/1.54  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.93/1.54  tff(f_60, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.93/1.54  tff(f_89, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.93/1.54  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.54  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.93/1.54  tff(f_75, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.93/1.54  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.93/1.54  tff(c_74, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.93/1.54  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.93/1.54  tff(c_34, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.93/1.54  tff(c_210, plain, (![A_92, B_93]: (k3_tarski(k2_tarski(A_92, B_93))=k2_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.54  tff(c_263, plain, (![A_102, B_103]: (k3_tarski(k2_tarski(A_102, B_103))=k2_xboole_0(B_103, A_102))), inference(superposition, [status(thm), theory('equality')], [c_34, c_210])).
% 2.93/1.54  tff(c_72, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.54  tff(c_269, plain, (![B_103, A_102]: (k2_xboole_0(B_103, A_102)=k2_xboole_0(A_102, B_103))), inference(superposition, [status(thm), theory('equality')], [c_263, c_72])).
% 2.93/1.54  tff(c_76, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.93/1.54  tff(c_286, plain, (r1_tarski(k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_76])).
% 2.93/1.54  tff(c_14, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.93/1.54  tff(c_369, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_286, c_14])).
% 2.93/1.54  tff(c_372, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_369])).
% 2.93/1.54  tff(c_225, plain, (![A_94, B_95]: (k1_enumset1(A_94, A_94, B_95)=k2_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.93/1.54  tff(c_38, plain, (![E_37, A_31, B_32]: (r2_hidden(E_37, k1_enumset1(A_31, B_32, E_37)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.93/1.54  tff(c_234, plain, (![B_95, A_94]: (r2_hidden(B_95, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_225, c_38])).
% 2.93/1.54  tff(c_522, plain, (![C_119, B_120, A_121]: (r2_hidden(C_119, B_120) | ~r2_hidden(C_119, A_121) | ~r1_tarski(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.93/1.54  tff(c_541, plain, (![B_122, B_123, A_124]: (r2_hidden(B_122, B_123) | ~r1_tarski(k2_tarski(A_124, B_122), B_123))), inference(resolution, [status(thm)], [c_234, c_522])).
% 2.93/1.54  tff(c_576, plain, (![B_126, A_127, B_128]: (r2_hidden(B_126, k2_xboole_0(k2_tarski(A_127, B_126), B_128)))), inference(resolution, [status(thm)], [c_28, c_541])).
% 2.93/1.54  tff(c_628, plain, (![B_132, A_133, B_134]: (r2_hidden(B_132, k2_xboole_0(k2_tarski(B_132, A_133), B_134)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_576])).
% 2.93/1.54  tff(c_665, plain, (![B_138, B_139, A_140]: (r2_hidden(B_138, k2_xboole_0(B_139, k2_tarski(B_138, A_140))))), inference(superposition, [status(thm), theory('equality')], [c_269, c_628])).
% 2.93/1.54  tff(c_670, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_372, c_665])).
% 2.93/1.54  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_670])).
% 2.93/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.54  
% 2.93/1.54  Inference rules
% 2.93/1.54  ----------------------
% 2.93/1.54  #Ref     : 0
% 2.93/1.54  #Sup     : 152
% 2.93/1.54  #Fact    : 0
% 2.93/1.54  #Define  : 0
% 2.93/1.54  #Split   : 1
% 2.93/1.54  #Chain   : 0
% 2.93/1.54  #Close   : 0
% 2.93/1.54  
% 2.93/1.54  Ordering : KBO
% 2.93/1.54  
% 2.93/1.54  Simplification rules
% 2.93/1.54  ----------------------
% 2.93/1.54  #Subsume      : 1
% 2.93/1.54  #Demod        : 55
% 2.93/1.54  #Tautology    : 108
% 2.93/1.54  #SimpNegUnit  : 1
% 2.93/1.54  #BackRed      : 2
% 2.93/1.54  
% 2.93/1.54  #Partial instantiations: 0
% 2.93/1.54  #Strategies tried      : 1
% 2.93/1.54  
% 2.93/1.54  Timing (in seconds)
% 2.93/1.54  ----------------------
% 2.93/1.54  Preprocessing        : 0.39
% 2.93/1.54  Parsing              : 0.19
% 2.93/1.54  CNF conversion       : 0.03
% 2.93/1.54  Main loop            : 0.28
% 2.93/1.54  Inferencing          : 0.09
% 2.93/1.54  Reduction            : 0.10
% 2.93/1.54  Demodulation         : 0.08
% 2.93/1.54  BG Simplification    : 0.02
% 2.93/1.54  Subsumption          : 0.05
% 2.93/1.54  Abstraction          : 0.02
% 2.93/1.54  MUC search           : 0.00
% 2.93/1.54  Cooper               : 0.00
% 2.93/1.54  Total                : 0.70
% 2.93/1.54  Index Insertion      : 0.00
% 2.93/1.54  Index Deletion       : 0.00
% 2.93/1.54  Index Matching       : 0.00
% 2.93/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
