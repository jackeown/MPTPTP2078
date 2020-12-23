%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:09 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.48s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  84 expanded)
%              Number of equality atoms :   12 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_108,plain,(
    ! [A_80,B_81] : k1_enumset1(A_80,A_80,B_81) = k2_tarski(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    ! [B_81,A_80] : r2_hidden(B_81,k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_60,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_137,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,k3_tarski(B_88))
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7346,plain,(
    ! [A_12861,A_12862,B_12863] :
      ( r1_tarski(A_12861,k2_xboole_0(A_12862,B_12863))
      | ~ r2_hidden(A_12861,k2_tarski(A_12862,B_12863)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_137])).

tff(c_7370,plain,(
    ! [B_81,A_80] : r1_tarski(B_81,k2_xboole_0(A_80,B_81)) ),
    inference(resolution,[status(thm)],[c_114,c_7346])).

tff(c_64,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_152,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_160,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_187,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_7424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7370,c_187])).

tff(c_7425,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_20,plain,(
    ! [E_14,B_9,C_10] : r2_hidden(E_14,k1_enumset1(E_14,B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [A_80,B_81] : r2_hidden(A_80,k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_20])).

tff(c_58,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,k3_tarski(B_63))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_165,plain,(
    ! [C_95,B_96,A_97] :
      ( r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7461,plain,(
    ! [A_13165,B_13166,B_13167] :
      ( r2_hidden(A_13165,B_13166)
      | ~ r1_tarski(k2_tarski(A_13165,B_13167),B_13166) ) ),
    inference(resolution,[status(thm)],[c_120,c_165])).

tff(c_8659,plain,(
    ! [A_13308,B_13309,B_13310] :
      ( r2_hidden(A_13308,k3_tarski(B_13309))
      | ~ r2_hidden(k2_tarski(A_13308,B_13310),B_13309) ) ),
    inference(resolution,[status(thm)],[c_58,c_7461])).

tff(c_8727,plain,(
    ! [A_13308,B_13310,B_81] : r2_hidden(A_13308,k3_tarski(k2_tarski(k2_tarski(A_13308,B_13310),B_81))) ),
    inference(resolution,[status(thm)],[c_120,c_8659])).

tff(c_8776,plain,(
    ! [A_13311,B_13312,B_13313] : r2_hidden(A_13311,k2_xboole_0(k2_tarski(A_13311,B_13312),B_13313)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8727])).

tff(c_8793,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7425,c_8776])).

tff(c_8806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.48/2.38  
% 6.48/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.48/2.39  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.48/2.39  
% 6.48/2.39  %Foreground sorts:
% 6.48/2.39  
% 6.48/2.39  
% 6.48/2.39  %Background operators:
% 6.48/2.39  
% 6.48/2.39  
% 6.48/2.39  %Foreground operators:
% 6.48/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.48/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.48/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.48/2.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.48/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.48/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.48/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.48/2.39  tff('#skF_5', type, '#skF_5': $i).
% 6.48/2.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.48/2.39  tff('#skF_6', type, '#skF_6': $i).
% 6.48/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.48/2.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.48/2.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.48/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.48/2.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.48/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.48/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.48/2.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.48/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.48/2.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.48/2.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.48/2.39  
% 6.48/2.40  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 6.48/2.40  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.48/2.40  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.48/2.40  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.48/2.40  tff(f_77, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.48/2.40  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.48/2.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.48/2.40  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.48/2.40  tff(c_108, plain, (![A_80, B_81]: (k1_enumset1(A_80, A_80, B_81)=k2_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.48/2.40  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.48/2.40  tff(c_114, plain, (![B_81, A_80]: (r2_hidden(B_81, k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 6.48/2.40  tff(c_60, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.48/2.40  tff(c_137, plain, (![A_87, B_88]: (r1_tarski(A_87, k3_tarski(B_88)) | ~r2_hidden(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.40  tff(c_7346, plain, (![A_12861, A_12862, B_12863]: (r1_tarski(A_12861, k2_xboole_0(A_12862, B_12863)) | ~r2_hidden(A_12861, k2_tarski(A_12862, B_12863)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_137])).
% 6.48/2.40  tff(c_7370, plain, (![B_81, A_80]: (r1_tarski(B_81, k2_xboole_0(A_80, B_81)))), inference(resolution, [status(thm)], [c_114, c_7346])).
% 6.48/2.40  tff(c_64, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.48/2.40  tff(c_152, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.48/2.40  tff(c_160, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_152])).
% 6.48/2.40  tff(c_187, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_160])).
% 6.48/2.40  tff(c_7424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7370, c_187])).
% 6.48/2.40  tff(c_7425, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_160])).
% 6.48/2.40  tff(c_20, plain, (![E_14, B_9, C_10]: (r2_hidden(E_14, k1_enumset1(E_14, B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.48/2.40  tff(c_120, plain, (![A_80, B_81]: (r2_hidden(A_80, k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_20])).
% 6.48/2.40  tff(c_58, plain, (![A_62, B_63]: (r1_tarski(A_62, k3_tarski(B_63)) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.40  tff(c_165, plain, (![C_95, B_96, A_97]: (r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.48/2.40  tff(c_7461, plain, (![A_13165, B_13166, B_13167]: (r2_hidden(A_13165, B_13166) | ~r1_tarski(k2_tarski(A_13165, B_13167), B_13166))), inference(resolution, [status(thm)], [c_120, c_165])).
% 6.48/2.40  tff(c_8659, plain, (![A_13308, B_13309, B_13310]: (r2_hidden(A_13308, k3_tarski(B_13309)) | ~r2_hidden(k2_tarski(A_13308, B_13310), B_13309))), inference(resolution, [status(thm)], [c_58, c_7461])).
% 6.48/2.40  tff(c_8727, plain, (![A_13308, B_13310, B_81]: (r2_hidden(A_13308, k3_tarski(k2_tarski(k2_tarski(A_13308, B_13310), B_81))))), inference(resolution, [status(thm)], [c_120, c_8659])).
% 6.48/2.40  tff(c_8776, plain, (![A_13311, B_13312, B_13313]: (r2_hidden(A_13311, k2_xboole_0(k2_tarski(A_13311, B_13312), B_13313)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8727])).
% 6.48/2.40  tff(c_8793, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7425, c_8776])).
% 6.48/2.40  tff(c_8806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_8793])).
% 6.48/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.48/2.40  
% 6.48/2.40  Inference rules
% 6.48/2.40  ----------------------
% 6.48/2.40  #Ref     : 0
% 6.48/2.40  #Sup     : 1152
% 6.48/2.40  #Fact    : 18
% 6.48/2.40  #Define  : 0
% 6.48/2.40  #Split   : 1
% 6.48/2.40  #Chain   : 0
% 6.48/2.40  #Close   : 0
% 6.48/2.40  
% 6.48/2.40  Ordering : KBO
% 6.48/2.40  
% 6.48/2.40  Simplification rules
% 6.48/2.40  ----------------------
% 6.48/2.40  #Subsume      : 138
% 6.48/2.40  #Demod        : 352
% 6.48/2.40  #Tautology    : 387
% 6.48/2.40  #SimpNegUnit  : 1
% 6.48/2.40  #BackRed      : 2
% 6.48/2.40  
% 6.48/2.40  #Partial instantiations: 4176
% 6.48/2.40  #Strategies tried      : 1
% 6.48/2.40  
% 6.48/2.40  Timing (in seconds)
% 6.48/2.40  ----------------------
% 6.75/2.40  Preprocessing        : 0.33
% 6.75/2.40  Parsing              : 0.17
% 6.75/2.40  CNF conversion       : 0.02
% 6.75/2.40  Main loop            : 1.31
% 6.75/2.40  Inferencing          : 0.70
% 6.75/2.40  Reduction            : 0.34
% 6.75/2.40  Demodulation         : 0.27
% 6.75/2.40  BG Simplification    : 0.05
% 6.75/2.40  Subsumption          : 0.16
% 6.75/2.40  Abstraction          : 0.06
% 6.75/2.40  MUC search           : 0.00
% 6.75/2.40  Cooper               : 0.00
% 6.75/2.40  Total                : 1.67
% 6.75/2.40  Index Insertion      : 0.00
% 6.75/2.40  Index Deletion       : 0.00
% 6.75/2.40  Index Matching       : 0.00
% 6.75/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
