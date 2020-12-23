%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:12 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  52 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [A_63,B_64] : k1_enumset1(A_63,A_63,B_64) = k2_tarski(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,(
    ! [A_63,B_64] : r2_hidden(A_63,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_14])).

tff(c_59,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,k3_tarski(B_47))
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_749,plain,(
    ! [A_175,A_176,B_177] :
      ( r1_tarski(A_175,k2_xboole_0(A_176,B_177))
      | ~ r2_hidden(A_175,k2_tarski(A_176,B_177)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_48])).

tff(c_763,plain,(
    ! [A_178,B_179] : r1_tarski(A_178,k2_xboole_0(A_178,B_179)) ),
    inference(resolution,[status(thm)],[c_80,c_749])).

tff(c_54,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_232,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(A_82,C_83)
      | ~ r1_tarski(B_84,C_83)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_240,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_6')
      | ~ r1_tarski(A_82,k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_54,c_232])).

tff(c_790,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_763,c_240])).

tff(c_242,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [A_63,B_86,B_64] :
      ( r2_hidden(A_63,B_86)
      | ~ r1_tarski(k2_tarski(A_63,B_64),B_86) ) ),
    inference(resolution,[status(thm)],[c_80,c_242])).

tff(c_841,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_790,c_256])).

tff(c_848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.46  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.78/1.46  
% 2.78/1.46  %Foreground sorts:
% 2.78/1.46  
% 2.78/1.46  
% 2.78/1.46  %Background operators:
% 2.78/1.46  
% 2.78/1.46  
% 2.78/1.46  %Foreground operators:
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.78/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.78/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.78/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.46  
% 3.09/1.47  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.09/1.47  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.09/1.47  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.09/1.47  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.09/1.47  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.09/1.47  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.09/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.09/1.47  tff(c_52, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.47  tff(c_71, plain, (![A_63, B_64]: (k1_enumset1(A_63, A_63, B_64)=k2_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.09/1.47  tff(c_14, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.09/1.47  tff(c_80, plain, (![A_63, B_64]: (r2_hidden(A_63, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_14])).
% 3.09/1.47  tff(c_59, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.09/1.47  tff(c_48, plain, (![A_46, B_47]: (r1_tarski(A_46, k3_tarski(B_47)) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.09/1.47  tff(c_749, plain, (![A_175, A_176, B_177]: (r1_tarski(A_175, k2_xboole_0(A_176, B_177)) | ~r2_hidden(A_175, k2_tarski(A_176, B_177)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_48])).
% 3.09/1.47  tff(c_763, plain, (![A_178, B_179]: (r1_tarski(A_178, k2_xboole_0(A_178, B_179)))), inference(resolution, [status(thm)], [c_80, c_749])).
% 3.09/1.47  tff(c_54, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.47  tff(c_232, plain, (![A_82, C_83, B_84]: (r1_tarski(A_82, C_83) | ~r1_tarski(B_84, C_83) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.47  tff(c_240, plain, (![A_82]: (r1_tarski(A_82, '#skF_6') | ~r1_tarski(A_82, k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')))), inference(resolution, [status(thm)], [c_54, c_232])).
% 3.09/1.47  tff(c_790, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_763, c_240])).
% 3.09/1.47  tff(c_242, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.47  tff(c_256, plain, (![A_63, B_86, B_64]: (r2_hidden(A_63, B_86) | ~r1_tarski(k2_tarski(A_63, B_64), B_86))), inference(resolution, [status(thm)], [c_80, c_242])).
% 3.09/1.47  tff(c_841, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_790, c_256])).
% 3.09/1.47  tff(c_848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_841])).
% 3.09/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.47  
% 3.09/1.47  Inference rules
% 3.09/1.47  ----------------------
% 3.09/1.47  #Ref     : 0
% 3.09/1.47  #Sup     : 172
% 3.09/1.47  #Fact    : 0
% 3.09/1.47  #Define  : 0
% 3.09/1.47  #Split   : 0
% 3.09/1.47  #Chain   : 0
% 3.09/1.47  #Close   : 0
% 3.09/1.47  
% 3.09/1.47  Ordering : KBO
% 3.09/1.47  
% 3.09/1.47  Simplification rules
% 3.09/1.47  ----------------------
% 3.09/1.47  #Subsume      : 12
% 3.09/1.47  #Demod        : 68
% 3.09/1.47  #Tautology    : 82
% 3.09/1.47  #SimpNegUnit  : 1
% 3.09/1.47  #BackRed      : 0
% 3.09/1.47  
% 3.09/1.47  #Partial instantiations: 0
% 3.09/1.47  #Strategies tried      : 1
% 3.09/1.47  
% 3.09/1.47  Timing (in seconds)
% 3.09/1.47  ----------------------
% 3.09/1.47  Preprocessing        : 0.34
% 3.09/1.47  Parsing              : 0.17
% 3.09/1.47  CNF conversion       : 0.03
% 3.09/1.47  Main loop            : 0.36
% 3.09/1.47  Inferencing          : 0.13
% 3.09/1.47  Reduction            : 0.12
% 3.09/1.47  Demodulation         : 0.10
% 3.09/1.47  BG Simplification    : 0.02
% 3.09/1.47  Subsumption          : 0.07
% 3.09/1.47  Abstraction          : 0.02
% 3.09/1.47  MUC search           : 0.00
% 3.09/1.47  Cooper               : 0.00
% 3.09/1.47  Total                : 0.73
% 3.09/1.47  Index Insertion      : 0.00
% 3.09/1.47  Index Deletion       : 0.00
% 3.09/1.47  Index Matching       : 0.00
% 3.09/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
