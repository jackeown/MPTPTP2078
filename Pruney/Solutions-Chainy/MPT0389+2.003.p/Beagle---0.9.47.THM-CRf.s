%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  66 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_3'(A_14,B_15),A_14)
      | r1_tarski(B_15,k1_setfam_1(A_14))
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_77,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_77])).

tff(c_98,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_92])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,'#skF_5')
      | ~ r2_hidden(D_6,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_setfam_1(B_13),A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_373,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,'#skF_3'(A_50,B_49))
      | r1_tarski(B_49,k1_setfam_1(A_50))
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_838,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k1_setfam_1(B_79),k1_setfam_1(A_80))
      | k1_xboole_0 = A_80
      | ~ r2_hidden('#skF_3'(A_80,k1_setfam_1(B_79)),B_79) ) ),
    inference(resolution,[status(thm)],[c_28,c_373])).

tff(c_869,plain,(
    ! [A_82] :
      ( r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1(A_82))
      | k1_xboole_0 = A_82
      | ~ r2_hidden('#skF_3'(A_82,k1_setfam_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_838])).

tff(c_873,plain,
    ( r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_869])).

tff(c_877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_36,c_34,c_873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.48  
% 2.86/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.49  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.86/1.49  
% 2.86/1.49  %Foreground sorts:
% 2.86/1.49  
% 2.86/1.49  
% 2.86/1.49  %Background operators:
% 2.86/1.49  
% 2.86/1.49  
% 2.86/1.49  %Foreground operators:
% 2.86/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.86/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.86/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.86/1.49  
% 2.86/1.50  tff(f_62, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.86/1.50  tff(f_55, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.86/1.50  tff(f_40, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.86/1.50  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.86/1.50  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.86/1.50  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.86/1.50  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.86/1.50  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.50  tff(c_34, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.50  tff(c_32, plain, (![A_14, B_15]: (r2_hidden('#skF_3'(A_14, B_15), A_14) | r1_tarski(B_15, k1_setfam_1(A_14)) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.50  tff(c_24, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.50  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.50  tff(c_48, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.50  tff(c_52, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_48])).
% 2.86/1.50  tff(c_77, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.86/1.50  tff(c_92, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_77])).
% 2.86/1.50  tff(c_98, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_92])).
% 2.86/1.50  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.50  tff(c_102, plain, (![D_6]: (r2_hidden(D_6, '#skF_5') | ~r2_hidden(D_6, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_4])).
% 2.86/1.50  tff(c_28, plain, (![B_13, A_12]: (r1_tarski(k1_setfam_1(B_13), A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.86/1.50  tff(c_373, plain, (![B_49, A_50]: (~r1_tarski(B_49, '#skF_3'(A_50, B_49)) | r1_tarski(B_49, k1_setfam_1(A_50)) | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.50  tff(c_838, plain, (![B_79, A_80]: (r1_tarski(k1_setfam_1(B_79), k1_setfam_1(A_80)) | k1_xboole_0=A_80 | ~r2_hidden('#skF_3'(A_80, k1_setfam_1(B_79)), B_79))), inference(resolution, [status(thm)], [c_28, c_373])).
% 2.86/1.50  tff(c_869, plain, (![A_82]: (r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1(A_82)) | k1_xboole_0=A_82 | ~r2_hidden('#skF_3'(A_82, k1_setfam_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_102, c_838])).
% 2.86/1.50  tff(c_873, plain, (r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_869])).
% 2.86/1.50  tff(c_877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_36, c_34, c_873])).
% 2.86/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.50  
% 2.86/1.50  Inference rules
% 2.86/1.50  ----------------------
% 2.86/1.50  #Ref     : 0
% 2.86/1.50  #Sup     : 205
% 2.86/1.50  #Fact    : 0
% 2.86/1.50  #Define  : 0
% 2.86/1.50  #Split   : 3
% 2.86/1.50  #Chain   : 0
% 2.86/1.50  #Close   : 0
% 2.86/1.50  
% 2.86/1.50  Ordering : KBO
% 2.86/1.50  
% 2.86/1.50  Simplification rules
% 2.86/1.50  ----------------------
% 2.86/1.50  #Subsume      : 25
% 2.86/1.50  #Demod        : 51
% 2.86/1.50  #Tautology    : 64
% 2.86/1.50  #SimpNegUnit  : 1
% 2.86/1.50  #BackRed      : 0
% 2.86/1.50  
% 2.86/1.50  #Partial instantiations: 0
% 2.86/1.50  #Strategies tried      : 1
% 2.86/1.50  
% 2.86/1.50  Timing (in seconds)
% 2.86/1.50  ----------------------
% 2.86/1.50  Preprocessing        : 0.29
% 2.86/1.50  Parsing              : 0.15
% 2.86/1.50  CNF conversion       : 0.02
% 2.86/1.50  Main loop            : 0.44
% 2.86/1.50  Inferencing          : 0.17
% 2.86/1.50  Reduction            : 0.12
% 2.86/1.50  Demodulation         : 0.09
% 2.86/1.50  BG Simplification    : 0.02
% 2.86/1.50  Subsumption          : 0.09
% 2.86/1.50  Abstraction          : 0.02
% 2.86/1.50  MUC search           : 0.00
% 2.86/1.50  Cooper               : 0.00
% 2.86/1.50  Total                : 0.76
% 2.86/1.50  Index Insertion      : 0.00
% 2.86/1.50  Index Deletion       : 0.00
% 2.86/1.50  Index Matching       : 0.00
% 2.86/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
