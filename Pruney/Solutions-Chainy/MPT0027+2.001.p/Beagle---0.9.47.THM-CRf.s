%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:34 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  72 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & ! [D] :
              ( ( r1_tarski(D,B)
                & r1_tarski(D,C) )
             => r1_tarski(D,A) ) )
       => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    k3_xboole_0('#skF_2','#skF_3') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_19,plain,(
    k3_xboole_0('#skF_3','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [B_18,A_19] : k3_xboole_0(B_18,A_19) = k3_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [B_18,A_19] : r1_tarski(k3_xboole_0(B_18,A_19),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_120,plain,(
    ! [D_24] :
      ( r1_tarski(D_24,'#skF_1')
      | ~ r1_tarski(D_24,'#skF_3')
      | ~ r1_tarski(D_24,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [B_34] :
      ( r1_tarski(k3_xboole_0('#skF_2',B_34),'#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_34),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_254,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_250])).

tff(c_264,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_254])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_268,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_264,c_6])).

tff(c_342,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_268])).

tff(c_182,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,k3_xboole_0(B_28,C_29))
      | ~ r1_tarski(A_27,C_29)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_xboole_0(A_27,k3_xboole_0(B_28,C_29)) = k3_xboole_0(B_28,C_29)
      | ~ r1_tarski(A_27,C_29)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_182,c_6])).

tff(c_402,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_192])).

tff(c_409,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_402])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.32  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.02/1.32  
% 2.02/1.32  %Foreground sorts:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Background operators:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Foreground operators:
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.32  
% 2.27/1.33  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.27/1.33  tff(f_55, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.27/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.27/1.33  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.27/1.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.27/1.33  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.27/1.33  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.33  tff(c_12, plain, (k3_xboole_0('#skF_2', '#skF_3')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.33  tff(c_19, plain, (k3_xboole_0('#skF_3', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 2.27/1.33  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.33  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.33  tff(c_54, plain, (![B_18, A_19]: (k3_xboole_0(B_18, A_19)=k3_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.33  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.33  tff(c_69, plain, (![B_18, A_19]: (r1_tarski(k3_xboole_0(B_18, A_19), A_19))), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 2.27/1.33  tff(c_120, plain, (![D_24]: (r1_tarski(D_24, '#skF_1') | ~r1_tarski(D_24, '#skF_3') | ~r1_tarski(D_24, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.33  tff(c_250, plain, (![B_34]: (r1_tarski(k3_xboole_0('#skF_2', B_34), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_34), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_120])).
% 2.27/1.33  tff(c_254, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_69, c_250])).
% 2.27/1.33  tff(c_264, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_254])).
% 2.27/1.33  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.33  tff(c_268, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_264, c_6])).
% 2.27/1.33  tff(c_342, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2, c_268])).
% 2.27/1.33  tff(c_182, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, k3_xboole_0(B_28, C_29)) | ~r1_tarski(A_27, C_29) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.33  tff(c_192, plain, (![A_27, B_28, C_29]: (k2_xboole_0(A_27, k3_xboole_0(B_28, C_29))=k3_xboole_0(B_28, C_29) | ~r1_tarski(A_27, C_29) | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_182, c_6])).
% 2.27/1.33  tff(c_402, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_1' | ~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_342, c_192])).
% 2.27/1.33  tff(c_409, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_402])).
% 2.27/1.33  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_409])).
% 2.27/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.33  
% 2.27/1.33  Inference rules
% 2.27/1.33  ----------------------
% 2.27/1.33  #Ref     : 0
% 2.27/1.33  #Sup     : 98
% 2.27/1.33  #Fact    : 0
% 2.27/1.33  #Define  : 0
% 2.27/1.33  #Split   : 0
% 2.27/1.33  #Chain   : 0
% 2.27/1.34  #Close   : 0
% 2.27/1.34  
% 2.27/1.34  Ordering : KBO
% 2.27/1.34  
% 2.27/1.34  Simplification rules
% 2.27/1.34  ----------------------
% 2.27/1.34  #Subsume      : 2
% 2.27/1.34  #Demod        : 23
% 2.27/1.34  #Tautology    : 61
% 2.27/1.34  #SimpNegUnit  : 1
% 2.27/1.34  #BackRed      : 0
% 2.27/1.34  
% 2.27/1.34  #Partial instantiations: 0
% 2.27/1.34  #Strategies tried      : 1
% 2.27/1.34  
% 2.27/1.34  Timing (in seconds)
% 2.27/1.34  ----------------------
% 2.27/1.34  Preprocessing        : 0.28
% 2.27/1.34  Parsing              : 0.16
% 2.27/1.34  CNF conversion       : 0.02
% 2.27/1.34  Main loop            : 0.24
% 2.27/1.34  Inferencing          : 0.09
% 2.27/1.34  Reduction            : 0.09
% 2.27/1.34  Demodulation         : 0.08
% 2.27/1.34  BG Simplification    : 0.01
% 2.27/1.34  Subsumption          : 0.04
% 2.27/1.34  Abstraction          : 0.01
% 2.27/1.34  MUC search           : 0.00
% 2.27/1.34  Cooper               : 0.00
% 2.27/1.34  Total                : 0.56
% 2.27/1.34  Index Insertion      : 0.00
% 2.27/1.34  Index Deletion       : 0.00
% 2.27/1.34  Index Matching       : 0.00
% 2.27/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
