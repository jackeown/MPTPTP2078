%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:50 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  88 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_35,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_20,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_20])).

tff(c_6,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k7_relat_1(B_9,A_8),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(A_16,C_17)
      | ~ r1_tarski(B_18,C_17)
      | ~ r1_tarski(A_16,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_20,B_21,A_22] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_tarski(A_20,k7_relat_1(B_21,A_22))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_57,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_74,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_74])).

tff(c_78,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_8,plain,(
    ! [A_10] :
      ( k7_relat_1(A_10,k1_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    ! [B_26,A_27,C_28] :
      ( r1_tarski(k7_relat_1(B_26,A_27),k7_relat_1(C_28,A_27))
      | ~ r1_tarski(B_26,C_28)
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [A_46,C_47] :
      ( r1_tarski(A_46,k7_relat_1(C_47,k1_relat_1(A_46)))
      | ~ r1_tarski(A_46,C_47)
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_77,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_225,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_212,c_77])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_78,c_225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n004.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 13:03:08 EST 2020
% 0.13/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.13  
% 1.81/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.13  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.81/1.13  
% 1.81/1.13  %Foreground sorts:
% 1.81/1.13  
% 1.81/1.13  
% 1.81/1.13  %Background operators:
% 1.81/1.13  
% 1.81/1.13  
% 1.81/1.13  %Foreground operators:
% 1.81/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.13  
% 1.81/1.14  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t219_relat_1)).
% 1.81/1.14  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.81/1.14  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.81/1.14  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.81/1.14  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 1.81/1.14  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.14  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.14  tff(c_14, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.14  tff(c_35, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_14])).
% 1.81/1.14  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.14  tff(c_36, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_35, c_20])).
% 1.81/1.14  tff(c_6, plain, (![B_9, A_8]: (r1_tarski(k7_relat_1(B_9, A_8), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.14  tff(c_37, plain, (![A_16, C_17, B_18]: (r1_tarski(A_16, C_17) | ~r1_tarski(B_18, C_17) | ~r1_tarski(A_16, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.14  tff(c_51, plain, (![A_20, B_21, A_22]: (r1_tarski(A_20, B_21) | ~r1_tarski(A_20, k7_relat_1(B_21, A_22)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_6, c_37])).
% 1.81/1.14  tff(c_57, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_51])).
% 1.81/1.14  tff(c_74, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_57])).
% 1.81/1.14  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_74])).
% 1.81/1.14  tff(c_78, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_14])).
% 1.81/1.14  tff(c_8, plain, (![A_10]: (k7_relat_1(A_10, k1_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.14  tff(c_91, plain, (![B_26, A_27, C_28]: (r1_tarski(k7_relat_1(B_26, A_27), k7_relat_1(C_28, A_27)) | ~r1_tarski(B_26, C_28) | ~v1_relat_1(C_28) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.14  tff(c_212, plain, (![A_46, C_47]: (r1_tarski(A_46, k7_relat_1(C_47, k1_relat_1(A_46))) | ~r1_tarski(A_46, C_47) | ~v1_relat_1(C_47) | ~v1_relat_1(A_46) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_8, c_91])).
% 1.81/1.14  tff(c_77, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_14])).
% 1.81/1.14  tff(c_225, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_212, c_77])).
% 1.81/1.14  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_78, c_225])).
% 1.81/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.14  
% 1.81/1.14  Inference rules
% 1.81/1.14  ----------------------
% 1.81/1.14  #Ref     : 0
% 1.81/1.14  #Sup     : 52
% 1.81/1.14  #Fact    : 0
% 1.81/1.14  #Define  : 0
% 1.81/1.14  #Split   : 1
% 1.81/1.14  #Chain   : 0
% 1.81/1.14  #Close   : 0
% 1.81/1.14  
% 1.81/1.14  Ordering : KBO
% 1.81/1.14  
% 1.81/1.14  Simplification rules
% 1.81/1.14  ----------------------
% 1.81/1.14  #Subsume      : 10
% 1.81/1.14  #Demod        : 7
% 1.81/1.14  #Tautology    : 11
% 1.81/1.14  #SimpNegUnit  : 3
% 1.81/1.15  #BackRed      : 0
% 1.81/1.15  
% 1.81/1.15  #Partial instantiations: 0
% 1.81/1.15  #Strategies tried      : 1
% 1.81/1.15  
% 1.81/1.15  Timing (in seconds)
% 1.81/1.15  ----------------------
% 1.81/1.15  Preprocessing        : 0.27
% 1.81/1.15  Parsing              : 0.15
% 1.81/1.15  CNF conversion       : 0.02
% 1.81/1.15  Main loop            : 0.19
% 1.81/1.15  Inferencing          : 0.08
% 1.81/1.15  Reduction            : 0.04
% 1.81/1.15  Demodulation         : 0.03
% 1.81/1.15  BG Simplification    : 0.01
% 1.81/1.15  Subsumption          : 0.05
% 1.81/1.15  Abstraction          : 0.01
% 1.81/1.15  MUC search           : 0.00
% 1.81/1.15  Cooper               : 0.00
% 1.81/1.15  Total                : 0.49
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
