%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 (  89 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( ( r1_tarski(k1_relat_1(C),A)
              & r1_tarski(C,B) )
           => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_24])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,C_19)
      | ~ r1_tarski(B_20,C_19)
      | ~ r1_tarski(A_18,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_22,B_23,A_24] :
      ( r1_tarski(A_22,B_23)
      | ~ r1_tarski(A_22,k7_relat_1(B_23,A_24))
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_66,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_80,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_66])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_80])).

tff(c_84,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [C_45,B_46,A_47] :
      ( r1_tarski(C_45,k7_relat_1(B_46,A_47))
      | ~ r1_tarski(C_45,B_46)
      | ~ r1_tarski(k1_relat_1(C_45),A_47)
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193,plain,(
    ! [C_48,B_49] :
      ( r1_tarski(C_48,k7_relat_1(B_49,k1_relat_1(C_48)))
      | ~ r1_tarski(C_48,B_49)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_184])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_216,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_193,c_83])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_84,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.95/1.21  
% 1.95/1.21  %Foreground sorts:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Background operators:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Foreground operators:
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.21  
% 1.95/1.22  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 1.95/1.22  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.95/1.22  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.95/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.95/1.22  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 1.95/1.22  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.22  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.22  tff(c_18, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.22  tff(c_38, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 1.95/1.22  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.22  tff(c_46, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_38, c_24])).
% 1.95/1.22  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.22  tff(c_39, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, C_19) | ~r1_tarski(B_20, C_19) | ~r1_tarski(A_18, B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.22  tff(c_60, plain, (![A_22, B_23, A_24]: (r1_tarski(A_22, B_23) | ~r1_tarski(A_22, k7_relat_1(B_23, A_24)) | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_12, c_39])).
% 1.95/1.22  tff(c_66, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_60])).
% 1.95/1.22  tff(c_80, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_66])).
% 1.95/1.22  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_80])).
% 1.95/1.22  tff(c_84, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 1.95/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.22  tff(c_184, plain, (![C_45, B_46, A_47]: (r1_tarski(C_45, k7_relat_1(B_46, A_47)) | ~r1_tarski(C_45, B_46) | ~r1_tarski(k1_relat_1(C_45), A_47) | ~v1_relat_1(C_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.22  tff(c_193, plain, (![C_48, B_49]: (r1_tarski(C_48, k7_relat_1(B_49, k1_relat_1(C_48))) | ~r1_tarski(C_48, B_49) | ~v1_relat_1(C_48) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_6, c_184])).
% 1.95/1.22  tff(c_83, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_18])).
% 1.95/1.22  tff(c_216, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_193, c_83])).
% 1.95/1.22  tff(c_233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_84, c_216])).
% 1.95/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  Inference rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Ref     : 0
% 1.95/1.22  #Sup     : 47
% 1.95/1.22  #Fact    : 0
% 1.95/1.22  #Define  : 0
% 1.95/1.22  #Split   : 2
% 1.95/1.22  #Chain   : 0
% 1.95/1.22  #Close   : 0
% 1.95/1.22  
% 1.95/1.22  Ordering : KBO
% 1.95/1.22  
% 1.95/1.22  Simplification rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Subsume      : 9
% 1.95/1.22  #Demod        : 11
% 1.95/1.22  #Tautology    : 8
% 1.95/1.22  #SimpNegUnit  : 3
% 1.95/1.22  #BackRed      : 0
% 1.95/1.22  
% 1.95/1.22  #Partial instantiations: 0
% 1.95/1.22  #Strategies tried      : 1
% 1.95/1.22  
% 1.95/1.22  Timing (in seconds)
% 1.95/1.22  ----------------------
% 1.95/1.22  Preprocessing        : 0.26
% 1.95/1.22  Parsing              : 0.14
% 1.95/1.22  CNF conversion       : 0.02
% 1.95/1.22  Main loop            : 0.20
% 1.95/1.22  Inferencing          : 0.07
% 1.95/1.22  Reduction            : 0.05
% 1.95/1.22  Demodulation         : 0.04
% 1.95/1.22  BG Simplification    : 0.01
% 1.95/1.22  Subsumption          : 0.05
% 1.95/1.22  Abstraction          : 0.01
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.48
% 1.95/1.22  Index Insertion      : 0.00
% 1.95/1.22  Index Deletion       : 0.00
% 1.95/1.23  Index Matching       : 0.00
% 1.95/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
