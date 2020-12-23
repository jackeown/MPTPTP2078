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
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  97 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

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

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_65,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_10),B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k7_relat_1(B_27,A_28),B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_30,B_31,A_32] :
      ( r1_tarski(A_30,B_31)
      | ~ r1_tarski(A_30,k7_relat_1(B_31,A_32))
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_105,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_124,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_105])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_124])).

tff(c_127,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [C_44,B_45,A_46] :
      ( r1_tarski(C_44,k7_relat_1(B_45,A_46))
      | ~ r1_tarski(C_44,B_45)
      | ~ r1_tarski(k1_relat_1(C_44),A_46)
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_369,plain,(
    ! [C_76,B_77] :
      ( r1_tarski(C_76,k7_relat_1(B_77,k1_relat_1(C_76)))
      | ~ r1_tarski(C_76,B_77)
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_128,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_389,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_369,c_128])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_127,c_389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.27  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.13/1.27  
% 2.13/1.27  %Foreground sorts:
% 2.13/1.27  
% 2.13/1.27  
% 2.13/1.27  %Background operators:
% 2.13/1.27  
% 2.13/1.27  
% 2.13/1.27  %Foreground operators:
% 2.13/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.13/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.13/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.27  
% 2.13/1.29  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 2.13/1.29  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.13/1.29  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 2.13/1.29  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.13/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.29  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 2.13/1.29  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.29  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.29  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.29  tff(c_46, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_28])).
% 2.13/1.29  tff(c_22, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.29  tff(c_64, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 2.13/1.29  tff(c_65, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.29  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k5_relat_1(k6_relat_1(A_10), B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.29  tff(c_81, plain, (![B_27, A_28]: (r1_tarski(k7_relat_1(B_27, A_28), B_27) | ~v1_relat_1(B_27) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_65, c_12])).
% 2.13/1.29  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.29  tff(c_95, plain, (![A_30, B_31, A_32]: (r1_tarski(A_30, B_31) | ~r1_tarski(A_30, k7_relat_1(B_31, A_32)) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_81, c_8])).
% 2.13/1.29  tff(c_105, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_95])).
% 2.13/1.29  tff(c_124, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_105])).
% 2.13/1.29  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_124])).
% 2.13/1.29  tff(c_127, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.13/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.29  tff(c_207, plain, (![C_44, B_45, A_46]: (r1_tarski(C_44, k7_relat_1(B_45, A_46)) | ~r1_tarski(C_44, B_45) | ~r1_tarski(k1_relat_1(C_44), A_46) | ~v1_relat_1(C_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.29  tff(c_369, plain, (![C_76, B_77]: (r1_tarski(C_76, k7_relat_1(B_77, k1_relat_1(C_76))) | ~r1_tarski(C_76, B_77) | ~v1_relat_1(C_76) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_6, c_207])).
% 2.13/1.29  tff(c_128, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_28])).
% 2.13/1.29  tff(c_389, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_369, c_128])).
% 2.13/1.29  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_127, c_389])).
% 2.13/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  Inference rules
% 2.13/1.29  ----------------------
% 2.13/1.29  #Ref     : 0
% 2.13/1.29  #Sup     : 90
% 2.13/1.29  #Fact    : 0
% 2.13/1.29  #Define  : 0
% 2.13/1.29  #Split   : 2
% 2.13/1.29  #Chain   : 0
% 2.13/1.29  #Close   : 0
% 2.13/1.29  
% 2.13/1.29  Ordering : KBO
% 2.13/1.29  
% 2.13/1.29  Simplification rules
% 2.13/1.29  ----------------------
% 2.13/1.29  #Subsume      : 18
% 2.13/1.29  #Demod        : 12
% 2.13/1.29  #Tautology    : 11
% 2.13/1.29  #SimpNegUnit  : 1
% 2.13/1.29  #BackRed      : 0
% 2.13/1.29  
% 2.13/1.29  #Partial instantiations: 0
% 2.13/1.29  #Strategies tried      : 1
% 2.13/1.29  
% 2.13/1.29  Timing (in seconds)
% 2.13/1.29  ----------------------
% 2.13/1.29  Preprocessing        : 0.27
% 2.13/1.29  Parsing              : 0.15
% 2.13/1.29  CNF conversion       : 0.02
% 2.13/1.29  Main loop            : 0.26
% 2.13/1.29  Inferencing          : 0.10
% 2.13/1.29  Reduction            : 0.06
% 2.13/1.29  Demodulation         : 0.05
% 2.13/1.29  BG Simplification    : 0.01
% 2.13/1.29  Subsumption          : 0.07
% 2.13/1.29  Abstraction          : 0.01
% 2.13/1.29  MUC search           : 0.00
% 2.13/1.29  Cooper               : 0.00
% 2.13/1.29  Total                : 0.56
% 2.13/1.29  Index Insertion      : 0.00
% 2.13/1.29  Index Deletion       : 0.00
% 2.13/1.29  Index Matching       : 0.00
% 2.13/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
