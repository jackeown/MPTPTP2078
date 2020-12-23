%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:47 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  92 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(c_20,plain,(
    ~ v4_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_51,plain,(
    ! [B_23,A_24] :
      ( k7_relat_1(B_23,A_24) = B_23
      | ~ v4_relat_1(B_23,A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_57,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_54])).

tff(c_92,plain,(
    ! [C_31,A_32,B_33] :
      ( r1_tarski(k7_relat_1(C_31,A_32),k7_relat_1(C_31,B_33))
      | ~ r1_tarski(A_32,B_33)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,(
    ! [B_33] :
      ( r1_tarski('#skF_3',k7_relat_1('#skF_3',B_33))
      | ~ r1_tarski('#skF_1',B_33)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_92])).

tff(c_103,plain,(
    ! [B_33] :
      ( r1_tarski('#skF_3',k7_relat_1('#skF_3',B_33))
      | ~ r1_tarski('#skF_1',B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [B_17,A_18] :
      ( B_17 = A_18
      | ~ r1_tarski(B_17,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ r1_tarski(B_52,k7_relat_1(B_52,A_53))
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_249,plain,(
    ! [B_33] :
      ( k7_relat_1('#skF_3',B_33) = '#skF_3'
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_1',B_33) ) ),
    inference(resolution,[status(thm)],[c_103,c_246])).

tff(c_263,plain,(
    ! [B_54] :
      ( k7_relat_1('#skF_3',B_54) = '#skF_3'
      | ~ r1_tarski('#skF_1',B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_249])).

tff(c_273,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_263])).

tff(c_83,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(k7_relat_1(C_28,A_29),A_29)
      | ~ v4_relat_1(C_28,B_30)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_29] :
      ( v4_relat_1(k7_relat_1('#skF_3',A_29),A_29)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_91,plain,(
    ! [A_29] : v4_relat_1(k7_relat_1('#skF_3',A_29),A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_87])).

tff(c_299,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_91])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.21  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
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
% 1.95/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.95/1.21  
% 1.95/1.22  tff(f_67, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 1.95/1.22  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.95/1.22  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 1.95/1.22  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.95/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.95/1.22  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 1.95/1.22  tff(c_20, plain, (~v4_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.22  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.22  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.22  tff(c_22, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.22  tff(c_51, plain, (![B_23, A_24]: (k7_relat_1(B_23, A_24)=B_23 | ~v4_relat_1(B_23, A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.22  tff(c_54, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_51])).
% 1.95/1.22  tff(c_57, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_54])).
% 1.95/1.22  tff(c_92, plain, (![C_31, A_32, B_33]: (r1_tarski(k7_relat_1(C_31, A_32), k7_relat_1(C_31, B_33)) | ~r1_tarski(A_32, B_33) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.22  tff(c_97, plain, (![B_33]: (r1_tarski('#skF_3', k7_relat_1('#skF_3', B_33)) | ~r1_tarski('#skF_1', B_33) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_92])).
% 1.95/1.22  tff(c_103, plain, (![B_33]: (r1_tarski('#skF_3', k7_relat_1('#skF_3', B_33)) | ~r1_tarski('#skF_1', B_33))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_97])).
% 1.95/1.22  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.22  tff(c_30, plain, (![B_17, A_18]: (B_17=A_18 | ~r1_tarski(B_17, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.22  tff(c_246, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~r1_tarski(B_52, k7_relat_1(B_52, A_53)) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_18, c_30])).
% 1.95/1.22  tff(c_249, plain, (![B_33]: (k7_relat_1('#skF_3', B_33)='#skF_3' | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', B_33))), inference(resolution, [status(thm)], [c_103, c_246])).
% 1.95/1.22  tff(c_263, plain, (![B_54]: (k7_relat_1('#skF_3', B_54)='#skF_3' | ~r1_tarski('#skF_1', B_54))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_249])).
% 1.95/1.22  tff(c_273, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_263])).
% 1.95/1.22  tff(c_83, plain, (![C_28, A_29, B_30]: (v4_relat_1(k7_relat_1(C_28, A_29), A_29) | ~v4_relat_1(C_28, B_30) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.22  tff(c_87, plain, (![A_29]: (v4_relat_1(k7_relat_1('#skF_3', A_29), A_29) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_83])).
% 1.95/1.22  tff(c_91, plain, (![A_29]: (v4_relat_1(k7_relat_1('#skF_3', A_29), A_29))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_87])).
% 1.95/1.22  tff(c_299, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_273, c_91])).
% 1.95/1.22  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_299])).
% 1.95/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  Inference rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Ref     : 0
% 1.95/1.22  #Sup     : 70
% 1.95/1.22  #Fact    : 0
% 1.95/1.22  #Define  : 0
% 1.95/1.22  #Split   : 1
% 1.95/1.22  #Chain   : 0
% 1.95/1.22  #Close   : 0
% 1.95/1.22  
% 1.95/1.22  Ordering : KBO
% 1.95/1.22  
% 1.95/1.22  Simplification rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Subsume      : 1
% 1.95/1.22  #Demod        : 63
% 1.95/1.22  #Tautology    : 37
% 1.95/1.22  #SimpNegUnit  : 1
% 1.95/1.22  #BackRed      : 0
% 1.95/1.22  
% 1.95/1.22  #Partial instantiations: 0
% 1.95/1.22  #Strategies tried      : 1
% 1.95/1.22  
% 1.95/1.22  Timing (in seconds)
% 1.95/1.22  ----------------------
% 1.95/1.22  Preprocessing        : 0.27
% 1.95/1.22  Parsing              : 0.15
% 1.95/1.22  CNF conversion       : 0.02
% 1.95/1.22  Main loop            : 0.20
% 1.95/1.22  Inferencing          : 0.08
% 1.95/1.22  Reduction            : 0.06
% 1.95/1.22  Demodulation         : 0.05
% 1.95/1.22  BG Simplification    : 0.01
% 1.95/1.22  Subsumption          : 0.04
% 1.95/1.22  Abstraction          : 0.01
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.50
% 1.95/1.22  Index Insertion      : 0.00
% 1.95/1.22  Index Deletion       : 0.00
% 1.95/1.22  Index Matching       : 0.00
% 1.95/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
