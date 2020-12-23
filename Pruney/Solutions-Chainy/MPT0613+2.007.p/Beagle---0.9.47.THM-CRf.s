%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:47 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   30 (  47 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  88 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(c_12,plain,(
    ~ v4_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_19,plain,(
    ! [B_10,A_11] :
      ( k7_relat_1(B_10,A_11) = B_10
      | ~ v4_relat_1(B_10,A_11)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_25,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_273,plain,(
    ! [C_52,A_53,B_54] :
      ( k7_relat_1(k7_relat_1(C_52,A_53),B_54) = k7_relat_1(C_52,A_53)
      | ~ r1_tarski(A_53,B_54)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_397,plain,(
    ! [B_54] :
      ( k7_relat_1('#skF_3',B_54) = k7_relat_1('#skF_3','#skF_1')
      | ~ r1_tarski('#skF_1',B_54)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_273])).

tff(c_466,plain,(
    ! [B_55] :
      ( k7_relat_1('#skF_3',B_55) = '#skF_3'
      | ~ r1_tarski('#skF_1',B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_25,c_397])).

tff(c_470,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_466])).

tff(c_40,plain,(
    ! [C_16,A_17,B_18] :
      ( v4_relat_1(k7_relat_1(C_16,A_17),A_17)
      | ~ v4_relat_1(C_16,B_18)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_17] :
      ( v4_relat_1(k7_relat_1('#skF_3',A_17),A_17)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_40])).

tff(c_45,plain,(
    ! [A_17] : v4_relat_1(k7_relat_1('#skF_3',A_17),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_503,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_45])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.08/1.27  
% 2.08/1.28  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.08/1.28  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.08/1.28  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.08/1.28  tff(f_35, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.08/1.28  tff(c_12, plain, (~v4_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.28  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.28  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.28  tff(c_14, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.28  tff(c_19, plain, (![B_10, A_11]: (k7_relat_1(B_10, A_11)=B_10 | ~v4_relat_1(B_10, A_11) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.28  tff(c_22, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_19])).
% 2.08/1.28  tff(c_25, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.08/1.28  tff(c_273, plain, (![C_52, A_53, B_54]: (k7_relat_1(k7_relat_1(C_52, A_53), B_54)=k7_relat_1(C_52, A_53) | ~r1_tarski(A_53, B_54) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.28  tff(c_397, plain, (![B_54]: (k7_relat_1('#skF_3', B_54)=k7_relat_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_1', B_54) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25, c_273])).
% 2.08/1.28  tff(c_466, plain, (![B_55]: (k7_relat_1('#skF_3', B_55)='#skF_3' | ~r1_tarski('#skF_1', B_55))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_25, c_397])).
% 2.08/1.28  tff(c_470, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_466])).
% 2.08/1.28  tff(c_40, plain, (![C_16, A_17, B_18]: (v4_relat_1(k7_relat_1(C_16, A_17), A_17) | ~v4_relat_1(C_16, B_18) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.28  tff(c_42, plain, (![A_17]: (v4_relat_1(k7_relat_1('#skF_3', A_17), A_17) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_40])).
% 2.08/1.28  tff(c_45, plain, (![A_17]: (v4_relat_1(k7_relat_1('#skF_3', A_17), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_42])).
% 2.08/1.28  tff(c_503, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_470, c_45])).
% 2.08/1.28  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_503])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 111
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 0
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 0
% 2.08/1.28  #Demod        : 118
% 2.08/1.28  #Tautology    : 78
% 2.08/1.28  #SimpNegUnit  : 1
% 2.08/1.28  #BackRed      : 0
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.25
% 2.08/1.28  Parsing              : 0.14
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.24
% 2.08/1.28  Inferencing          : 0.10
% 2.08/1.28  Reduction            : 0.09
% 2.08/1.28  Demodulation         : 0.07
% 2.08/1.28  BG Simplification    : 0.01
% 2.08/1.28  Subsumption          : 0.03
% 2.08/1.28  Abstraction          : 0.02
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.52
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
