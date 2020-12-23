%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 ( 118 expanded)
%              Number of equality atoms :   16 (  43 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_relat_1(A) )
       => ! [B] :
            ( m1_subset_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ( k1_mcart_1(B) = k1_mcart_1(C)
                    & k2_mcart_1(B) = k2_mcart_1(C) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(c_6,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( k4_tarski(k1_mcart_1(A_11),k2_mcart_1(A_11)) = A_11
      | ~ r2_hidden(A_11,B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( k4_tarski(k1_mcart_1(A_13),k2_mcart_1(A_13)) = A_13
      | ~ v1_relat_1(B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_2,c_28])).

tff(c_36,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_32])).

tff(c_43,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_44,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_43])).

tff(c_8,plain,(
    k2_mcart_1('#skF_2') = k2_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    k1_mcart_1('#skF_2') = k1_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,
    ( k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_32])).

tff(c_39,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_2'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8,c_10,c_34])).

tff(c_40,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_39])).

tff(c_49,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.39  
% 2.07/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.40  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.40  
% 2.07/1.40  %Foreground sorts:
% 2.07/1.40  
% 2.07/1.40  
% 2.07/1.40  %Background operators:
% 2.07/1.40  
% 2.07/1.40  
% 2.07/1.40  %Foreground operators:
% 2.07/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.40  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.07/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.40  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.07/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.40  
% 2.07/1.42  tff(f_55, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => (![B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (((k1_mcart_1(B) = k1_mcart_1(C)) & (k2_mcart_1(B) = k2_mcart_1(C))) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_mcart_1)).
% 2.07/1.42  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.07/1.42  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.07/1.42  tff(c_6, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.42  tff(c_18, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.42  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.42  tff(c_12, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.42  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.42  tff(c_28, plain, (![A_11, B_12]: (k4_tarski(k1_mcart_1(A_11), k2_mcart_1(A_11))=A_11 | ~r2_hidden(A_11, B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.42  tff(c_32, plain, (![A_13, B_14]: (k4_tarski(k1_mcart_1(A_13), k2_mcart_1(A_13))=A_13 | ~v1_relat_1(B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(resolution, [status(thm)], [c_2, c_28])).
% 2.07/1.42  tff(c_36, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_32])).
% 2.07/1.42  tff(c_43, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 2.07/1.42  tff(c_44, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_18, c_43])).
% 2.07/1.42  tff(c_8, plain, (k2_mcart_1('#skF_2')=k2_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.42  tff(c_10, plain, (k1_mcart_1('#skF_2')=k1_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.42  tff(c_14, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.42  tff(c_34, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_32])).
% 2.07/1.42  tff(c_39, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_2' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8, c_10, c_34])).
% 2.07/1.42  tff(c_40, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_18, c_39])).
% 2.07/1.42  tff(c_49, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 2.07/1.42  tff(c_51, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_49])).
% 2.07/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.42  
% 2.07/1.42  Inference rules
% 2.07/1.42  ----------------------
% 2.07/1.42  #Ref     : 0
% 2.07/1.42  #Sup     : 9
% 2.07/1.42  #Fact    : 0
% 2.07/1.42  #Define  : 0
% 2.07/1.42  #Split   : 0
% 2.07/1.42  #Chain   : 0
% 2.07/1.42  #Close   : 0
% 2.07/1.42  
% 2.07/1.42  Ordering : KBO
% 2.07/1.42  
% 2.07/1.42  Simplification rules
% 2.07/1.42  ----------------------
% 2.07/1.42  #Subsume      : 0
% 2.07/1.42  #Demod        : 5
% 2.07/1.42  #Tautology    : 6
% 2.07/1.42  #SimpNegUnit  : 3
% 2.07/1.42  #BackRed      : 1
% 2.07/1.42  
% 2.07/1.42  #Partial instantiations: 0
% 2.07/1.42  #Strategies tried      : 1
% 2.07/1.42  
% 2.07/1.42  Timing (in seconds)
% 2.07/1.42  ----------------------
% 2.07/1.42  Preprocessing        : 0.44
% 2.07/1.42  Parsing              : 0.23
% 2.07/1.42  CNF conversion       : 0.03
% 2.07/1.42  Main loop            : 0.15
% 2.07/1.42  Inferencing          : 0.07
% 2.07/1.42  Reduction            : 0.05
% 2.07/1.42  Demodulation         : 0.04
% 2.07/1.42  BG Simplification    : 0.01
% 2.07/1.42  Subsumption          : 0.02
% 2.07/1.42  Abstraction          : 0.01
% 2.07/1.42  MUC search           : 0.00
% 2.07/1.42  Cooper               : 0.00
% 2.07/1.42  Total                : 0.64
% 2.07/1.42  Index Insertion      : 0.00
% 2.07/1.42  Index Deletion       : 0.00
% 2.07/1.42  Index Matching       : 0.00
% 2.07/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
