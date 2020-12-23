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
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 ( 124 expanded)
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

tff(f_62,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(c_12,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_53,plain,(
    ! [A_17,B_18] :
      ( k4_tarski(k1_mcart_1(A_17),k2_mcart_1(A_17)) = A_17
      | ~ r2_hidden(A_17,B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    ! [B_19,A_20] :
      ( k4_tarski(k1_mcart_1(B_19),k2_mcart_1(B_19)) = B_19
      | ~ v1_relat_1(A_20)
      | ~ m1_subset_1(B_19,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_63,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_57])).

tff(c_71,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_72,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_71])).

tff(c_14,plain,(
    k2_mcart_1('#skF_2') = k2_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    k1_mcart_1('#skF_2') = k1_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_61,plain,
    ( k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_67,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_2'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14,c_16,c_61])).

tff(c_68,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_67])).

tff(c_77,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.12  
% 1.68/1.12  %Foreground sorts:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Background operators:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Foreground operators:
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.68/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.12  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.68/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.12  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.68/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.12  
% 1.68/1.13  tff(f_62, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => (![B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (((k1_mcart_1(B) = k1_mcart_1(C)) & (k2_mcart_1(B) = k2_mcart_1(C))) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_mcart_1)).
% 1.68/1.13  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.68/1.13  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.68/1.13  tff(c_12, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.13  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.13  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.13  tff(c_18, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.13  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.13  tff(c_53, plain, (![A_17, B_18]: (k4_tarski(k1_mcart_1(A_17), k2_mcart_1(A_17))=A_17 | ~r2_hidden(A_17, B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.13  tff(c_57, plain, (![B_19, A_20]: (k4_tarski(k1_mcart_1(B_19), k2_mcart_1(B_19))=B_19 | ~v1_relat_1(A_20) | ~m1_subset_1(B_19, A_20) | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_4, c_53])).
% 1.68/1.13  tff(c_63, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_57])).
% 1.68/1.13  tff(c_71, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63])).
% 1.68/1.13  tff(c_72, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_24, c_71])).
% 1.68/1.13  tff(c_14, plain, (k2_mcart_1('#skF_2')=k2_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.13  tff(c_16, plain, (k1_mcart_1('#skF_2')=k1_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.13  tff(c_20, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.13  tff(c_61, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_57])).
% 1.68/1.13  tff(c_67, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_2' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14, c_16, c_61])).
% 1.68/1.13  tff(c_68, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_24, c_67])).
% 1.68/1.13  tff(c_77, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68])).
% 1.68/1.13  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_77])).
% 1.68/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  Inference rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Ref     : 0
% 1.68/1.13  #Sup     : 14
% 1.68/1.13  #Fact    : 0
% 1.68/1.13  #Define  : 0
% 1.68/1.13  #Split   : 0
% 1.68/1.13  #Chain   : 0
% 1.68/1.13  #Close   : 0
% 1.68/1.13  
% 1.68/1.13  Ordering : KBO
% 1.68/1.13  
% 1.68/1.13  Simplification rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Subsume      : 2
% 1.68/1.13  #Demod        : 5
% 1.68/1.13  #Tautology    : 9
% 1.68/1.13  #SimpNegUnit  : 3
% 1.68/1.13  #BackRed      : 1
% 1.68/1.13  
% 1.68/1.13  #Partial instantiations: 0
% 1.68/1.13  #Strategies tried      : 1
% 1.68/1.13  
% 1.68/1.13  Timing (in seconds)
% 1.68/1.13  ----------------------
% 1.68/1.13  Preprocessing        : 0.27
% 1.68/1.13  Parsing              : 0.15
% 1.68/1.13  CNF conversion       : 0.02
% 1.68/1.13  Main loop            : 0.10
% 1.68/1.13  Inferencing          : 0.04
% 1.68/1.13  Reduction            : 0.03
% 1.68/1.13  Demodulation         : 0.02
% 1.68/1.13  BG Simplification    : 0.01
% 1.68/1.13  Subsumption          : 0.02
% 1.68/1.13  Abstraction          : 0.00
% 1.68/1.13  MUC search           : 0.00
% 1.68/1.13  Cooper               : 0.00
% 1.68/1.13  Total                : 0.39
% 1.68/1.13  Index Insertion      : 0.00
% 1.68/1.13  Index Deletion       : 0.00
% 1.68/1.13  Index Matching       : 0.00
% 1.68/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
