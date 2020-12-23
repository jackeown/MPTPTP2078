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
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 119 expanded)
%              Number of equality atoms :   26 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_69,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( ( r2_hidden(C,B)
            & r2_hidden(A,B)
            & k1_mcart_1(C) = k1_mcart_1(A)
            & k2_mcart_1(C) = k2_mcart_1(A) )
         => C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    k1_mcart_1('#skF_2') = k1_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    k2_mcart_1('#skF_2') = k2_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,(
    ! [C_19,A_20,B_21] :
      ( C_19 = A_20
      | k2_mcart_1(C_19) != k2_mcart_1(A_20)
      | k1_mcart_1(C_19) != k1_mcart_1(A_20)
      | ~ r2_hidden(A_20,B_21)
      | ~ r2_hidden(C_19,B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ! [A_20,B_21] :
      ( A_20 = '#skF_2'
      | k2_mcart_1(A_20) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_20) != k1_mcart_1('#skF_2')
      | ~ r2_hidden(A_20,B_21)
      | ~ r2_hidden('#skF_2',B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_65,plain,(
    ! [A_22,B_23] :
      ( A_22 = '#skF_2'
      | k2_mcart_1(A_22) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_22) != k1_mcart_1('#skF_3')
      | ~ r2_hidden(A_22,B_23)
      | ~ r2_hidden('#skF_2',B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_69,plain,(
    ! [B_24,A_25] :
      ( B_24 = '#skF_2'
      | k2_mcart_1(B_24) != k2_mcart_1('#skF_3')
      | k1_mcart_1(B_24) != k1_mcart_1('#skF_3')
      | ~ r2_hidden('#skF_2',A_25)
      | ~ v1_relat_1(A_25)
      | ~ m1_subset_1(B_24,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_74,plain,(
    ! [B_26,A_27] :
      ( B_26 = '#skF_2'
      | k2_mcart_1(B_26) != k2_mcart_1('#skF_3')
      | k1_mcart_1(B_26) != k1_mcart_1('#skF_3')
      | ~ v1_relat_1(A_27)
      | ~ m1_subset_1(B_26,A_27)
      | ~ m1_subset_1('#skF_2',A_27)
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_80,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_relat_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_89,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_80])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_12,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.66/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.66/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.13  
% 1.66/1.14  tff(f_69, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => (![B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (((k1_mcart_1(B) = k1_mcart_1(C)) & (k2_mcart_1(B) = k2_mcart_1(C))) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_mcart_1)).
% 1.66/1.14  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.66/1.14  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (![C]: ((((r2_hidden(C, B) & r2_hidden(A, B)) & (k1_mcart_1(C) = k1_mcart_1(A))) & (k2_mcart_1(C) = k2_mcart_1(A))) => (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_mcart_1)).
% 1.66/1.14  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.66/1.14  tff(c_12, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.66/1.14  tff(c_20, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.66/1.14  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.66/1.14  tff(c_18, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.66/1.14  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.14  tff(c_16, plain, (k1_mcart_1('#skF_2')=k1_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.66/1.14  tff(c_14, plain, (k2_mcart_1('#skF_2')=k2_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.66/1.14  tff(c_58, plain, (![C_19, A_20, B_21]: (C_19=A_20 | k2_mcart_1(C_19)!=k2_mcart_1(A_20) | k1_mcart_1(C_19)!=k1_mcart_1(A_20) | ~r2_hidden(A_20, B_21) | ~r2_hidden(C_19, B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.66/1.14  tff(c_60, plain, (![A_20, B_21]: (A_20='#skF_2' | k2_mcart_1(A_20)!=k2_mcart_1('#skF_3') | k1_mcart_1(A_20)!=k1_mcart_1('#skF_2') | ~r2_hidden(A_20, B_21) | ~r2_hidden('#skF_2', B_21) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_14, c_58])).
% 1.66/1.14  tff(c_65, plain, (![A_22, B_23]: (A_22='#skF_2' | k2_mcart_1(A_22)!=k2_mcart_1('#skF_3') | k1_mcart_1(A_22)!=k1_mcart_1('#skF_3') | ~r2_hidden(A_22, B_23) | ~r2_hidden('#skF_2', B_23) | ~v1_relat_1(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_60])).
% 1.66/1.14  tff(c_69, plain, (![B_24, A_25]: (B_24='#skF_2' | k2_mcart_1(B_24)!=k2_mcart_1('#skF_3') | k1_mcart_1(B_24)!=k1_mcart_1('#skF_3') | ~r2_hidden('#skF_2', A_25) | ~v1_relat_1(A_25) | ~m1_subset_1(B_24, A_25) | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_4, c_65])).
% 1.66/1.14  tff(c_74, plain, (![B_26, A_27]: (B_26='#skF_2' | k2_mcart_1(B_26)!=k2_mcart_1('#skF_3') | k1_mcart_1(B_26)!=k1_mcart_1('#skF_3') | ~v1_relat_1(A_27) | ~m1_subset_1(B_26, A_27) | ~m1_subset_1('#skF_2', A_27) | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_4, c_69])).
% 1.66/1.14  tff(c_80, plain, ('#skF_2'='#skF_3' | ~v1_relat_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_74])).
% 1.66/1.14  tff(c_89, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_80])).
% 1.66/1.14  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_12, c_89])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 1
% 1.66/1.14  #Sup     : 15
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 0
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 3
% 1.66/1.14  #Demod        : 8
% 1.66/1.14  #Tautology    : 9
% 1.66/1.14  #SimpNegUnit  : 2
% 1.66/1.14  #BackRed      : 0
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.66/1.14  Preprocessing        : 0.26
% 1.66/1.14  Parsing              : 0.14
% 1.66/1.14  CNF conversion       : 0.02
% 1.66/1.14  Main loop            : 0.12
% 1.66/1.14  Inferencing          : 0.05
% 1.66/1.14  Reduction            : 0.03
% 1.66/1.14  Demodulation         : 0.02
% 1.66/1.14  BG Simplification    : 0.01
% 1.66/1.14  Subsumption          : 0.03
% 1.66/1.14  Abstraction          : 0.01
% 1.66/1.14  MUC search           : 0.00
% 1.66/1.14  Cooper               : 0.00
% 1.66/1.14  Total                : 0.40
% 1.66/1.14  Index Insertion      : 0.00
% 1.66/1.14  Index Deletion       : 0.00
% 1.66/1.14  Index Matching       : 0.00
% 1.66/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
