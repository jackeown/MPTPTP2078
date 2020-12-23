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
% DateTime   : Thu Dec  3 10:10:27 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 113 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( ( r2_hidden(C,B)
            & r2_hidden(A,B)
            & k1_mcart_1(C) = k1_mcart_1(A)
            & k2_mcart_1(C) = k2_mcart_1(A) )
         => C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_mcart_1)).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k1_mcart_1('#skF_2') = k1_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    k2_mcart_1('#skF_2') = k2_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    ! [C_13,A_14,B_15] :
      ( C_13 = A_14
      | k2_mcart_1(C_13) != k2_mcart_1(A_14)
      | k1_mcart_1(C_13) != k1_mcart_1(A_14)
      | ~ r2_hidden(A_14,B_15)
      | ~ r2_hidden(C_13,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_35,plain,(
    ! [A_14,B_15] :
      ( A_14 = '#skF_2'
      | k2_mcart_1(A_14) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_14) != k1_mcart_1('#skF_2')
      | ~ r2_hidden(A_14,B_15)
      | ~ r2_hidden('#skF_2',B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( A_16 = '#skF_2'
      | k2_mcart_1(A_16) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_16) != k1_mcart_1('#skF_3')
      | ~ r2_hidden(A_16,B_17)
      | ~ r2_hidden('#skF_2',B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_35])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( A_18 = '#skF_2'
      | k2_mcart_1(A_18) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_18) != k1_mcart_1('#skF_3')
      | ~ r2_hidden('#skF_2',B_19)
      | ~ v1_relat_1(B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_49,plain,(
    ! [A_20,B_21] :
      ( A_20 = '#skF_2'
      | k2_mcart_1(A_20) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_20) != k1_mcart_1('#skF_3')
      | ~ v1_relat_1(B_21)
      | ~ m1_subset_1(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1('#skF_2',B_21) ) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_53,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_49])).

tff(c_61,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_53])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_6,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.16  
% 1.64/1.16  %Foreground sorts:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Background operators:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Foreground operators:
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.64/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.64/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.16  
% 1.64/1.17  tff(f_62, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => (![B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (((k1_mcart_1(B) = k1_mcart_1(C)) & (k2_mcart_1(B) = k2_mcart_1(C))) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_mcart_1)).
% 1.64/1.17  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.64/1.17  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: ((((r2_hidden(C, B) & r2_hidden(A, B)) & (k1_mcart_1(C) = k1_mcart_1(A))) & (k2_mcart_1(C) = k2_mcart_1(A))) => (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_mcart_1)).
% 1.64/1.17  tff(c_18, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.64/1.17  tff(c_6, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.64/1.17  tff(c_14, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.64/1.17  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.64/1.17  tff(c_12, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.64/1.17  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.17  tff(c_10, plain, (k1_mcart_1('#skF_2')=k1_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.64/1.17  tff(c_8, plain, (k2_mcart_1('#skF_2')=k2_mcart_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.64/1.17  tff(c_33, plain, (![C_13, A_14, B_15]: (C_13=A_14 | k2_mcart_1(C_13)!=k2_mcart_1(A_14) | k1_mcart_1(C_13)!=k1_mcart_1(A_14) | ~r2_hidden(A_14, B_15) | ~r2_hidden(C_13, B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.17  tff(c_35, plain, (![A_14, B_15]: (A_14='#skF_2' | k2_mcart_1(A_14)!=k2_mcart_1('#skF_3') | k1_mcart_1(A_14)!=k1_mcart_1('#skF_2') | ~r2_hidden(A_14, B_15) | ~r2_hidden('#skF_2', B_15) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 1.64/1.17  tff(c_40, plain, (![A_16, B_17]: (A_16='#skF_2' | k2_mcart_1(A_16)!=k2_mcart_1('#skF_3') | k1_mcart_1(A_16)!=k1_mcart_1('#skF_3') | ~r2_hidden(A_16, B_17) | ~r2_hidden('#skF_2', B_17) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_35])).
% 1.64/1.17  tff(c_44, plain, (![A_18, B_19]: (A_18='#skF_2' | k2_mcart_1(A_18)!=k2_mcart_1('#skF_3') | k1_mcart_1(A_18)!=k1_mcart_1('#skF_3') | ~r2_hidden('#skF_2', B_19) | ~v1_relat_1(B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(resolution, [status(thm)], [c_2, c_40])).
% 1.64/1.17  tff(c_49, plain, (![A_20, B_21]: (A_20='#skF_2' | k2_mcart_1(A_20)!=k2_mcart_1('#skF_3') | k1_mcart_1(A_20)!=k1_mcart_1('#skF_3') | ~v1_relat_1(B_21) | ~m1_subset_1(A_20, B_21) | v1_xboole_0(B_21) | ~m1_subset_1('#skF_2', B_21))), inference(resolution, [status(thm)], [c_2, c_44])).
% 1.64/1.17  tff(c_53, plain, ('#skF_2'='#skF_3' | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_49])).
% 1.64/1.17  tff(c_61, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_53])).
% 1.64/1.17  tff(c_63, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_6, c_61])).
% 1.64/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  Inference rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Ref     : 1
% 1.64/1.17  #Sup     : 10
% 1.64/1.17  #Fact    : 0
% 1.64/1.17  #Define  : 0
% 1.64/1.17  #Split   : 0
% 1.64/1.17  #Chain   : 0
% 1.64/1.17  #Close   : 0
% 1.64/1.17  
% 1.64/1.17  Ordering : KBO
% 1.64/1.17  
% 1.64/1.17  Simplification rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Subsume      : 1
% 1.64/1.17  #Demod        : 8
% 1.64/1.17  #Tautology    : 6
% 1.64/1.17  #SimpNegUnit  : 2
% 1.64/1.17  #BackRed      : 0
% 1.64/1.17  
% 1.64/1.17  #Partial instantiations: 0
% 1.64/1.17  #Strategies tried      : 1
% 1.64/1.17  
% 1.64/1.17  Timing (in seconds)
% 1.64/1.17  ----------------------
% 1.64/1.17  Preprocessing        : 0.27
% 1.64/1.17  Parsing              : 0.15
% 1.64/1.17  CNF conversion       : 0.02
% 1.64/1.17  Main loop            : 0.12
% 1.64/1.17  Inferencing          : 0.05
% 1.64/1.17  Reduction            : 0.03
% 1.64/1.17  Demodulation         : 0.02
% 1.64/1.17  BG Simplification    : 0.01
% 1.64/1.17  Subsumption          : 0.02
% 1.64/1.17  Abstraction          : 0.01
% 1.64/1.17  MUC search           : 0.00
% 1.64/1.17  Cooper               : 0.00
% 1.64/1.17  Total                : 0.42
% 1.64/1.17  Index Insertion      : 0.00
% 1.64/1.17  Index Deletion       : 0.00
% 1.64/1.17  Index Matching       : 0.00
% 1.64/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
