%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:26 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   36 (  64 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_19])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_33,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_33])).

tff(c_46,plain,(
    ! [C_12,A_13,B_14] :
      ( k3_xboole_0(k9_relat_1(C_12,A_13),k9_relat_1(C_12,B_14)) = k9_relat_1(C_12,k3_xboole_0(A_13,B_14))
      | ~ v2_funct_1(C_12)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_10])).

tff(c_52,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_32])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_12,c_23,c_41,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  %$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.11  
% 1.65/1.11  tff(f_52, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 1.65/1.11  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 1.65/1.11  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.65/1.11  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 1.65/1.11  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.11  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.11  tff(c_12, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.11  tff(c_19, plain, (![A_7]: (k9_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.11  tff(c_23, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_19])).
% 1.65/1.11  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.11  tff(c_33, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.11  tff(c_41, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_33])).
% 1.65/1.11  tff(c_46, plain, (![C_12, A_13, B_14]: (k3_xboole_0(k9_relat_1(C_12, A_13), k9_relat_1(C_12, B_14))=k9_relat_1(C_12, k3_xboole_0(A_13, B_14)) | ~v2_funct_1(C_12) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.11  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.11  tff(c_10, plain, (~r1_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.11  tff(c_32, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_10])).
% 1.65/1.11  tff(c_52, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_32])).
% 1.65/1.11  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_12, c_23, c_41, c_52])).
% 1.65/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  Inference rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Ref     : 0
% 1.65/1.11  #Sup     : 13
% 1.65/1.11  #Fact    : 0
% 1.65/1.11  #Define  : 0
% 1.65/1.11  #Split   : 0
% 1.65/1.11  #Chain   : 0
% 1.65/1.11  #Close   : 0
% 1.65/1.11  
% 1.65/1.11  Ordering : KBO
% 1.65/1.11  
% 1.65/1.11  Simplification rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Subsume      : 0
% 1.65/1.11  #Demod        : 5
% 1.65/1.11  #Tautology    : 6
% 1.65/1.11  #SimpNegUnit  : 0
% 1.65/1.11  #BackRed      : 0
% 1.65/1.11  
% 1.65/1.11  #Partial instantiations: 0
% 1.65/1.11  #Strategies tried      : 1
% 1.65/1.11  
% 1.65/1.11  Timing (in seconds)
% 1.65/1.11  ----------------------
% 1.65/1.12  Preprocessing        : 0.26
% 1.65/1.12  Parsing              : 0.15
% 1.65/1.12  CNF conversion       : 0.02
% 1.65/1.12  Main loop            : 0.10
% 1.65/1.12  Inferencing          : 0.05
% 1.65/1.12  Reduction            : 0.02
% 1.65/1.12  Demodulation         : 0.02
% 1.65/1.12  BG Simplification    : 0.01
% 1.65/1.12  Subsumption          : 0.01
% 1.65/1.12  Abstraction          : 0.00
% 1.65/1.12  MUC search           : 0.00
% 1.65/1.12  Cooper               : 0.00
% 1.65/1.12  Total                : 0.38
% 1.65/1.12  Index Insertion      : 0.00
% 1.65/1.12  Index Deletion       : 0.00
% 1.65/1.12  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
