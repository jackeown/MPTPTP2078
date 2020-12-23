%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:33 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   31 (  47 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_47,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_27])).

tff(c_6,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( k6_subset_1(k10_relat_1(C_7,A_5),k10_relat_1(C_7,B_6)) = k10_relat_1(C_7,k6_subset_1(A_5,B_6))
      | ~ v1_funct_1(C_7)
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [C_16,A_17,B_18] :
      ( k4_xboole_0(k10_relat_1(C_16,A_17),k10_relat_1(C_16,B_18)) = k10_relat_1(C_16,k4_xboole_0(A_17,B_18))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')) != k10_relat_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_10])).

tff(c_51,plain,
    ( k10_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k10_relat_1('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_43])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_31,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:11:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  %$ r1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.65/1.12  
% 1.65/1.12  %Foreground sorts:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Background operators:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Foreground operators:
% 1.65/1.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.12  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.65/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.65/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.12  
% 1.65/1.13  tff(f_47, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_funct_1)).
% 1.65/1.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.65/1.13  tff(f_31, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.65/1.13  tff(f_37, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 1.65/1.13  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.13  tff(c_14, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.13  tff(c_12, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.13  tff(c_27, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.13  tff(c_31, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_27])).
% 1.65/1.13  tff(c_6, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.13  tff(c_8, plain, (![C_7, A_5, B_6]: (k6_subset_1(k10_relat_1(C_7, A_5), k10_relat_1(C_7, B_6))=k10_relat_1(C_7, k6_subset_1(A_5, B_6)) | ~v1_funct_1(C_7) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.13  tff(c_45, plain, (![C_16, A_17, B_18]: (k4_xboole_0(k10_relat_1(C_16, A_17), k10_relat_1(C_16, B_18))=k10_relat_1(C_16, k4_xboole_0(A_17, B_18)) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8])).
% 1.65/1.13  tff(c_36, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.13  tff(c_10, plain, (~r1_xboole_0(k10_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.13  tff(c_43, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))!=k10_relat_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_10])).
% 1.65/1.13  tff(c_51, plain, (k10_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k10_relat_1('#skF_1', '#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_43])).
% 1.65/1.13  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_31, c_51])).
% 1.65/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  Inference rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Ref     : 0
% 1.65/1.13  #Sup     : 10
% 1.65/1.13  #Fact    : 0
% 1.65/1.13  #Define  : 0
% 1.65/1.13  #Split   : 0
% 1.65/1.13  #Chain   : 0
% 1.65/1.13  #Close   : 0
% 1.65/1.13  
% 1.65/1.13  Ordering : KBO
% 1.65/1.13  
% 1.65/1.13  Simplification rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Subsume      : 0
% 1.65/1.13  #Demod        : 5
% 1.65/1.13  #Tautology    : 6
% 1.65/1.13  #SimpNegUnit  : 0
% 1.65/1.13  #BackRed      : 0
% 1.65/1.13  
% 1.65/1.13  #Partial instantiations: 0
% 1.65/1.13  #Strategies tried      : 1
% 1.65/1.13  
% 1.65/1.13  Timing (in seconds)
% 1.65/1.13  ----------------------
% 1.65/1.13  Preprocessing        : 0.28
% 1.65/1.13  Parsing              : 0.15
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.09
% 1.65/1.13  Inferencing          : 0.04
% 1.65/1.13  Reduction            : 0.03
% 1.65/1.13  Demodulation         : 0.02
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.01
% 1.65/1.13  Abstraction          : 0.01
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.14  Cooper               : 0.00
% 1.65/1.14  Total                : 0.39
% 1.65/1.14  Index Insertion      : 0.00
% 1.65/1.14  Index Deletion       : 0.00
% 1.65/1.14  Index Matching       : 0.00
% 1.65/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
