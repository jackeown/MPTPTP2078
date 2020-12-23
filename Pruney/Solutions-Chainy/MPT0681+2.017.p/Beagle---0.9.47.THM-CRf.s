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
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   37 (  61 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_34])).

tff(c_6,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( k6_subset_1(k9_relat_1(C_7,A_5),k9_relat_1(C_7,B_6)) = k9_relat_1(C_7,k6_subset_1(A_5,B_6))
      | ~ v2_funct_1(C_7)
      | ~ v1_funct_1(C_7)
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [C_14,A_15,B_16] :
      ( k4_xboole_0(k9_relat_1(C_14,A_15),k9_relat_1(C_14,B_16)) = k9_relat_1(C_14,k4_xboole_0(A_15,B_16))
      | ~ v2_funct_1(C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8])).

tff(c_29,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_33,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) != k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_29,c_10])).

tff(c_53,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) != k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_33])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_12,c_42,c_53])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 13:16:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  %$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.67/1.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.67/1.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.67/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  
% 1.67/1.14  tff(f_50, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 1.67/1.14  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.67/1.14  tff(f_31, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.67/1.14  tff(f_39, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 1.67/1.14  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.14  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.14  tff(c_12, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.14  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.14  tff(c_34, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.14  tff(c_42, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_14, c_34])).
% 1.67/1.14  tff(c_6, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.14  tff(c_8, plain, (![C_7, A_5, B_6]: (k6_subset_1(k9_relat_1(C_7, A_5), k9_relat_1(C_7, B_6))=k9_relat_1(C_7, k6_subset_1(A_5, B_6)) | ~v2_funct_1(C_7) | ~v1_funct_1(C_7) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.14  tff(c_47, plain, (![C_14, A_15, B_16]: (k4_xboole_0(k9_relat_1(C_14, A_15), k9_relat_1(C_14, B_16))=k9_relat_1(C_14, k4_xboole_0(A_15, B_16)) | ~v2_funct_1(C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8])).
% 1.67/1.14  tff(c_29, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.14  tff(c_10, plain, (~r1_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.14  tff(c_33, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))!=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_29, c_10])).
% 1.67/1.14  tff(c_53, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))!=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_47, c_33])).
% 1.67/1.14  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_12, c_42, c_53])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 10
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 6
% 1.67/1.14  #Tautology    : 6
% 1.67/1.14  #SimpNegUnit  : 0
% 1.67/1.14  #BackRed      : 0
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.14  Preprocessing        : 0.28
% 1.67/1.14  Parsing              : 0.14
% 1.67/1.14  CNF conversion       : 0.02
% 1.67/1.14  Main loop            : 0.09
% 1.67/1.14  Inferencing          : 0.04
% 1.67/1.14  Reduction            : 0.03
% 1.67/1.14  Demodulation         : 0.02
% 1.67/1.14  BG Simplification    : 0.01
% 1.67/1.14  Subsumption          : 0.01
% 1.67/1.14  Abstraction          : 0.01
% 1.67/1.14  MUC search           : 0.00
% 1.67/1.14  Cooper               : 0.00
% 1.67/1.14  Total                : 0.39
% 1.67/1.14  Index Insertion      : 0.00
% 1.67/1.14  Index Deletion       : 0.00
% 1.67/1.14  Index Matching       : 0.00
% 1.67/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
