%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:08 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 101 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_35,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_14])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_12,A_10,B_11] :
      ( k6_subset_1(k9_relat_1(C_12,A_10),k9_relat_1(C_12,B_11)) = k9_relat_1(C_12,k6_subset_1(A_10,B_11))
      | ~ v2_funct_1(C_12)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_215,plain,(
    ! [C_32,A_33,B_34] :
      ( k4_xboole_0(k9_relat_1(C_32,A_33),k9_relat_1(C_32,B_34)) = k9_relat_1(C_32,k4_xboole_0(A_33,B_34))
      | ~ v2_funct_1(C_32)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_20,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_224,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_51])).

tff(c_236,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_16,c_224])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [B_24,A_25] :
      ( k9_relat_1(B_24,A_25) != k1_xboole_0
      | ~ r1_tarski(A_25,k1_relat_1(B_24))
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_524,plain,(
    ! [B_64,A_65,C_66] :
      ( k9_relat_1(B_64,k4_xboole_0(A_65,C_66)) != k1_xboole_0
      | k4_xboole_0(A_65,C_66) = k1_xboole_0
      | ~ v1_relat_1(B_64)
      | ~ r1_tarski(A_65,k1_relat_1(B_64)) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_526,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_524])).

tff(c_543,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24,c_526])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.30  
% 2.13/1.30  %Foreground sorts:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Background operators:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Foreground operators:
% 2.13/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.30  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.13/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.30  
% 2.13/1.31  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.13/1.31  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 2.13/1.31  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.13/1.31  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 2.13/1.31  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.13/1.31  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 2.13/1.31  tff(c_35, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.31  tff(c_14, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.31  tff(c_39, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_35, c_14])).
% 2.13/1.31  tff(c_18, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.31  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.31  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.31  tff(c_16, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.31  tff(c_8, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.31  tff(c_12, plain, (![C_12, A_10, B_11]: (k6_subset_1(k9_relat_1(C_12, A_10), k9_relat_1(C_12, B_11))=k9_relat_1(C_12, k6_subset_1(A_10, B_11)) | ~v2_funct_1(C_12) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.31  tff(c_215, plain, (![C_32, A_33, B_34]: (k4_xboole_0(k9_relat_1(C_32, A_33), k9_relat_1(C_32, B_34))=k9_relat_1(C_32, k4_xboole_0(A_33, B_34)) | ~v2_funct_1(C_32) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_12])).
% 2.13/1.31  tff(c_20, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.31  tff(c_40, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.31  tff(c_51, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_40])).
% 2.13/1.31  tff(c_224, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_215, c_51])).
% 2.13/1.31  tff(c_236, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_16, c_224])).
% 2.13/1.31  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.31  tff(c_87, plain, (![B_24, A_25]: (k9_relat_1(B_24, A_25)!=k1_xboole_0 | ~r1_tarski(A_25, k1_relat_1(B_24)) | k1_xboole_0=A_25 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.31  tff(c_524, plain, (![B_64, A_65, C_66]: (k9_relat_1(B_64, k4_xboole_0(A_65, C_66))!=k1_xboole_0 | k4_xboole_0(A_65, C_66)=k1_xboole_0 | ~v1_relat_1(B_64) | ~r1_tarski(A_65, k1_relat_1(B_64)))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.13/1.31  tff(c_526, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_236, c_524])).
% 2.13/1.31  tff(c_543, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24, c_526])).
% 2.13/1.31  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_543])).
% 2.13/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  Inference rules
% 2.13/1.31  ----------------------
% 2.13/1.31  #Ref     : 0
% 2.13/1.31  #Sup     : 141
% 2.13/1.31  #Fact    : 0
% 2.13/1.31  #Define  : 0
% 2.13/1.31  #Split   : 3
% 2.13/1.31  #Chain   : 0
% 2.13/1.31  #Close   : 0
% 2.13/1.31  
% 2.13/1.31  Ordering : KBO
% 2.13/1.31  
% 2.13/1.31  Simplification rules
% 2.13/1.31  ----------------------
% 2.13/1.31  #Subsume      : 34
% 2.13/1.31  #Demod        : 40
% 2.13/1.31  #Tautology    : 54
% 2.13/1.31  #SimpNegUnit  : 2
% 2.13/1.31  #BackRed      : 1
% 2.13/1.31  
% 2.13/1.31  #Partial instantiations: 0
% 2.13/1.31  #Strategies tried      : 1
% 2.13/1.31  
% 2.13/1.31  Timing (in seconds)
% 2.13/1.31  ----------------------
% 2.13/1.32  Preprocessing        : 0.29
% 2.13/1.32  Parsing              : 0.16
% 2.13/1.32  CNF conversion       : 0.02
% 2.13/1.32  Main loop            : 0.27
% 2.13/1.32  Inferencing          : 0.10
% 2.13/1.32  Reduction            : 0.08
% 2.13/1.32  Demodulation         : 0.05
% 2.13/1.32  BG Simplification    : 0.01
% 2.13/1.32  Subsumption          : 0.06
% 2.13/1.32  Abstraction          : 0.01
% 2.13/1.32  MUC search           : 0.00
% 2.13/1.32  Cooper               : 0.00
% 2.13/1.32  Total                : 0.58
% 2.13/1.32  Index Insertion      : 0.00
% 2.13/1.32  Index Deletion       : 0.00
% 2.13/1.32  Index Matching       : 0.00
% 2.13/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
