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
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   39 (  75 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 114 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r1_xboole_0(B,k1_relat_1(A))
           => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_16,plain,(
    k7_relat_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [B_21,A_22] :
      ( k3_xboole_0(k1_relat_1(B_21),A_22) = k1_relat_1(k7_relat_1(B_21,A_22))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21,plain,(
    ! [B_11,A_12] :
      ( r1_xboole_0(B_11,A_12)
      | ~ r1_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_21])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    k3_xboole_0(k1_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_81,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_55])).

tff(c_90,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_81])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k1_relat_1(B_9),A_8) = k1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),A_8)) = k3_xboole_0(k1_xboole_0,A_8)
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_14])).

tff(c_102,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_105,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_111,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_2')) != k1_xboole_0
    | k7_relat_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_12])).

tff(c_120,plain,(
    k7_relat_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_114])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:16:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.23  
% 1.75/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.23  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.75/1.23  
% 1.75/1.23  %Foreground sorts:
% 1.75/1.23  
% 1.75/1.23  
% 1.75/1.23  %Background operators:
% 1.75/1.23  
% 1.75/1.23  
% 1.75/1.23  %Foreground operators:
% 1.75/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.75/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.75/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.75/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.75/1.23  
% 1.89/1.24  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.89/1.24  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.89/1.24  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.89/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.89/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.89/1.24  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.89/1.24  tff(c_16, plain, (k7_relat_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.24  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.24  tff(c_75, plain, (![B_21, A_22]: (k3_xboole_0(k1_relat_1(B_21), A_22)=k1_relat_1(k7_relat_1(B_21, A_22)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.24  tff(c_18, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.24  tff(c_21, plain, (![B_11, A_12]: (r1_xboole_0(B_11, A_12) | ~r1_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.24  tff(c_24, plain, (r1_xboole_0(k1_relat_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_18, c_21])).
% 1.89/1.24  tff(c_44, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.24  tff(c_55, plain, (k3_xboole_0(k1_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_44])).
% 1.89/1.24  tff(c_81, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75, c_55])).
% 1.89/1.24  tff(c_90, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_81])).
% 1.89/1.24  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.24  tff(c_14, plain, (![B_9, A_8]: (k3_xboole_0(k1_relat_1(B_9), A_8)=k1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.24  tff(c_97, plain, (![A_8]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), A_8))=k3_xboole_0(k1_xboole_0, A_8) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_14])).
% 1.89/1.24  tff(c_102, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_97])).
% 1.89/1.24  tff(c_105, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_102])).
% 1.89/1.24  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_105])).
% 1.89/1.24  tff(c_111, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_97])).
% 1.89/1.24  tff(c_12, plain, (![A_7]: (k1_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.24  tff(c_114, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k1_xboole_0 | k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_12])).
% 1.89/1.24  tff(c_120, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_90, c_114])).
% 1.89/1.24  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_120])).
% 1.89/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.24  
% 1.89/1.24  Inference rules
% 1.89/1.24  ----------------------
% 1.89/1.24  #Ref     : 0
% 1.89/1.24  #Sup     : 24
% 1.89/1.24  #Fact    : 0
% 1.89/1.24  #Define  : 0
% 1.89/1.24  #Split   : 3
% 1.89/1.24  #Chain   : 0
% 1.89/1.24  #Close   : 0
% 1.89/1.24  
% 1.89/1.24  Ordering : KBO
% 1.89/1.24  
% 1.89/1.24  Simplification rules
% 1.89/1.24  ----------------------
% 1.89/1.24  #Subsume      : 0
% 1.89/1.24  #Demod        : 6
% 1.89/1.24  #Tautology    : 11
% 1.89/1.24  #SimpNegUnit  : 1
% 1.89/1.24  #BackRed      : 0
% 1.89/1.24  
% 1.89/1.24  #Partial instantiations: 0
% 1.89/1.24  #Strategies tried      : 1
% 1.89/1.24  
% 1.89/1.24  Timing (in seconds)
% 1.89/1.24  ----------------------
% 1.89/1.25  Preprocessing        : 0.26
% 1.89/1.25  Parsing              : 0.14
% 1.89/1.25  CNF conversion       : 0.02
% 1.89/1.25  Main loop            : 0.17
% 1.89/1.25  Inferencing          : 0.06
% 1.89/1.25  Reduction            : 0.05
% 1.89/1.25  Demodulation         : 0.04
% 1.89/1.25  BG Simplification    : 0.01
% 1.89/1.25  Subsumption          : 0.03
% 1.89/1.25  Abstraction          : 0.01
% 1.89/1.25  MUC search           : 0.00
% 1.89/1.25  Cooper               : 0.00
% 1.89/1.25  Total                : 0.46
% 1.89/1.25  Index Insertion      : 0.00
% 1.89/1.25  Index Deletion       : 0.00
% 1.89/1.25  Index Matching       : 0.00
% 1.89/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
