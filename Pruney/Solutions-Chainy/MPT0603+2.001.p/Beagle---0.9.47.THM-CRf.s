%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:24 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_subset_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_53,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_55,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_35] : k1_subset_1(A_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_36] : v1_xboole_0(k1_subset_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_269,plain,(
    ! [A_70,B_71] :
      ( v1_xboole_0(k7_relat_1(A_70,B_71))
      | ~ v1_xboole_0(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_300,plain,(
    ! [A_75,B_76] :
      ( k7_relat_1(A_75,B_76) = k1_xboole_0
      | ~ v1_xboole_0(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_269,c_6])).

tff(c_307,plain,(
    ! [A_77] :
      ( k7_relat_1(A_77,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_77) ) ),
    inference(resolution,[status(thm)],[c_53,c_300])).

tff(c_319,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_307])).

tff(c_50,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_130,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_130])).

tff(c_418,plain,(
    ! [C_89,A_90,B_91] :
      ( k7_relat_1(k7_relat_1(C_89,A_90),B_91) = k7_relat_1(C_89,k3_xboole_0(A_90,B_91))
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_440,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_48])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_319,c_138,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.31  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_subset_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.31  
% 2.30/1.31  %Foreground sorts:
% 2.30/1.31  
% 2.30/1.31  
% 2.30/1.31  %Background operators:
% 2.30/1.31  
% 2.30/1.31  
% 2.30/1.31  %Foreground operators:
% 2.30/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.30/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.31  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.30/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.30/1.31  
% 2.30/1.32  tff(f_97, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.30/1.32  tff(f_53, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.30/1.32  tff(f_55, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.30/1.32  tff(f_69, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 2.30/1.32  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.30/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.30/1.32  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.30/1.32  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.32  tff(c_24, plain, (![A_35]: (k1_subset_1(A_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.32  tff(c_26, plain, (![A_36]: (v1_xboole_0(k1_subset_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.30/1.32  tff(c_53, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.30/1.32  tff(c_269, plain, (![A_70, B_71]: (v1_xboole_0(k7_relat_1(A_70, B_71)) | ~v1_xboole_0(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.30/1.32  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.32  tff(c_300, plain, (![A_75, B_76]: (k7_relat_1(A_75, B_76)=k1_xboole_0 | ~v1_xboole_0(B_76) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_269, c_6])).
% 2.30/1.32  tff(c_307, plain, (![A_77]: (k7_relat_1(A_77, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_77))), inference(resolution, [status(thm)], [c_53, c_300])).
% 2.30/1.32  tff(c_319, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_307])).
% 2.30/1.32  tff(c_50, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.32  tff(c_130, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.32  tff(c_138, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_130])).
% 2.30/1.32  tff(c_418, plain, (![C_89, A_90, B_91]: (k7_relat_1(k7_relat_1(C_89, A_90), B_91)=k7_relat_1(C_89, k3_xboole_0(A_90, B_91)) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.30/1.32  tff(c_48, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.30/1.32  tff(c_440, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_418, c_48])).
% 2.30/1.32  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_319, c_138, c_440])).
% 2.30/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.32  
% 2.30/1.32  Inference rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Ref     : 0
% 2.30/1.32  #Sup     : 103
% 2.30/1.32  #Fact    : 0
% 2.30/1.32  #Define  : 0
% 2.30/1.32  #Split   : 1
% 2.30/1.32  #Chain   : 0
% 2.30/1.32  #Close   : 0
% 2.30/1.32  
% 2.30/1.32  Ordering : KBO
% 2.30/1.32  
% 2.30/1.32  Simplification rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Subsume      : 3
% 2.30/1.32  #Demod        : 47
% 2.30/1.32  #Tautology    : 70
% 2.30/1.32  #SimpNegUnit  : 1
% 2.30/1.32  #BackRed      : 0
% 2.30/1.32  
% 2.30/1.32  #Partial instantiations: 0
% 2.30/1.32  #Strategies tried      : 1
% 2.30/1.32  
% 2.30/1.32  Timing (in seconds)
% 2.30/1.32  ----------------------
% 2.30/1.32  Preprocessing        : 0.32
% 2.30/1.32  Parsing              : 0.17
% 2.30/1.32  CNF conversion       : 0.02
% 2.30/1.32  Main loop            : 0.24
% 2.30/1.32  Inferencing          : 0.08
% 2.30/1.32  Reduction            : 0.08
% 2.30/1.32  Demodulation         : 0.06
% 2.30/1.32  BG Simplification    : 0.02
% 2.30/1.32  Subsumption          : 0.05
% 2.30/1.32  Abstraction          : 0.02
% 2.30/1.32  MUC search           : 0.00
% 2.30/1.32  Cooper               : 0.00
% 2.30/1.32  Total                : 0.58
% 2.30/1.32  Index Insertion      : 0.00
% 2.30/1.32  Index Deletion       : 0.00
% 2.30/1.32  Index Matching       : 0.00
% 2.30/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
