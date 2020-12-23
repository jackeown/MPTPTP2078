%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:25 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  45 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_165,plain,(
    ! [C_42,A_43,B_44] :
      ( k7_relat_1(k7_relat_1(C_42,A_43),B_44) = k7_relat_1(C_42,k3_xboole_0(A_43,B_44))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_174,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_20])).

tff(c_183,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_84,c_174])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_5] : r1_xboole_0(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_8,c_26])).

tff(c_149,plain,(
    ! [A_40,B_41] :
      ( k7_relat_1(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(B_41,k1_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_185,plain,(
    ! [A_45] :
      ( k7_relat_1(A_45,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_31,c_149])).

tff(c_188,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_185])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  %$ r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.20  
% 1.81/1.20  %Foreground sorts:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Background operators:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Foreground operators:
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.81/1.20  
% 1.81/1.20  tff(f_59, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.81/1.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.81/1.20  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.81/1.20  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.81/1.20  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.81/1.20  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.81/1.20  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.81/1.20  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.81/1.20  tff(c_64, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.20  tff(c_84, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_64])).
% 1.81/1.20  tff(c_165, plain, (![C_42, A_43, B_44]: (k7_relat_1(k7_relat_1(C_42, A_43), B_44)=k7_relat_1(C_42, k3_xboole_0(A_43, B_44)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.20  tff(c_20, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.81/1.20  tff(c_174, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_165, c_20])).
% 1.81/1.20  tff(c_183, plain, (k7_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_84, c_174])).
% 1.81/1.20  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.20  tff(c_26, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.20  tff(c_31, plain, (![A_5]: (r1_xboole_0(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_8, c_26])).
% 1.81/1.20  tff(c_149, plain, (![A_40, B_41]: (k7_relat_1(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(B_41, k1_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.20  tff(c_185, plain, (![A_45]: (k7_relat_1(A_45, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_31, c_149])).
% 1.81/1.20  tff(c_188, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_185])).
% 1.81/1.20  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_188])).
% 1.81/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  Inference rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Ref     : 0
% 1.81/1.20  #Sup     : 41
% 1.81/1.20  #Fact    : 0
% 1.81/1.21  #Define  : 0
% 1.81/1.21  #Split   : 0
% 1.81/1.21  #Chain   : 0
% 1.81/1.21  #Close   : 0
% 1.81/1.21  
% 1.81/1.21  Ordering : KBO
% 1.81/1.21  
% 1.81/1.21  Simplification rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Subsume      : 1
% 1.81/1.21  #Demod        : 8
% 1.81/1.21  #Tautology    : 25
% 1.81/1.21  #SimpNegUnit  : 1
% 1.81/1.21  #BackRed      : 0
% 1.81/1.21  
% 1.81/1.21  #Partial instantiations: 0
% 1.81/1.21  #Strategies tried      : 1
% 1.81/1.21  
% 1.81/1.21  Timing (in seconds)
% 1.81/1.21  ----------------------
% 1.81/1.21  Preprocessing        : 0.30
% 1.81/1.21  Parsing              : 0.16
% 1.81/1.21  CNF conversion       : 0.02
% 1.81/1.21  Main loop            : 0.14
% 1.81/1.21  Inferencing          : 0.06
% 1.81/1.21  Reduction            : 0.04
% 1.81/1.21  Demodulation         : 0.03
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.02
% 1.81/1.21  Abstraction          : 0.01
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.46
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
