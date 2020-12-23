%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:43 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_43,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_43])).

tff(c_66,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_66])).

tff(c_87,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( k2_wellord1(k2_wellord1(C_15,A_13),B_14) = k2_wellord1(C_15,k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_227,plain,(
    ! [C_41,B_42,A_43] :
      ( k2_wellord1(k2_wellord1(C_41,B_42),A_43) = k2_wellord1(k2_wellord1(C_41,A_43),B_42)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_266,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_20])).

tff(c_311,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_266])).

tff(c_320,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_311])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_87,c_320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.61  
% 2.53/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.61  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.61  
% 2.53/1.61  %Foreground sorts:
% 2.53/1.61  
% 2.53/1.61  
% 2.53/1.61  %Background operators:
% 2.53/1.61  
% 2.53/1.61  
% 2.53/1.61  %Foreground operators:
% 2.53/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.61  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.53/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.61  
% 2.53/1.62  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 2.53/1.62  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.53/1.62  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.53/1.62  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.53/1.62  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 2.53/1.62  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_wellord1)).
% 2.53/1.62  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.62  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.62  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.62  tff(c_43, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.62  tff(c_47, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_43])).
% 2.53/1.62  tff(c_66, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.62  tff(c_81, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_47, c_66])).
% 2.53/1.62  tff(c_87, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_81])).
% 2.53/1.62  tff(c_16, plain, (![C_15, A_13, B_14]: (k2_wellord1(k2_wellord1(C_15, A_13), B_14)=k2_wellord1(C_15, k3_xboole_0(A_13, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.62  tff(c_227, plain, (![C_41, B_42, A_43]: (k2_wellord1(k2_wellord1(C_41, B_42), A_43)=k2_wellord1(k2_wellord1(C_41, A_43), B_42) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.62  tff(c_20, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.62  tff(c_266, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_227, c_20])).
% 2.53/1.62  tff(c_311, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_266])).
% 2.53/1.62  tff(c_320, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_311])).
% 2.53/1.62  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_87, c_320])).
% 2.53/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.62  
% 2.53/1.62  Inference rules
% 2.53/1.62  ----------------------
% 2.53/1.62  #Ref     : 0
% 2.53/1.62  #Sup     : 78
% 2.53/1.63  #Fact    : 0
% 2.53/1.63  #Define  : 0
% 2.53/1.63  #Split   : 0
% 2.53/1.63  #Chain   : 0
% 2.53/1.63  #Close   : 0
% 2.53/1.63  
% 2.53/1.63  Ordering : KBO
% 2.53/1.63  
% 2.53/1.63  Simplification rules
% 2.53/1.63  ----------------------
% 2.53/1.63  #Subsume      : 0
% 2.53/1.63  #Demod        : 24
% 2.53/1.63  #Tautology    : 47
% 2.53/1.63  #SimpNegUnit  : 0
% 2.53/1.63  #BackRed      : 0
% 2.53/1.63  
% 2.53/1.63  #Partial instantiations: 0
% 2.53/1.63  #Strategies tried      : 1
% 2.53/1.63  
% 2.53/1.63  Timing (in seconds)
% 2.53/1.63  ----------------------
% 2.53/1.63  Preprocessing        : 0.47
% 2.53/1.63  Parsing              : 0.25
% 2.53/1.63  CNF conversion       : 0.03
% 2.53/1.63  Main loop            : 0.30
% 2.53/1.63  Inferencing          : 0.13
% 2.53/1.63  Reduction            : 0.08
% 2.53/1.63  Demodulation         : 0.07
% 2.53/1.63  BG Simplification    : 0.02
% 2.53/1.63  Subsumption          : 0.04
% 2.53/1.63  Abstraction          : 0.02
% 2.53/1.63  MUC search           : 0.00
% 2.53/1.63  Cooper               : 0.00
% 2.53/1.63  Total                : 0.81
% 2.53/1.63  Index Insertion      : 0.00
% 2.53/1.63  Index Deletion       : 0.00
% 2.53/1.63  Index Matching       : 0.00
% 2.53/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
