%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:27 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  59 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_85,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_51,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_79,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_64])).

tff(c_126,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_79])).

tff(c_146,plain,(
    ! [C_30,A_31,B_32] :
      ( k7_relat_1(k7_relat_1(C_30,A_31),B_32) = k7_relat_1(C_30,k3_xboole_0(A_31,B_32))
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_20])).

tff(c_164,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_126,c_155])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [B_26,A_27] :
      ( k7_relat_1(B_26,A_27) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_26),A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_274,plain,(
    ! [B_40,B_41] :
      ( k7_relat_1(B_40,B_41) = k1_xboole_0
      | ~ v1_relat_1(B_40)
      | k4_xboole_0(k1_relat_1(B_40),B_41) != k1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_296,plain,(
    ! [B_42] :
      ( k7_relat_1(B_42,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_274])).

tff(c_299,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_296])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n003.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 09:29:26 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.06  
% 1.67/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.06  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.06  
% 1.67/1.06  %Foreground sorts:
% 1.67/1.06  
% 1.67/1.06  
% 1.67/1.06  %Background operators:
% 1.67/1.06  
% 1.67/1.06  
% 1.67/1.06  %Foreground operators:
% 1.67/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.67/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.67/1.06  
% 1.67/1.07  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.67/1.07  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.67/1.07  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.67/1.07  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.67/1.07  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.67/1.07  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.67/1.07  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.67/1.07  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.07  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.07  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.07  tff(c_64, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.07  tff(c_82, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 1.67/1.07  tff(c_85, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_82])).
% 1.67/1.07  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.07  tff(c_51, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.07  tff(c_59, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_51])).
% 1.67/1.07  tff(c_79, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_64])).
% 1.67/1.07  tff(c_126, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_85, c_79])).
% 1.67/1.07  tff(c_146, plain, (![C_30, A_31, B_32]: (k7_relat_1(k7_relat_1(C_30, A_31), B_32)=k7_relat_1(C_30, k3_xboole_0(A_31, B_32)) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.07  tff(c_20, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.07  tff(c_155, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_146, c_20])).
% 1.67/1.07  tff(c_164, plain, (k7_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_126, c_155])).
% 1.67/1.07  tff(c_10, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k4_xboole_0(A_5, B_6)!=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.07  tff(c_131, plain, (![B_26, A_27]: (k7_relat_1(B_26, A_27)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_26), A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.67/1.07  tff(c_274, plain, (![B_40, B_41]: (k7_relat_1(B_40, B_41)=k1_xboole_0 | ~v1_relat_1(B_40) | k4_xboole_0(k1_relat_1(B_40), B_41)!=k1_relat_1(B_40))), inference(resolution, [status(thm)], [c_10, c_131])).
% 1.67/1.07  tff(c_296, plain, (![B_42]: (k7_relat_1(B_42, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_4, c_274])).
% 1.67/1.07  tff(c_299, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_296])).
% 1.67/1.07  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_299])).
% 1.67/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.07  
% 1.67/1.07  Inference rules
% 1.67/1.07  ----------------------
% 1.67/1.07  #Ref     : 0
% 1.67/1.07  #Sup     : 66
% 1.67/1.07  #Fact    : 0
% 1.67/1.07  #Define  : 0
% 1.67/1.07  #Split   : 0
% 1.67/1.07  #Chain   : 0
% 1.67/1.07  #Close   : 0
% 1.67/1.07  
% 1.67/1.07  Ordering : KBO
% 1.67/1.07  
% 1.67/1.07  Simplification rules
% 1.67/1.07  ----------------------
% 1.67/1.07  #Subsume      : 3
% 1.67/1.07  #Demod        : 17
% 1.67/1.07  #Tautology    : 39
% 1.67/1.07  #SimpNegUnit  : 1
% 1.67/1.07  #BackRed      : 0
% 1.67/1.07  
% 1.67/1.07  #Partial instantiations: 0
% 1.67/1.07  #Strategies tried      : 1
% 1.67/1.07  
% 1.67/1.07  Timing (in seconds)
% 1.67/1.07  ----------------------
% 1.67/1.07  Preprocessing        : 0.27
% 1.67/1.07  Parsing              : 0.15
% 1.67/1.07  CNF conversion       : 0.02
% 1.67/1.07  Main loop            : 0.19
% 1.67/1.07  Inferencing          : 0.08
% 1.67/1.07  Reduction            : 0.05
% 1.67/1.07  Demodulation         : 0.04
% 1.67/1.07  BG Simplification    : 0.01
% 1.67/1.07  Subsumption          : 0.03
% 1.67/1.07  Abstraction          : 0.01
% 1.67/1.07  MUC search           : 0.00
% 1.67/1.07  Cooper               : 0.00
% 1.67/1.07  Total                : 0.48
% 1.67/1.07  Index Insertion      : 0.00
% 1.67/1.07  Index Deletion       : 0.00
% 1.67/1.07  Index Matching       : 0.00
% 1.67/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
