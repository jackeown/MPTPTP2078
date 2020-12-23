%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:26 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_349,plain,(
    ! [C_36,A_37,B_38] :
      ( k7_relat_1(k7_relat_1(C_36,A_37),B_38) = k7_relat_1(C_36,k3_xboole_0(A_37,B_38))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_358,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_20])).

tff(c_367,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_54,c_358])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [B_26,A_27] :
      ( k7_relat_1(B_26,A_27) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_26),A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_553,plain,(
    ! [B_48,B_49] :
      ( k7_relat_1(B_48,B_49) = k1_xboole_0
      | ~ v1_relat_1(B_48)
      | k3_xboole_0(k1_relat_1(B_48),B_49) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_163])).

tff(c_568,plain,(
    ! [B_50] :
      ( k7_relat_1(B_50,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_553])).

tff(c_571,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_568])).

tff(c_575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.27  
% 2.04/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.27  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.27  
% 2.04/1.27  %Foreground sorts:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Background operators:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Foreground operators:
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.04/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.27  
% 2.04/1.28  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.04/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.04/1.28  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.04/1.28  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.04/1.28  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.04/1.28  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_46, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.28  tff(c_54, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_46])).
% 2.04/1.28  tff(c_349, plain, (![C_36, A_37, B_38]: (k7_relat_1(k7_relat_1(C_36, A_37), B_38)=k7_relat_1(C_36, k3_xboole_0(A_37, B_38)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.28  tff(c_20, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_358, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_349, c_20])).
% 2.04/1.28  tff(c_367, plain, (k7_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_54, c_358])).
% 2.04/1.28  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.28  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.28  tff(c_163, plain, (![B_26, A_27]: (k7_relat_1(B_26, A_27)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_26), A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.28  tff(c_553, plain, (![B_48, B_49]: (k7_relat_1(B_48, B_49)=k1_xboole_0 | ~v1_relat_1(B_48) | k3_xboole_0(k1_relat_1(B_48), B_49)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_163])).
% 2.04/1.28  tff(c_568, plain, (![B_50]: (k7_relat_1(B_50, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_6, c_553])).
% 2.04/1.28  tff(c_571, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_568])).
% 2.04/1.28  tff(c_575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_571])).
% 2.04/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  Inference rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Ref     : 0
% 2.04/1.28  #Sup     : 130
% 2.04/1.28  #Fact    : 0
% 2.04/1.28  #Define  : 0
% 2.04/1.28  #Split   : 0
% 2.04/1.28  #Chain   : 0
% 2.04/1.28  #Close   : 0
% 2.04/1.28  
% 2.04/1.28  Ordering : KBO
% 2.04/1.28  
% 2.04/1.28  Simplification rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Subsume      : 1
% 2.04/1.28  #Demod        : 97
% 2.04/1.28  #Tautology    : 96
% 2.04/1.28  #SimpNegUnit  : 1
% 2.04/1.28  #BackRed      : 4
% 2.04/1.28  
% 2.04/1.28  #Partial instantiations: 0
% 2.04/1.28  #Strategies tried      : 1
% 2.04/1.28  
% 2.04/1.28  Timing (in seconds)
% 2.04/1.28  ----------------------
% 2.04/1.28  Preprocessing        : 0.26
% 2.04/1.28  Parsing              : 0.15
% 2.04/1.28  CNF conversion       : 0.02
% 2.04/1.28  Main loop            : 0.26
% 2.04/1.28  Inferencing          : 0.11
% 2.04/1.28  Reduction            : 0.08
% 2.04/1.29  Demodulation         : 0.06
% 2.04/1.29  BG Simplification    : 0.01
% 2.04/1.29  Subsumption          : 0.04
% 2.04/1.29  Abstraction          : 0.01
% 2.04/1.29  MUC search           : 0.00
% 2.04/1.29  Cooper               : 0.00
% 2.04/1.29  Total                : 0.55
% 2.04/1.29  Index Insertion      : 0.00
% 2.04/1.29  Index Deletion       : 0.00
% 2.04/1.29  Index Matching       : 0.00
% 2.04/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
