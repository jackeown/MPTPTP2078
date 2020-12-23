%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  39 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_45,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r1_xboole_0(B,k1_relat_1(A))
           => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_12,plain,(
    k7_relat_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    k3_xboole_0('#skF_2',k1_relat_1('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [B_14,A_15] :
      ( k7_relat_1(B_14,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_14),A_15)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [B_18,B_19] :
      ( k7_relat_1(B_18,B_19) = k1_xboole_0
      | ~ v1_relat_1(B_18)
      | k3_xboole_0(k1_relat_1(B_18),B_19) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_115,plain,(
    ! [B_22,A_23] :
      ( k7_relat_1(B_22,A_23) = k1_xboole_0
      | ~ v1_relat_1(B_22)
      | k3_xboole_0(A_23,k1_relat_1(B_22)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_122,plain,
    ( k7_relat_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_115])).

tff(c_134,plain,(
    k7_relat_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_122])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:08:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.32  
% 1.81/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.33  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.33  
% 1.81/1.33  %Foreground sorts:
% 1.81/1.33  
% 1.81/1.33  
% 1.81/1.33  %Background operators:
% 1.81/1.33  
% 1.81/1.33  
% 1.81/1.33  %Foreground operators:
% 1.81/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.33  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.33  
% 1.99/1.34  tff(f_45, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.99/1.34  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.99/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.34  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.99/1.34  tff(c_12, plain, (k7_relat_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.34  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.34  tff(c_14, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.34  tff(c_51, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.34  tff(c_59, plain, (k3_xboole_0('#skF_2', k1_relat_1('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_51])).
% 1.99/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.34  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.34  tff(c_64, plain, (![B_14, A_15]: (k7_relat_1(B_14, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_14), A_15) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.34  tff(c_79, plain, (![B_18, B_19]: (k7_relat_1(B_18, B_19)=k1_xboole_0 | ~v1_relat_1(B_18) | k3_xboole_0(k1_relat_1(B_18), B_19)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_64])).
% 1.99/1.34  tff(c_115, plain, (![B_22, A_23]: (k7_relat_1(B_22, A_23)=k1_xboole_0 | ~v1_relat_1(B_22) | k3_xboole_0(A_23, k1_relat_1(B_22))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 1.99/1.34  tff(c_122, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_59, c_115])).
% 1.99/1.34  tff(c_134, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_122])).
% 1.99/1.34  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_134])).
% 1.99/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.34  
% 1.99/1.34  Inference rules
% 1.99/1.34  ----------------------
% 1.99/1.34  #Ref     : 0
% 1.99/1.34  #Sup     : 28
% 1.99/1.34  #Fact    : 0
% 1.99/1.34  #Define  : 0
% 1.99/1.34  #Split   : 0
% 1.99/1.34  #Chain   : 0
% 1.99/1.34  #Close   : 0
% 1.99/1.34  
% 1.99/1.34  Ordering : KBO
% 1.99/1.34  
% 1.99/1.34  Simplification rules
% 1.99/1.34  ----------------------
% 1.99/1.34  #Subsume      : 0
% 1.99/1.34  #Demod        : 1
% 1.99/1.34  #Tautology    : 15
% 1.99/1.34  #SimpNegUnit  : 1
% 1.99/1.34  #BackRed      : 0
% 1.99/1.34  
% 1.99/1.34  #Partial instantiations: 0
% 1.99/1.34  #Strategies tried      : 1
% 1.99/1.34  
% 1.99/1.34  Timing (in seconds)
% 1.99/1.34  ----------------------
% 1.99/1.34  Preprocessing        : 0.31
% 1.99/1.34  Parsing              : 0.15
% 1.99/1.34  CNF conversion       : 0.02
% 1.99/1.34  Main loop            : 0.15
% 1.99/1.34  Inferencing          : 0.07
% 1.99/1.34  Reduction            : 0.04
% 1.99/1.34  Demodulation         : 0.03
% 1.99/1.34  BG Simplification    : 0.02
% 1.99/1.34  Subsumption          : 0.03
% 1.99/1.34  Abstraction          : 0.01
% 1.99/1.34  MUC search           : 0.00
% 1.99/1.34  Cooper               : 0.00
% 1.99/1.34  Total                : 0.50
% 1.99/1.34  Index Insertion      : 0.00
% 1.99/1.34  Index Deletion       : 0.00
% 1.99/1.34  Index Matching       : 0.00
% 1.99/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
