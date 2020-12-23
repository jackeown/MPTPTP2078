%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:47 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [B_13,A_14] :
      ( r1_xboole_0(k2_relat_1(B_13),A_14)
      | k10_relat_1(B_13,A_14) != k1_xboole_0
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( r1_xboole_0(B_3,A_2)
      | ~ r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,k2_relat_1(B_18))
      | k10_relat_1(B_18,A_17) != k1_xboole_0
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_26,c_4])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ r1_xboole_0(B_5,A_4)
      | ~ r1_tarski(B_5,A_4)
      | v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [A_19,B_20] :
      ( ~ r1_tarski(A_19,k2_relat_1(B_20))
      | v1_xboole_0(A_19)
      | k10_relat_1(B_20,A_19) != k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_39,c_6])).

tff(c_55,plain,
    ( v1_xboole_0('#skF_1')
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_52])).

tff(c_58,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12,c_55])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.62/1.09  
% 1.62/1.09  %Foreground sorts:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Background operators:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Foreground operators:
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.62/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.09  
% 1.62/1.10  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 1.62/1.10  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.62/1.10  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.62/1.10  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.62/1.10  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.62/1.10  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.62/1.10  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.62/1.10  tff(c_12, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.62/1.10  tff(c_14, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.62/1.10  tff(c_26, plain, (![B_13, A_14]: (r1_xboole_0(k2_relat_1(B_13), A_14) | k10_relat_1(B_13, A_14)!=k1_xboole_0 | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.10  tff(c_4, plain, (![B_3, A_2]: (r1_xboole_0(B_3, A_2) | ~r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.10  tff(c_39, plain, (![A_17, B_18]: (r1_xboole_0(A_17, k2_relat_1(B_18)) | k10_relat_1(B_18, A_17)!=k1_xboole_0 | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_26, c_4])).
% 1.62/1.10  tff(c_6, plain, (![B_5, A_4]: (~r1_xboole_0(B_5, A_4) | ~r1_tarski(B_5, A_4) | v1_xboole_0(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.10  tff(c_52, plain, (![A_19, B_20]: (~r1_tarski(A_19, k2_relat_1(B_20)) | v1_xboole_0(A_19) | k10_relat_1(B_20, A_19)!=k1_xboole_0 | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_39, c_6])).
% 1.62/1.10  tff(c_55, plain, (v1_xboole_0('#skF_1') | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_52])).
% 1.62/1.10  tff(c_58, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12, c_55])).
% 1.62/1.10  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.10  tff(c_61, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.62/1.10  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_61])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.10  #Sup     : 10
% 1.62/1.10  #Fact    : 0
% 1.62/1.10  #Define  : 0
% 1.62/1.10  #Split   : 0
% 1.62/1.10  #Chain   : 0
% 1.62/1.10  #Close   : 0
% 1.62/1.10  
% 1.62/1.10  Ordering : KBO
% 1.62/1.10  
% 1.62/1.10  Simplification rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Subsume      : 1
% 1.62/1.10  #Demod        : 2
% 1.62/1.10  #Tautology    : 3
% 1.62/1.10  #SimpNegUnit  : 1
% 1.62/1.10  #BackRed      : 0
% 1.62/1.10  
% 1.62/1.10  #Partial instantiations: 0
% 1.62/1.10  #Strategies tried      : 1
% 1.62/1.10  
% 1.62/1.10  Timing (in seconds)
% 1.62/1.10  ----------------------
% 1.62/1.10  Preprocessing        : 0.26
% 1.62/1.10  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.02
% 1.62/1.10  Main loop            : 0.09
% 1.62/1.10  Inferencing          : 0.04
% 1.62/1.10  Reduction            : 0.02
% 1.62/1.10  Demodulation         : 0.02
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.01
% 1.62/1.10  Abstraction          : 0.00
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.11  Cooper               : 0.00
% 1.62/1.11  Total                : 0.36
% 1.62/1.11  Index Insertion      : 0.00
% 1.62/1.11  Index Deletion       : 0.00
% 1.62/1.11  Index Matching       : 0.00
% 1.62/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
