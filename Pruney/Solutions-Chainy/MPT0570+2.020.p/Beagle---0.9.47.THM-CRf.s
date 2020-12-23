%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:44 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  72 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_82,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(k2_relat_1(B_27),A_28)
      | k10_relat_1(B_27,A_28) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k2_relat_1(B_33),A_34) = k1_xboole_0
      | k10_relat_1(B_33,A_34) != k1_xboole_0
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_xboole_0(A_22,C_23)
      | ~ r1_xboole_0(B_24,C_23)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_29,B_30,A_31] :
      ( r1_xboole_0(A_29,B_30)
      | ~ r1_tarski(A_29,A_31)
      | k3_xboole_0(A_31,B_30) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_99,plain,(
    ! [B_30] :
      ( r1_xboole_0('#skF_1',B_30)
      | k3_xboole_0(k2_relat_1('#skF_2'),B_30) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_94])).

tff(c_114,plain,(
    ! [A_34] :
      ( r1_xboole_0('#skF_1',A_34)
      | k10_relat_1('#skF_2',A_34) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_99])).

tff(c_131,plain,(
    ! [A_35] :
      ( r1_xboole_0('#skF_1',A_35)
      | k10_relat_1('#skF_2',A_35) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_114])).

tff(c_139,plain,(
    ! [A_36] :
      ( k3_xboole_0('#skF_1',A_36) = k1_xboole_0
      | k10_relat_1('#skF_2',A_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_41,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_149,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_41])).

tff(c_163,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:32:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.96/1.23  
% 1.96/1.23  %Foreground sorts:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Background operators:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Foreground operators:
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.96/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.23  
% 1.96/1.24  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 1.96/1.24  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.96/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.96/1.24  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.96/1.24  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.96/1.24  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.96/1.24  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.24  tff(c_20, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.24  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.24  tff(c_82, plain, (![B_27, A_28]: (r1_xboole_0(k2_relat_1(B_27), A_28) | k10_relat_1(B_27, A_28)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.24  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.24  tff(c_107, plain, (![B_33, A_34]: (k3_xboole_0(k2_relat_1(B_33), A_34)=k1_xboole_0 | k10_relat_1(B_33, A_34)!=k1_xboole_0 | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_82, c_2])).
% 1.96/1.24  tff(c_22, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.24  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.24  tff(c_72, plain, (![A_22, C_23, B_24]: (r1_xboole_0(A_22, C_23) | ~r1_xboole_0(B_24, C_23) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.24  tff(c_94, plain, (![A_29, B_30, A_31]: (r1_xboole_0(A_29, B_30) | ~r1_tarski(A_29, A_31) | k3_xboole_0(A_31, B_30)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_72])).
% 1.96/1.24  tff(c_99, plain, (![B_30]: (r1_xboole_0('#skF_1', B_30) | k3_xboole_0(k2_relat_1('#skF_2'), B_30)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_94])).
% 1.96/1.24  tff(c_114, plain, (![A_34]: (r1_xboole_0('#skF_1', A_34) | k10_relat_1('#skF_2', A_34)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_99])).
% 1.96/1.24  tff(c_131, plain, (![A_35]: (r1_xboole_0('#skF_1', A_35) | k10_relat_1('#skF_2', A_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_114])).
% 1.96/1.24  tff(c_139, plain, (![A_36]: (k3_xboole_0('#skF_1', A_36)=k1_xboole_0 | k10_relat_1('#skF_2', A_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_131, c_2])).
% 1.96/1.24  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.24  tff(c_33, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.24  tff(c_41, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_10, c_33])).
% 1.96/1.24  tff(c_149, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_139, c_41])).
% 1.96/1.24  tff(c_163, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 1.96/1.24  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_163])).
% 1.96/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  Inference rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Ref     : 0
% 1.96/1.24  #Sup     : 32
% 1.96/1.24  #Fact    : 0
% 1.96/1.24  #Define  : 0
% 1.96/1.24  #Split   : 2
% 1.96/1.24  #Chain   : 0
% 1.96/1.24  #Close   : 0
% 1.96/1.24  
% 1.96/1.24  Ordering : KBO
% 1.96/1.24  
% 1.96/1.24  Simplification rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Subsume      : 1
% 1.96/1.24  #Demod        : 4
% 1.96/1.24  #Tautology    : 13
% 1.96/1.24  #SimpNegUnit  : 2
% 1.96/1.24  #BackRed      : 0
% 1.96/1.24  
% 1.96/1.24  #Partial instantiations: 0
% 1.96/1.24  #Strategies tried      : 1
% 1.96/1.24  
% 1.96/1.24  Timing (in seconds)
% 1.96/1.24  ----------------------
% 1.96/1.24  Preprocessing        : 0.31
% 1.96/1.24  Parsing              : 0.16
% 1.96/1.24  CNF conversion       : 0.02
% 1.96/1.24  Main loop            : 0.13
% 1.96/1.24  Inferencing          : 0.05
% 1.96/1.24  Reduction            : 0.04
% 1.96/1.24  Demodulation         : 0.03
% 1.96/1.24  BG Simplification    : 0.02
% 1.96/1.24  Subsumption          : 0.03
% 1.96/1.24  Abstraction          : 0.01
% 1.96/1.24  MUC search           : 0.00
% 1.96/1.24  Cooper               : 0.00
% 1.96/1.24  Total                : 0.46
% 1.96/1.24  Index Insertion      : 0.00
% 1.96/1.24  Index Deletion       : 0.00
% 1.96/1.24  Index Matching       : 0.00
% 1.96/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
