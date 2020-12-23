%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:53 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  52 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(k1_relat_1(B_7),A_6)
      | k9_relat_1(B_7,A_6) != k1_xboole_0
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_xboole_0 = A_15
      | ~ r1_xboole_0(B_16,C_17)
      | ~ r1_tarski(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_18,A_19,B_20] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,A_19)
      | ~ r1_tarski(A_18,k1_relat_1(B_20))
      | k9_relat_1(B_20,A_19) != k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_12,c_44])).

tff(c_64,plain,(
    ! [B_22,B_23] :
      ( k1_xboole_0 = B_22
      | ~ r1_tarski(B_22,k1_relat_1(B_23))
      | k9_relat_1(B_23,B_22) != k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_67,plain,
    ( k1_xboole_0 = '#skF_1'
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_74,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_67])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:30:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.23  
% 1.81/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.23  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.23  
% 1.81/1.23  %Foreground sorts:
% 1.81/1.23  
% 1.81/1.23  
% 1.81/1.23  %Background operators:
% 1.81/1.23  
% 1.81/1.23  
% 1.81/1.23  %Foreground operators:
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.81/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.23  
% 1.88/1.24  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 1.88/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.88/1.24  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.88/1.24  tff(f_39, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.88/1.24  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.24  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.24  tff(c_14, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.24  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.24  tff(c_12, plain, (![B_7, A_6]: (r1_xboole_0(k1_relat_1(B_7), A_6) | k9_relat_1(B_7, A_6)!=k1_xboole_0 | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.24  tff(c_44, plain, (![A_15, B_16, C_17]: (k1_xboole_0=A_15 | ~r1_xboole_0(B_16, C_17) | ~r1_tarski(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.24  tff(c_48, plain, (![A_18, A_19, B_20]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, A_19) | ~r1_tarski(A_18, k1_relat_1(B_20)) | k9_relat_1(B_20, A_19)!=k1_xboole_0 | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_12, c_44])).
% 1.88/1.24  tff(c_64, plain, (![B_22, B_23]: (k1_xboole_0=B_22 | ~r1_tarski(B_22, k1_relat_1(B_23)) | k9_relat_1(B_23, B_22)!=k1_xboole_0 | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_6, c_48])).
% 1.88/1.24  tff(c_67, plain, (k1_xboole_0='#skF_1' | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_64])).
% 1.88/1.24  tff(c_74, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_67])).
% 1.88/1.24  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_74])).
% 1.88/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.24  
% 1.88/1.24  Inference rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Ref     : 0
% 1.88/1.24  #Sup     : 11
% 1.88/1.24  #Fact    : 0
% 1.88/1.24  #Define  : 0
% 1.88/1.24  #Split   : 1
% 1.88/1.24  #Chain   : 0
% 1.88/1.24  #Close   : 0
% 1.88/1.24  
% 1.88/1.24  Ordering : KBO
% 1.88/1.24  
% 1.88/1.24  Simplification rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Subsume      : 0
% 1.88/1.24  #Demod        : 5
% 1.88/1.24  #Tautology    : 5
% 1.88/1.24  #SimpNegUnit  : 2
% 1.88/1.24  #BackRed      : 0
% 1.88/1.24  
% 1.88/1.24  #Partial instantiations: 0
% 1.88/1.24  #Strategies tried      : 1
% 1.88/1.24  
% 1.88/1.24  Timing (in seconds)
% 1.88/1.24  ----------------------
% 1.88/1.24  Preprocessing        : 0.29
% 1.88/1.24  Parsing              : 0.15
% 1.88/1.24  CNF conversion       : 0.02
% 1.88/1.24  Main loop            : 0.10
% 1.88/1.24  Inferencing          : 0.04
% 1.88/1.24  Reduction            : 0.03
% 1.88/1.24  Demodulation         : 0.02
% 1.88/1.24  BG Simplification    : 0.01
% 1.88/1.24  Subsumption          : 0.02
% 1.88/1.24  Abstraction          : 0.00
% 1.88/1.24  MUC search           : 0.00
% 1.88/1.24  Cooper               : 0.00
% 1.88/1.24  Total                : 0.42
% 1.88/1.24  Index Insertion      : 0.00
% 1.88/1.24  Index Deletion       : 0.00
% 1.88/1.24  Index Matching       : 0.00
% 1.88/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
