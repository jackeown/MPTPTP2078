%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:53 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  63 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(k1_relat_1(B_9),A_8)
      | k9_relat_1(B_9,A_8) != k1_xboole_0
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r1_tarski(C_22,B_21)
      | ~ r1_tarski(C_22,A_20)
      | v1_xboole_0(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [C_23,A_24,B_25] :
      ( ~ r1_tarski(C_23,A_24)
      | ~ r1_tarski(C_23,k1_relat_1(B_25))
      | v1_xboole_0(C_23)
      | k9_relat_1(B_25,A_24) != k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_69,plain,(
    ! [B_26,B_27] :
      ( ~ r1_tarski(B_26,k1_relat_1(B_27))
      | v1_xboole_0(B_26)
      | k9_relat_1(B_27,B_26) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_72,plain,
    ( v1_xboole_0('#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_69])).

tff(c_79,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_31,plain,(
    ! [B_11,A_12] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_2,c_31])).

tff(c_83,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_79,c_34])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:33:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.13  
% 1.80/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.13  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.80/1.13  
% 1.80/1.13  %Foreground sorts:
% 1.80/1.13  
% 1.80/1.13  
% 1.80/1.13  %Background operators:
% 1.80/1.13  
% 1.80/1.13  
% 1.80/1.13  %Foreground operators:
% 1.80/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.80/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.80/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.13  
% 1.80/1.14  tff(f_67, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 1.80/1.14  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.80/1.14  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.80/1.14  tff(f_42, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.80/1.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.80/1.14  tff(f_50, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.80/1.14  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.14  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.14  tff(c_18, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.14  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.14  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.80/1.14  tff(c_16, plain, (![B_9, A_8]: (r1_xboole_0(k1_relat_1(B_9), A_8) | k9_relat_1(B_9, A_8)!=k1_xboole_0 | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.80/1.14  tff(c_58, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r1_tarski(C_22, B_21) | ~r1_tarski(C_22, A_20) | v1_xboole_0(C_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.80/1.14  tff(c_62, plain, (![C_23, A_24, B_25]: (~r1_tarski(C_23, A_24) | ~r1_tarski(C_23, k1_relat_1(B_25)) | v1_xboole_0(C_23) | k9_relat_1(B_25, A_24)!=k1_xboole_0 | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_16, c_58])).
% 1.80/1.14  tff(c_69, plain, (![B_26, B_27]: (~r1_tarski(B_26, k1_relat_1(B_27)) | v1_xboole_0(B_26) | k9_relat_1(B_27, B_26)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_8, c_62])).
% 1.80/1.14  tff(c_72, plain, (v1_xboole_0('#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_69])).
% 1.80/1.14  tff(c_79, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_72])).
% 1.80/1.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.80/1.14  tff(c_31, plain, (![B_11, A_12]: (~v1_xboole_0(B_11) | B_11=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.14  tff(c_34, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_2, c_31])).
% 1.80/1.14  tff(c_83, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_79, c_34])).
% 1.80/1.14  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_83])).
% 1.80/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.14  
% 1.80/1.14  Inference rules
% 1.80/1.14  ----------------------
% 1.80/1.14  #Ref     : 0
% 1.80/1.14  #Sup     : 14
% 1.80/1.14  #Fact    : 0
% 1.80/1.14  #Define  : 0
% 1.80/1.14  #Split   : 1
% 1.80/1.14  #Chain   : 0
% 1.80/1.14  #Close   : 0
% 1.80/1.14  
% 1.80/1.14  Ordering : KBO
% 1.80/1.14  
% 1.80/1.14  Simplification rules
% 1.80/1.14  ----------------------
% 1.80/1.14  #Subsume      : 0
% 1.80/1.14  #Demod        : 4
% 1.80/1.14  #Tautology    : 6
% 1.80/1.14  #SimpNegUnit  : 1
% 1.80/1.14  #BackRed      : 0
% 1.80/1.14  
% 1.80/1.14  #Partial instantiations: 0
% 1.80/1.14  #Strategies tried      : 1
% 1.80/1.14  
% 1.80/1.14  Timing (in seconds)
% 1.80/1.14  ----------------------
% 1.80/1.14  Preprocessing        : 0.28
% 1.80/1.14  Parsing              : 0.15
% 1.80/1.14  CNF conversion       : 0.02
% 1.80/1.15  Main loop            : 0.11
% 1.80/1.15  Inferencing          : 0.04
% 1.80/1.15  Reduction            : 0.03
% 1.80/1.15  Demodulation         : 0.02
% 1.80/1.15  BG Simplification    : 0.01
% 1.80/1.15  Subsumption          : 0.02
% 1.80/1.15  Abstraction          : 0.00
% 1.80/1.15  MUC search           : 0.00
% 1.80/1.15  Cooper               : 0.00
% 1.80/1.15  Total                : 0.41
% 1.80/1.15  Index Insertion      : 0.00
% 1.80/1.15  Index Deletion       : 0.00
% 1.80/1.15  Index Matching       : 0.00
% 1.80/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
