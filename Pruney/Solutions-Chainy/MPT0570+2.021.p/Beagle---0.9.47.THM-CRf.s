%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:44 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.87s
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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(k2_relat_1(B_9),A_8)
      | k10_relat_1(B_9,A_8) != k1_xboole_0
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
      | ~ r1_tarski(C_23,k2_relat_1(B_25))
      | v1_xboole_0(C_23)
      | k10_relat_1(B_25,A_24) != k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_69,plain,(
    ! [B_26,B_27] :
      ( ~ r1_tarski(B_26,k2_relat_1(B_27))
      | v1_xboole_0(B_26)
      | k10_relat_1(B_27,B_26) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_72,plain,
    ( v1_xboole_0('#skF_1')
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
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
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:38:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.87/1.21  
% 1.87/1.21  %Foreground sorts:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Background operators:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Foreground operators:
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.87/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.21  
% 1.87/1.22  tff(f_67, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 1.87/1.22  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.87/1.22  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.87/1.22  tff(f_42, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.87/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.87/1.22  tff(f_50, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.87/1.22  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.22  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.22  tff(c_18, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.22  tff(c_20, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.22  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.22  tff(c_16, plain, (![B_9, A_8]: (r1_xboole_0(k2_relat_1(B_9), A_8) | k10_relat_1(B_9, A_8)!=k1_xboole_0 | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.22  tff(c_58, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r1_tarski(C_22, B_21) | ~r1_tarski(C_22, A_20) | v1_xboole_0(C_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.87/1.22  tff(c_62, plain, (![C_23, A_24, B_25]: (~r1_tarski(C_23, A_24) | ~r1_tarski(C_23, k2_relat_1(B_25)) | v1_xboole_0(C_23) | k10_relat_1(B_25, A_24)!=k1_xboole_0 | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_16, c_58])).
% 1.87/1.22  tff(c_69, plain, (![B_26, B_27]: (~r1_tarski(B_26, k2_relat_1(B_27)) | v1_xboole_0(B_26) | k10_relat_1(B_27, B_26)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_8, c_62])).
% 1.87/1.22  tff(c_72, plain, (v1_xboole_0('#skF_1') | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_69])).
% 1.87/1.22  tff(c_79, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_72])).
% 1.87/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.87/1.22  tff(c_31, plain, (![B_11, A_12]: (~v1_xboole_0(B_11) | B_11=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.22  tff(c_34, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_2, c_31])).
% 1.87/1.22  tff(c_83, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_79, c_34])).
% 1.87/1.22  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_83])).
% 1.87/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  Inference rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Ref     : 0
% 1.87/1.22  #Sup     : 14
% 1.87/1.22  #Fact    : 0
% 1.87/1.22  #Define  : 0
% 1.87/1.22  #Split   : 1
% 1.87/1.22  #Chain   : 0
% 1.87/1.22  #Close   : 0
% 1.87/1.22  
% 1.87/1.22  Ordering : KBO
% 1.87/1.22  
% 1.87/1.22  Simplification rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Subsume      : 0
% 1.87/1.22  #Demod        : 4
% 1.87/1.22  #Tautology    : 6
% 1.87/1.22  #SimpNegUnit  : 1
% 1.87/1.22  #BackRed      : 0
% 1.87/1.22  
% 1.87/1.22  #Partial instantiations: 0
% 1.87/1.22  #Strategies tried      : 1
% 1.87/1.22  
% 1.87/1.22  Timing (in seconds)
% 1.87/1.22  ----------------------
% 1.87/1.22  Preprocessing        : 0.30
% 1.87/1.22  Parsing              : 0.16
% 1.87/1.22  CNF conversion       : 0.02
% 1.87/1.22  Main loop            : 0.11
% 1.87/1.22  Inferencing          : 0.04
% 1.87/1.22  Reduction            : 0.03
% 1.87/1.22  Demodulation         : 0.02
% 1.87/1.22  BG Simplification    : 0.01
% 1.87/1.22  Subsumption          : 0.02
% 1.87/1.22  Abstraction          : 0.00
% 1.87/1.22  MUC search           : 0.00
% 1.87/1.22  Cooper               : 0.00
% 1.87/1.22  Total                : 0.43
% 1.87/1.22  Index Insertion      : 0.00
% 1.87/1.22  Index Deletion       : 0.00
% 1.87/1.22  Index Matching       : 0.00
% 1.87/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
