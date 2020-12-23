%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:44 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  57 expanded)
%              Number of equality atoms :   13 (  19 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(k2_relat_1(B_8),A_7)
      | k10_relat_1(B_8,A_7) != k1_xboole_0
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r1_tarski(C_19,B_18)
      | ~ r1_tarski(C_19,A_17)
      | v1_xboole_0(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [C_20,A_21,B_22] :
      ( ~ r1_tarski(C_20,A_21)
      | ~ r1_tarski(C_20,k2_relat_1(B_22))
      | v1_xboole_0(C_20)
      | k10_relat_1(B_22,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_14,c_47])).

tff(c_58,plain,(
    ! [B_23,B_24] :
      ( ~ r1_tarski(B_23,k2_relat_1(B_24))
      | v1_xboole_0(B_23)
      | k10_relat_1(B_24,B_23) != k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_8,c_51])).

tff(c_61,plain,
    ( v1_xboole_0('#skF_1')
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_68,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_61])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:01:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.18  
% 1.68/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.18  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.18  
% 1.68/1.18  %Foreground sorts:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Background operators:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Foreground operators:
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.68/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.68/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.18  
% 1.68/1.19  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 1.68/1.19  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.68/1.19  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.68/1.19  tff(f_45, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.68/1.19  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.68/1.19  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.19  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.19  tff(c_16, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.19  tff(c_18, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.19  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.19  tff(c_14, plain, (![B_8, A_7]: (r1_xboole_0(k2_relat_1(B_8), A_7) | k10_relat_1(B_8, A_7)!=k1_xboole_0 | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.68/1.19  tff(c_47, plain, (![A_17, B_18, C_19]: (~r1_xboole_0(A_17, B_18) | ~r1_tarski(C_19, B_18) | ~r1_tarski(C_19, A_17) | v1_xboole_0(C_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.68/1.19  tff(c_51, plain, (![C_20, A_21, B_22]: (~r1_tarski(C_20, A_21) | ~r1_tarski(C_20, k2_relat_1(B_22)) | v1_xboole_0(C_20) | k10_relat_1(B_22, A_21)!=k1_xboole_0 | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_14, c_47])).
% 1.68/1.19  tff(c_58, plain, (![B_23, B_24]: (~r1_tarski(B_23, k2_relat_1(B_24)) | v1_xboole_0(B_23) | k10_relat_1(B_24, B_23)!=k1_xboole_0 | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_8, c_51])).
% 1.68/1.19  tff(c_61, plain, (v1_xboole_0('#skF_1') | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_58])).
% 1.68/1.19  tff(c_68, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_61])).
% 1.68/1.19  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.19  tff(c_72, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_68, c_2])).
% 1.68/1.19  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_72])).
% 1.68/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.19  
% 1.68/1.19  Inference rules
% 1.68/1.19  ----------------------
% 1.68/1.19  #Ref     : 0
% 1.68/1.19  #Sup     : 11
% 1.68/1.19  #Fact    : 0
% 1.68/1.19  #Define  : 0
% 1.68/1.19  #Split   : 1
% 1.68/1.19  #Chain   : 0
% 1.68/1.19  #Close   : 0
% 1.68/1.19  
% 1.68/1.19  Ordering : KBO
% 1.68/1.19  
% 1.68/1.19  Simplification rules
% 1.68/1.19  ----------------------
% 1.68/1.19  #Subsume      : 0
% 1.68/1.19  #Demod        : 4
% 1.68/1.19  #Tautology    : 5
% 1.68/1.19  #SimpNegUnit  : 1
% 1.68/1.19  #BackRed      : 0
% 1.68/1.19  
% 1.68/1.19  #Partial instantiations: 0
% 1.68/1.19  #Strategies tried      : 1
% 1.68/1.19  
% 1.68/1.19  Timing (in seconds)
% 1.68/1.19  ----------------------
% 1.68/1.19  Preprocessing        : 0.26
% 1.68/1.19  Parsing              : 0.14
% 1.68/1.19  CNF conversion       : 0.02
% 1.68/1.19  Main loop            : 0.10
% 1.68/1.19  Inferencing          : 0.03
% 1.68/1.19  Reduction            : 0.03
% 1.68/1.19  Demodulation         : 0.02
% 1.68/1.19  BG Simplification    : 0.01
% 1.68/1.19  Subsumption          : 0.02
% 1.68/1.19  Abstraction          : 0.00
% 1.68/1.19  MUC search           : 0.00
% 1.68/1.19  Cooper               : 0.00
% 1.68/1.19  Total                : 0.38
% 1.68/1.19  Index Insertion      : 0.00
% 1.68/1.19  Index Deletion       : 0.00
% 1.68/1.19  Index Matching       : 0.00
% 1.68/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
