%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:24 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  60 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_25,plain,(
    ! [B_17,A_18] :
      ( r1_xboole_0(B_17,A_18)
      | ~ r1_xboole_0(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_46,plain,(
    ! [A_27,C_28,B_29,D_30] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_xboole_0(B_29,D_30)
      | ~ r1_tarski(C_28,D_30)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_33,C_34] :
      ( r1_xboole_0(A_33,C_34)
      | ~ r1_tarski(C_34,'#skF_1')
      | ~ r1_tarski(A_33,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( k7_relat_1(A_11,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    ! [A_39,A_40] :
      ( k7_relat_1(A_39,A_40) = k1_xboole_0
      | ~ v1_relat_1(A_39)
      | ~ r1_tarski(k1_relat_1(A_39),'#skF_1')
      | ~ r1_tarski(A_40,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_65,c_14])).

tff(c_658,plain,(
    ! [B_95,A_96] :
      ( k7_relat_1(k7_relat_1(B_95,'#skF_1'),A_96) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(B_95,'#skF_1'))
      | ~ r1_tarski(A_96,'#skF_2')
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_16,c_83])).

tff(c_924,plain,(
    ! [A_113,A_114] :
      ( k7_relat_1(k7_relat_1(A_113,'#skF_1'),A_114) = k1_xboole_0
      | ~ r1_tarski(A_114,'#skF_2')
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_12,c_658])).

tff(c_18,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_970,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_18])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8,c_970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.47  
% 3.17/1.47  %Foreground sorts:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Background operators:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Foreground operators:
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.17/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.17/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.47  
% 3.17/1.48  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 3.17/1.48  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.48  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.17/1.48  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.17/1.48  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.17/1.48  tff(f_43, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 3.17/1.48  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 3.17/1.48  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.48  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.48  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.48  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.17/1.48  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.48  tff(c_25, plain, (![B_17, A_18]: (r1_xboole_0(B_17, A_18) | ~r1_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.48  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_25])).
% 3.17/1.48  tff(c_46, plain, (![A_27, C_28, B_29, D_30]: (r1_xboole_0(A_27, C_28) | ~r1_xboole_0(B_29, D_30) | ~r1_tarski(C_28, D_30) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.48  tff(c_65, plain, (![A_33, C_34]: (r1_xboole_0(A_33, C_34) | ~r1_tarski(C_34, '#skF_1') | ~r1_tarski(A_33, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_46])).
% 3.17/1.48  tff(c_14, plain, (![A_11, B_13]: (k7_relat_1(A_11, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.17/1.48  tff(c_83, plain, (![A_39, A_40]: (k7_relat_1(A_39, A_40)=k1_xboole_0 | ~v1_relat_1(A_39) | ~r1_tarski(k1_relat_1(A_39), '#skF_1') | ~r1_tarski(A_40, '#skF_2'))), inference(resolution, [status(thm)], [c_65, c_14])).
% 3.17/1.48  tff(c_658, plain, (![B_95, A_96]: (k7_relat_1(k7_relat_1(B_95, '#skF_1'), A_96)=k1_xboole_0 | ~v1_relat_1(k7_relat_1(B_95, '#skF_1')) | ~r1_tarski(A_96, '#skF_2') | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_16, c_83])).
% 3.17/1.48  tff(c_924, plain, (![A_113, A_114]: (k7_relat_1(k7_relat_1(A_113, '#skF_1'), A_114)=k1_xboole_0 | ~r1_tarski(A_114, '#skF_2') | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_12, c_658])).
% 3.17/1.48  tff(c_18, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.48  tff(c_970, plain, (~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_924, c_18])).
% 3.17/1.48  tff(c_998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_8, c_970])).
% 3.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  Inference rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Ref     : 0
% 3.17/1.48  #Sup     : 227
% 3.17/1.48  #Fact    : 0
% 3.17/1.48  #Define  : 0
% 3.17/1.48  #Split   : 7
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 94
% 3.17/1.48  #Demod        : 118
% 3.17/1.48  #Tautology    : 37
% 3.17/1.48  #SimpNegUnit  : 5
% 3.17/1.48  #BackRed      : 3
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.48  Preprocessing        : 0.27
% 3.17/1.48  Parsing              : 0.15
% 3.17/1.48  CNF conversion       : 0.02
% 3.17/1.48  Main loop            : 0.43
% 3.17/1.48  Inferencing          : 0.15
% 3.17/1.48  Reduction            : 0.11
% 3.17/1.48  Demodulation         : 0.07
% 3.17/1.48  BG Simplification    : 0.02
% 3.17/1.48  Subsumption          : 0.12
% 3.17/1.48  Abstraction          : 0.02
% 3.17/1.48  MUC search           : 0.00
% 3.17/1.48  Cooper               : 0.00
% 3.17/1.48  Total                : 0.72
% 3.17/1.48  Index Insertion      : 0.00
% 3.17/1.48  Index Deletion       : 0.00
% 3.17/1.48  Index Matching       : 0.00
% 3.17/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
