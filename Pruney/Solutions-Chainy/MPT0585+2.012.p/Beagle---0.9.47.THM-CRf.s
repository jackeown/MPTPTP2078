%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:01 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k1_relat_1(B_9),A_8) = k1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [B_19,A_20] :
      ( k7_relat_1(B_19,A_20) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [B_24,A_25] :
      ( k7_relat_1(k7_relat_1(B_24,A_25),k1_relat_1(B_24)) = k7_relat_1(B_24,A_25)
      | ~ v1_relat_1(k7_relat_1(B_24,A_25))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( k7_relat_1(k7_relat_1(C_5,A_3),B_4) = k7_relat_1(C_5,k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [B_29,A_30] :
      ( k7_relat_1(B_29,k3_xboole_0(A_30,k1_relat_1(B_29))) = k7_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k7_relat_1(B_29,A_30))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4])).

tff(c_566,plain,(
    ! [B_48,B_49] :
      ( k7_relat_1(B_48,k1_relat_1(k7_relat_1(B_49,k1_relat_1(B_48)))) = k7_relat_1(B_48,k1_relat_1(B_49))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(k7_relat_1(B_48,k1_relat_1(B_49)))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_12,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_619,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_12])).

tff(c_657,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_619])).

tff(c_663,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_657])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.62/1.35  
% 2.62/1.35  %Foreground sorts:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Background operators:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Foreground operators:
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.35  
% 2.62/1.36  tff(f_55, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.62/1.36  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.62/1.36  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.62/1.36  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.62/1.36  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.62/1.36  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.62/1.36  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.36  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.36  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.36  tff(c_8, plain, (![B_9, A_8]: (k3_xboole_0(k1_relat_1(B_9), A_8)=k1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.36  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.36  tff(c_28, plain, (![B_19, A_20]: (k7_relat_1(B_19, A_20)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_20) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.62/1.36  tff(c_54, plain, (![B_24, A_25]: (k7_relat_1(k7_relat_1(B_24, A_25), k1_relat_1(B_24))=k7_relat_1(B_24, A_25) | ~v1_relat_1(k7_relat_1(B_24, A_25)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_6, c_28])).
% 2.62/1.36  tff(c_4, plain, (![C_5, A_3, B_4]: (k7_relat_1(k7_relat_1(C_5, A_3), B_4)=k7_relat_1(C_5, k3_xboole_0(A_3, B_4)) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.36  tff(c_106, plain, (![B_29, A_30]: (k7_relat_1(B_29, k3_xboole_0(A_30, k1_relat_1(B_29)))=k7_relat_1(B_29, A_30) | ~v1_relat_1(B_29) | ~v1_relat_1(k7_relat_1(B_29, A_30)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4])).
% 2.62/1.36  tff(c_566, plain, (![B_48, B_49]: (k7_relat_1(B_48, k1_relat_1(k7_relat_1(B_49, k1_relat_1(B_48))))=k7_relat_1(B_48, k1_relat_1(B_49)) | ~v1_relat_1(B_48) | ~v1_relat_1(k7_relat_1(B_48, k1_relat_1(B_49))) | ~v1_relat_1(B_48) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 2.62/1.36  tff(c_12, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.36  tff(c_619, plain, (~v1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_566, c_12])).
% 2.62/1.36  tff(c_657, plain, (~v1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_619])).
% 2.62/1.36  tff(c_663, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_657])).
% 2.62/1.36  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_663])).
% 2.62/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  Inference rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Ref     : 0
% 2.62/1.36  #Sup     : 188
% 2.62/1.36  #Fact    : 0
% 2.62/1.36  #Define  : 0
% 2.62/1.36  #Split   : 0
% 2.62/1.36  #Chain   : 0
% 2.62/1.36  #Close   : 0
% 2.62/1.36  
% 2.62/1.36  Ordering : KBO
% 2.62/1.36  
% 2.62/1.36  Simplification rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Subsume      : 36
% 2.62/1.36  #Demod        : 3
% 2.62/1.36  #Tautology    : 21
% 2.62/1.36  #SimpNegUnit  : 0
% 2.62/1.36  #BackRed      : 0
% 2.62/1.36  
% 2.62/1.36  #Partial instantiations: 0
% 2.62/1.36  #Strategies tried      : 1
% 2.62/1.36  
% 2.62/1.36  Timing (in seconds)
% 2.62/1.36  ----------------------
% 2.62/1.36  Preprocessing        : 0.27
% 2.62/1.36  Parsing              : 0.15
% 2.62/1.36  CNF conversion       : 0.02
% 2.62/1.36  Main loop            : 0.32
% 2.62/1.36  Inferencing          : 0.14
% 2.62/1.36  Reduction            : 0.08
% 2.62/1.36  Demodulation         : 0.06
% 2.62/1.36  BG Simplification    : 0.02
% 2.62/1.36  Subsumption          : 0.06
% 2.62/1.36  Abstraction          : 0.02
% 2.62/1.36  MUC search           : 0.00
% 2.62/1.36  Cooper               : 0.00
% 2.62/1.36  Total                : 0.62
% 2.62/1.36  Index Insertion      : 0.00
% 2.62/1.36  Index Deletion       : 0.00
% 2.62/1.36  Index Matching       : 0.00
% 2.62/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
