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
% DateTime   : Thu Dec  3 10:01:12 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   27 (  33 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  47 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_47,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [C_14,B_15,A_16] :
      ( k7_relat_1(k7_relat_1(C_14,B_15),A_16) = k7_relat_1(C_14,A_16)
      | ~ r1_tarski(A_16,B_15)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [C_17,B_18,A_19] :
      ( k9_relat_1(k7_relat_1(C_17,B_18),A_19) = k2_relat_1(k7_relat_1(C_17,A_19))
      | ~ v1_relat_1(k7_relat_1(C_17,B_18))
      | ~ r1_tarski(A_19,B_18)
      | ~ v1_relat_1(C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_6])).

tff(c_50,plain,(
    ! [A_20,B_21,A_22] :
      ( k9_relat_1(k7_relat_1(A_20,B_21),A_22) = k2_relat_1(k7_relat_1(A_20,A_22))
      | ~ r1_tarski(A_22,B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_8,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,
    ( k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_65,plain,(
    k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_56])).

tff(c_69,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:51:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.64/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  
% 1.64/1.11  tff(f_47, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 1.64/1.11  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.64/1.11  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.64/1.11  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 1.64/1.11  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.11  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.11  tff(c_10, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.11  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.11  tff(c_23, plain, (![C_14, B_15, A_16]: (k7_relat_1(k7_relat_1(C_14, B_15), A_16)=k7_relat_1(C_14, A_16) | ~r1_tarski(A_16, B_15) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.11  tff(c_44, plain, (![C_17, B_18, A_19]: (k9_relat_1(k7_relat_1(C_17, B_18), A_19)=k2_relat_1(k7_relat_1(C_17, A_19)) | ~v1_relat_1(k7_relat_1(C_17, B_18)) | ~r1_tarski(A_19, B_18) | ~v1_relat_1(C_17))), inference(superposition, [status(thm), theory('equality')], [c_23, c_6])).
% 1.64/1.11  tff(c_50, plain, (![A_20, B_21, A_22]: (k9_relat_1(k7_relat_1(A_20, B_21), A_22)=k2_relat_1(k7_relat_1(A_20, A_22)) | ~r1_tarski(A_22, B_21) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_2, c_44])).
% 1.64/1.11  tff(c_8, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.11  tff(c_56, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 1.64/1.11  tff(c_65, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_56])).
% 1.64/1.11  tff(c_69, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 1.64/1.11  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_69])).
% 1.64/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  Inference rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Ref     : 0
% 1.64/1.11  #Sup     : 15
% 1.64/1.11  #Fact    : 0
% 1.64/1.11  #Define  : 0
% 1.64/1.11  #Split   : 0
% 1.64/1.11  #Chain   : 0
% 1.64/1.11  #Close   : 0
% 1.64/1.11  
% 1.64/1.11  Ordering : KBO
% 1.64/1.11  
% 1.64/1.11  Simplification rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Subsume      : 2
% 1.64/1.11  #Demod        : 3
% 1.64/1.11  #Tautology    : 6
% 1.64/1.11  #SimpNegUnit  : 0
% 1.64/1.11  #BackRed      : 0
% 1.64/1.11  
% 1.64/1.11  #Partial instantiations: 0
% 1.64/1.11  #Strategies tried      : 1
% 1.64/1.11  
% 1.64/1.11  Timing (in seconds)
% 1.64/1.11  ----------------------
% 1.64/1.12  Preprocessing        : 0.25
% 1.64/1.12  Parsing              : 0.14
% 1.64/1.12  CNF conversion       : 0.02
% 1.64/1.12  Main loop            : 0.11
% 1.64/1.12  Inferencing          : 0.05
% 1.64/1.12  Reduction            : 0.02
% 1.64/1.12  Demodulation         : 0.02
% 1.64/1.12  BG Simplification    : 0.01
% 1.64/1.12  Subsumption          : 0.02
% 1.64/1.12  Abstraction          : 0.01
% 1.64/1.12  MUC search           : 0.00
% 1.64/1.12  Cooper               : 0.00
% 1.64/1.12  Total                : 0.38
% 1.64/1.12  Index Insertion      : 0.00
% 1.64/1.12  Index Deletion       : 0.00
% 1.64/1.12  Index Matching       : 0.00
% 1.64/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
