%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:35 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_63,axiom,(
    ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : r1_relat_2(k1_wellord2(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord2)).

tff(c_32,plain,(
    ! [A_23] : v1_relat_1(k1_wellord2(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_24] : v1_relat_2(k1_wellord2(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_15] :
      ( k3_relat_1(k1_wellord2(A_15)) = A_15
      | ~ v1_relat_1(k1_wellord2(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [A_15] : k3_relat_1(k1_wellord2(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( r2_hidden('#skF_1'(A_1,B_7),B_7)
      | r1_relat_2(A_1,B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_14,A_11] :
      ( r2_hidden(k4_tarski(B_14,B_14),A_11)
      | ~ r2_hidden(B_14,k3_relat_1(A_11))
      | ~ v1_relat_2(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_39,B_40),'#skF_1'(A_39,B_40)),A_39)
      | r1_relat_2(A_39,B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_41,B_42] :
      ( r1_relat_2(A_41,B_42)
      | ~ r2_hidden('#skF_1'(A_41,B_42),k3_relat_1(A_41))
      | ~ v1_relat_2(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_123,plain,(
    ! [A_43] :
      ( ~ v1_relat_2(A_43)
      | r1_relat_2(A_43,k3_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_126,plain,(
    ! [A_15] :
      ( ~ v1_relat_2(k1_wellord2(A_15))
      | r1_relat_2(k1_wellord2(A_15),A_15)
      | ~ v1_relat_1(k1_wellord2(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_123])).

tff(c_128,plain,(
    ! [A_15] : r1_relat_2(k1_wellord2(A_15),A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_126])).

tff(c_36,plain,(
    ~ r1_relat_2(k1_wellord2('#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:04:21 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.24  %$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.24  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.16/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.16/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.24  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.16/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.24  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.16/1.24  
% 2.18/1.25  tff(f_61, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.18/1.25  tff(f_63, axiom, (![A]: v1_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 2.18/1.25  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 2.18/1.25  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 2.18/1.25  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 2.18/1.25  tff(f_66, negated_conjecture, ~(![A]: r1_relat_2(k1_wellord2(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord2)).
% 2.18/1.25  tff(c_32, plain, (![A_23]: (v1_relat_1(k1_wellord2(A_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.25  tff(c_34, plain, (![A_24]: (v1_relat_2(k1_wellord2(A_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.25  tff(c_26, plain, (![A_15]: (k3_relat_1(k1_wellord2(A_15))=A_15 | ~v1_relat_1(k1_wellord2(A_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.25  tff(c_42, plain, (![A_15]: (k3_relat_1(k1_wellord2(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 2.18/1.25  tff(c_6, plain, (![A_1, B_7]: (r2_hidden('#skF_1'(A_1, B_7), B_7) | r1_relat_2(A_1, B_7) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.25  tff(c_8, plain, (![B_14, A_11]: (r2_hidden(k4_tarski(B_14, B_14), A_11) | ~r2_hidden(B_14, k3_relat_1(A_11)) | ~v1_relat_2(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.25  tff(c_106, plain, (![A_39, B_40]: (~r2_hidden(k4_tarski('#skF_1'(A_39, B_40), '#skF_1'(A_39, B_40)), A_39) | r1_relat_2(A_39, B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.25  tff(c_112, plain, (![A_41, B_42]: (r1_relat_2(A_41, B_42) | ~r2_hidden('#skF_1'(A_41, B_42), k3_relat_1(A_41)) | ~v1_relat_2(A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_8, c_106])).
% 2.18/1.25  tff(c_123, plain, (![A_43]: (~v1_relat_2(A_43) | r1_relat_2(A_43, k3_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_6, c_112])).
% 2.18/1.25  tff(c_126, plain, (![A_15]: (~v1_relat_2(k1_wellord2(A_15)) | r1_relat_2(k1_wellord2(A_15), A_15) | ~v1_relat_1(k1_wellord2(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_123])).
% 2.18/1.25  tff(c_128, plain, (![A_15]: (r1_relat_2(k1_wellord2(A_15), A_15))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_126])).
% 2.18/1.25  tff(c_36, plain, (~r1_relat_2(k1_wellord2('#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.18/1.25  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_36])).
% 2.18/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  Inference rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Ref     : 0
% 2.18/1.25  #Sup     : 17
% 2.18/1.25  #Fact    : 0
% 2.18/1.25  #Define  : 0
% 2.18/1.25  #Split   : 0
% 2.18/1.25  #Chain   : 0
% 2.18/1.25  #Close   : 0
% 2.18/1.25  
% 2.18/1.25  Ordering : KBO
% 2.18/1.25  
% 2.18/1.25  Simplification rules
% 2.18/1.25  ----------------------
% 2.18/1.26  #Subsume      : 0
% 2.18/1.26  #Demod        : 22
% 2.18/1.26  #Tautology    : 10
% 2.18/1.26  #SimpNegUnit  : 0
% 2.18/1.26  #BackRed      : 1
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.32
% 2.18/1.26  Parsing              : 0.17
% 2.18/1.26  CNF conversion       : 0.02
% 2.18/1.26  Main loop            : 0.17
% 2.18/1.26  Inferencing          : 0.07
% 2.18/1.26  Reduction            : 0.05
% 2.18/1.26  Demodulation         : 0.04
% 2.18/1.26  BG Simplification    : 0.02
% 2.18/1.26  Subsumption          : 0.03
% 2.18/1.26  Abstraction          : 0.01
% 2.18/1.26  MUC search           : 0.00
% 2.18/1.26  Cooper               : 0.00
% 2.18/1.26  Total                : 0.52
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
