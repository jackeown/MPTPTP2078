%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:47 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  56 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A) )
           => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,k2_xboole_0(C_16,B_17))
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_18,B_19,A_20] :
      ( r1_tarski(A_18,k2_xboole_0(B_19,A_20))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_81,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,'#skF_2')
      | ~ r1_tarski(A_18,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_75])).

tff(c_95,plain,(
    ! [B_23,A_24] :
      ( v5_relat_1(B_23,A_24)
      | ~ r1_tarski(k2_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    ! [B_27] :
      ( v5_relat_1(B_27,'#skF_2')
      | ~ v1_relat_1(B_27)
      | ~ r1_tarski(k2_relat_1(B_27),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_81,c_95])).

tff(c_161,plain,(
    ! [B_30] :
      ( v5_relat_1(B_30,'#skF_2')
      | ~ v5_relat_1(B_30,'#skF_1')
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_12,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_12])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.22  
% 1.84/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.22  %$ v5_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.22  
% 1.84/1.22  %Foreground sorts:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Background operators:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Foreground operators:
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.22  
% 1.95/1.23  tff(f_51, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 1.95/1.23  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.95/1.23  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.95/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.95/1.23  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.95/1.23  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.23  tff(c_14, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.23  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.23  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.23  tff(c_52, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.23  tff(c_56, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_52])).
% 1.95/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.23  tff(c_61, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, k2_xboole_0(C_16, B_17)) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.23  tff(c_75, plain, (![A_18, B_19, A_20]: (r1_tarski(A_18, k2_xboole_0(B_19, A_20)) | ~r1_tarski(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 1.95/1.23  tff(c_81, plain, (![A_18]: (r1_tarski(A_18, '#skF_2') | ~r1_tarski(A_18, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_75])).
% 1.95/1.23  tff(c_95, plain, (![B_23, A_24]: (v5_relat_1(B_23, A_24) | ~r1_tarski(k2_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.23  tff(c_126, plain, (![B_27]: (v5_relat_1(B_27, '#skF_2') | ~v1_relat_1(B_27) | ~r1_tarski(k2_relat_1(B_27), '#skF_1'))), inference(resolution, [status(thm)], [c_81, c_95])).
% 1.95/1.23  tff(c_161, plain, (![B_30]: (v5_relat_1(B_30, '#skF_2') | ~v5_relat_1(B_30, '#skF_1') | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_10, c_126])).
% 1.95/1.23  tff(c_12, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.23  tff(c_164, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_12])).
% 1.95/1.23  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_164])).
% 1.95/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  Inference rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Ref     : 0
% 1.95/1.23  #Sup     : 36
% 1.95/1.23  #Fact    : 0
% 1.95/1.23  #Define  : 0
% 1.95/1.23  #Split   : 0
% 1.95/1.23  #Chain   : 0
% 1.95/1.23  #Close   : 0
% 1.95/1.23  
% 1.95/1.23  Ordering : KBO
% 1.95/1.23  
% 1.95/1.23  Simplification rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Subsume      : 3
% 1.95/1.23  #Demod        : 3
% 1.95/1.23  #Tautology    : 15
% 1.95/1.23  #SimpNegUnit  : 0
% 1.95/1.23  #BackRed      : 0
% 1.95/1.23  
% 1.95/1.23  #Partial instantiations: 0
% 1.95/1.23  #Strategies tried      : 1
% 1.95/1.23  
% 1.95/1.23  Timing (in seconds)
% 1.95/1.23  ----------------------
% 1.95/1.23  Preprocessing        : 0.27
% 1.95/1.23  Parsing              : 0.16
% 1.95/1.23  CNF conversion       : 0.02
% 1.95/1.23  Main loop            : 0.15
% 1.95/1.23  Inferencing          : 0.06
% 1.95/1.23  Reduction            : 0.04
% 1.95/1.23  Demodulation         : 0.03
% 1.95/1.23  BG Simplification    : 0.01
% 1.95/1.23  Subsumption          : 0.03
% 1.95/1.23  Abstraction          : 0.01
% 1.95/1.23  MUC search           : 0.00
% 1.95/1.23  Cooper               : 0.00
% 1.95/1.23  Total                : 0.45
% 1.95/1.23  Index Insertion      : 0.00
% 1.95/1.24  Index Deletion       : 0.00
% 1.95/1.24  Index Matching       : 0.00
% 1.95/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
