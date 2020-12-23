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
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
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
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

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
    v4_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
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
      ( v4_relat_1(B_23,A_24)
      | ~ r1_tarski(k1_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    ! [B_27] :
      ( v4_relat_1(B_27,'#skF_2')
      | ~ v1_relat_1(B_27)
      | ~ r1_tarski(k1_relat_1(B_27),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_81,c_95])).

tff(c_161,plain,(
    ! [B_30] :
      ( v4_relat_1(B_30,'#skF_2')
      | ~ v4_relat_1(B_30,'#skF_1')
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_12,plain,(
    ~ v4_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_12])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:09:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.20  
% 1.83/1.20  %Foreground sorts:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Background operators:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Foreground operators:
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.83/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.83/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.20  
% 1.83/1.21  tff(f_51, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 1.83/1.21  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.83/1.21  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.83/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.83/1.21  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.83/1.21  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.21  tff(c_14, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.21  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.21  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.21  tff(c_52, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.21  tff(c_56, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_52])).
% 1.83/1.21  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.21  tff(c_61, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, k2_xboole_0(C_16, B_17)) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.21  tff(c_75, plain, (![A_18, B_19, A_20]: (r1_tarski(A_18, k2_xboole_0(B_19, A_20)) | ~r1_tarski(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 1.83/1.21  tff(c_81, plain, (![A_18]: (r1_tarski(A_18, '#skF_2') | ~r1_tarski(A_18, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_75])).
% 1.83/1.21  tff(c_95, plain, (![B_23, A_24]: (v4_relat_1(B_23, A_24) | ~r1_tarski(k1_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.21  tff(c_126, plain, (![B_27]: (v4_relat_1(B_27, '#skF_2') | ~v1_relat_1(B_27) | ~r1_tarski(k1_relat_1(B_27), '#skF_1'))), inference(resolution, [status(thm)], [c_81, c_95])).
% 1.83/1.21  tff(c_161, plain, (![B_30]: (v4_relat_1(B_30, '#skF_2') | ~v4_relat_1(B_30, '#skF_1') | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_10, c_126])).
% 1.83/1.21  tff(c_12, plain, (~v4_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.21  tff(c_164, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_161, c_12])).
% 1.83/1.21  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_164])).
% 1.83/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  Inference rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Ref     : 0
% 1.83/1.21  #Sup     : 36
% 1.83/1.21  #Fact    : 0
% 1.83/1.21  #Define  : 0
% 1.83/1.21  #Split   : 0
% 1.83/1.21  #Chain   : 0
% 1.83/1.21  #Close   : 0
% 1.83/1.21  
% 1.83/1.21  Ordering : KBO
% 1.83/1.21  
% 1.83/1.21  Simplification rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Subsume      : 3
% 1.83/1.21  #Demod        : 3
% 1.83/1.21  #Tautology    : 15
% 1.83/1.21  #SimpNegUnit  : 0
% 1.83/1.21  #BackRed      : 0
% 1.83/1.21  
% 1.83/1.21  #Partial instantiations: 0
% 1.83/1.21  #Strategies tried      : 1
% 1.83/1.21  
% 1.83/1.21  Timing (in seconds)
% 1.83/1.21  ----------------------
% 1.89/1.21  Preprocessing        : 0.27
% 1.89/1.21  Parsing              : 0.15
% 1.89/1.21  CNF conversion       : 0.02
% 1.89/1.21  Main loop            : 0.14
% 1.89/1.21  Inferencing          : 0.06
% 1.89/1.21  Reduction            : 0.04
% 1.89/1.21  Demodulation         : 0.03
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.03
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.44
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
