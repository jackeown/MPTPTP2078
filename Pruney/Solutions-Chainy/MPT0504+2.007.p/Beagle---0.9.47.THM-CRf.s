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
% DateTime   : Thu Dec  3 09:59:49 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  45 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,k3_xboole_0(B_19,C_20))
      | ~ r1_tarski(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [B_14,A_15] :
      ( B_14 = A_15
      | ~ r1_tarski(B_14,A_15)
      | ~ r1_tarski(A_15,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_22])).

tff(c_41,plain,(
    ! [B_19,C_20] :
      ( k3_xboole_0(B_19,C_20) = B_19
      | ~ r1_tarski(B_19,C_20)
      | ~ r1_tarski(B_19,B_19) ) ),
    inference(resolution,[status(thm)],[c_37,c_29])).

tff(c_48,plain,(
    ! [B_21,C_22] :
      ( k3_xboole_0(B_21,C_22) = B_21
      | ~ r1_tarski(B_21,C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_41])).

tff(c_64,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_48])).

tff(c_139,plain,(
    ! [C_26,A_27,B_28] :
      ( k7_relat_1(k7_relat_1(C_26,A_27),B_28) = k7_relat_1(C_26,k3_xboole_0(A_27,B_28))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_148,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_14])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_64,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:15:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.72/1.13  
% 1.72/1.13  %Foreground sorts:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Background operators:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Foreground operators:
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.72/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.13  
% 1.72/1.14  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.72/1.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.72/1.14  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.72/1.14  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.72/1.14  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.72/1.14  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.72/1.14  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.72/1.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.14  tff(c_37, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, k3_xboole_0(B_19, C_20)) | ~r1_tarski(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.14  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.14  tff(c_22, plain, (![B_14, A_15]: (B_14=A_15 | ~r1_tarski(B_14, A_15) | ~r1_tarski(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.14  tff(c_29, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_22])).
% 1.72/1.14  tff(c_41, plain, (![B_19, C_20]: (k3_xboole_0(B_19, C_20)=B_19 | ~r1_tarski(B_19, C_20) | ~r1_tarski(B_19, B_19))), inference(resolution, [status(thm)], [c_37, c_29])).
% 1.72/1.14  tff(c_48, plain, (![B_21, C_22]: (k3_xboole_0(B_21, C_22)=B_21 | ~r1_tarski(B_21, C_22))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_41])).
% 1.72/1.14  tff(c_64, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_16, c_48])).
% 1.72/1.14  tff(c_139, plain, (![C_26, A_27, B_28]: (k7_relat_1(k7_relat_1(C_26, A_27), B_28)=k7_relat_1(C_26, k3_xboole_0(A_27, B_28)) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.14  tff(c_14, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.72/1.14  tff(c_148, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_139, c_14])).
% 1.72/1.14  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_64, c_148])).
% 1.72/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  Inference rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Ref     : 0
% 1.72/1.14  #Sup     : 33
% 1.72/1.14  #Fact    : 0
% 1.72/1.14  #Define  : 0
% 1.72/1.14  #Split   : 1
% 1.72/1.14  #Chain   : 0
% 1.72/1.14  #Close   : 0
% 1.72/1.14  
% 1.72/1.14  Ordering : KBO
% 1.72/1.14  
% 1.72/1.14  Simplification rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Subsume      : 0
% 1.72/1.14  #Demod        : 22
% 1.72/1.14  #Tautology    : 22
% 1.72/1.14  #SimpNegUnit  : 0
% 1.72/1.14  #BackRed      : 0
% 1.72/1.14  
% 1.72/1.14  #Partial instantiations: 0
% 1.72/1.14  #Strategies tried      : 1
% 1.72/1.14  
% 1.72/1.14  Timing (in seconds)
% 1.72/1.14  ----------------------
% 1.72/1.14  Preprocessing        : 0.25
% 1.72/1.14  Parsing              : 0.14
% 1.72/1.14  CNF conversion       : 0.02
% 1.72/1.14  Main loop            : 0.13
% 1.72/1.14  Inferencing          : 0.05
% 1.72/1.14  Reduction            : 0.04
% 1.72/1.14  Demodulation         : 0.03
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.03
% 1.72/1.14  Abstraction          : 0.01
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.14  Cooper               : 0.00
% 1.72/1.14  Total                : 0.41
% 1.72/1.14  Index Insertion      : 0.00
% 1.72/1.14  Index Deletion       : 0.00
% 1.72/1.14  Index Matching       : 0.00
% 1.72/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
