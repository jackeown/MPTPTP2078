%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:53 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  54 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_30,B_31,C_32] : r1_tarski(k2_xboole_0(k3_xboole_0(A_30,B_31),k3_xboole_0(A_30,C_32)),k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_30,B_31] : r1_tarski(k3_xboole_0(A_30,B_31),k2_xboole_0(B_31,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_169,plain,(
    ! [A_30,B_31] : r1_tarski(k3_xboole_0(A_30,B_31),B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_67,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(k3_xboole_0(A_23,C_24),k3_xboole_0(B_25,C_24))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [B_35,B_36] :
      ( r1_tarski(B_35,k3_xboole_0(B_36,B_35))
      | ~ r1_tarski(B_35,B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_67])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_191,plain,(
    ! [B_36,B_35] :
      ( k3_xboole_0(B_36,B_35) = B_35
      | ~ r1_tarski(k3_xboole_0(B_36,B_35),B_35)
      | ~ r1_tarski(B_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_189,c_4])).

tff(c_264,plain,(
    ! [B_38,B_39] :
      ( k3_xboole_0(B_38,B_39) = B_39
      | ~ r1_tarski(B_39,B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_191])).

tff(c_305,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_264])).

tff(c_358,plain,(
    ! [C_40,A_41,B_42] :
      ( k7_relat_1(k7_relat_1(C_40,A_41),B_42) = k7_relat_1(C_40,k3_xboole_0(A_41,B_42))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_367,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_18])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_305,c_367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.35  
% 1.95/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.35  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.17/1.35  
% 2.17/1.35  %Foreground sorts:
% 2.17/1.35  
% 2.17/1.35  
% 2.17/1.35  %Background operators:
% 2.17/1.35  
% 2.17/1.35  
% 2.17/1.35  %Foreground operators:
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.35  
% 2.17/1.36  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.17/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.17/1.36  tff(f_43, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.17/1.36  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.36  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.17/1.36  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.17/1.36  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.17/1.36  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.36  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.36  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.36  tff(c_142, plain, (![A_30, B_31, C_32]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_30, B_31), k3_xboole_0(A_30, C_32)), k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.36  tff(c_163, plain, (![A_30, B_31]: (r1_tarski(k3_xboole_0(A_30, B_31), k2_xboole_0(B_31, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_142])).
% 2.17/1.36  tff(c_169, plain, (![A_30, B_31]: (r1_tarski(k3_xboole_0(A_30, B_31), B_31))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_163])).
% 2.17/1.36  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.36  tff(c_34, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.36  tff(c_41, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_34])).
% 2.17/1.36  tff(c_67, plain, (![A_23, C_24, B_25]: (r1_tarski(k3_xboole_0(A_23, C_24), k3_xboole_0(B_25, C_24)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.36  tff(c_189, plain, (![B_35, B_36]: (r1_tarski(B_35, k3_xboole_0(B_36, B_35)) | ~r1_tarski(B_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_41, c_67])).
% 2.17/1.36  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.36  tff(c_191, plain, (![B_36, B_35]: (k3_xboole_0(B_36, B_35)=B_35 | ~r1_tarski(k3_xboole_0(B_36, B_35), B_35) | ~r1_tarski(B_35, B_36))), inference(resolution, [status(thm)], [c_189, c_4])).
% 2.17/1.36  tff(c_264, plain, (![B_38, B_39]: (k3_xboole_0(B_38, B_39)=B_39 | ~r1_tarski(B_39, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_191])).
% 2.17/1.36  tff(c_305, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_264])).
% 2.17/1.36  tff(c_358, plain, (![C_40, A_41, B_42]: (k7_relat_1(k7_relat_1(C_40, A_41), B_42)=k7_relat_1(C_40, k3_xboole_0(A_41, B_42)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.36  tff(c_18, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.36  tff(c_367, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_358, c_18])).
% 2.17/1.36  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_305, c_367])).
% 2.17/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.36  
% 2.17/1.36  Inference rules
% 2.17/1.36  ----------------------
% 2.17/1.36  #Ref     : 0
% 2.17/1.36  #Sup     : 91
% 2.17/1.36  #Fact    : 0
% 2.17/1.36  #Define  : 0
% 2.17/1.36  #Split   : 1
% 2.17/1.36  #Chain   : 0
% 2.17/1.36  #Close   : 0
% 2.17/1.36  
% 2.17/1.36  Ordering : KBO
% 2.17/1.36  
% 2.17/1.36  Simplification rules
% 2.17/1.36  ----------------------
% 2.17/1.36  #Subsume      : 2
% 2.17/1.36  #Demod        : 41
% 2.17/1.36  #Tautology    : 36
% 2.17/1.36  #SimpNegUnit  : 2
% 2.17/1.36  #BackRed      : 0
% 2.17/1.36  
% 2.17/1.36  #Partial instantiations: 0
% 2.17/1.36  #Strategies tried      : 1
% 2.17/1.36  
% 2.17/1.36  Timing (in seconds)
% 2.17/1.36  ----------------------
% 2.17/1.36  Preprocessing        : 0.28
% 2.17/1.36  Parsing              : 0.16
% 2.17/1.36  CNF conversion       : 0.02
% 2.17/1.36  Main loop            : 0.22
% 2.17/1.36  Inferencing          : 0.08
% 2.17/1.36  Reduction            : 0.07
% 2.17/1.36  Demodulation         : 0.05
% 2.17/1.36  BG Simplification    : 0.01
% 2.17/1.36  Subsumption          : 0.05
% 2.17/1.36  Abstraction          : 0.01
% 2.17/1.36  MUC search           : 0.00
% 2.17/1.36  Cooper               : 0.00
% 2.17/1.36  Total                : 0.52
% 2.17/1.36  Index Insertion      : 0.00
% 2.17/1.36  Index Deletion       : 0.00
% 2.17/1.36  Index Matching       : 0.00
% 2.17/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
