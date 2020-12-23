%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:00 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   40 (  60 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  81 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C,D] :
                ( ( r1_tarski(C,D)
                  & k7_relat_1(A,D) = k7_relat_1(B,D) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_10,plain,(
    k7_relat_1('#skF_2','#skF_3') != k7_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [B_26,A_27] : k1_setfam_1(k2_tarski(B_26,A_27)) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_65])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_6])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_138,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_60])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [C_23,A_24,B_25] :
      ( k7_relat_1(k7_relat_1(C_23,A_24),B_25) = k7_relat_1(C_23,k3_xboole_0(A_24,B_25))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [B_25] :
      ( k7_relat_1(k7_relat_1('#skF_1','#skF_4'),B_25) = k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_25))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_176,plain,(
    ! [B_30] : k7_relat_1(k7_relat_1('#skF_1','#skF_4'),B_30) = k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_8,plain,(
    ! [C_9,A_7,B_8] :
      ( k7_relat_1(k7_relat_1(C_9,A_7),B_8) = k7_relat_1(C_9,k3_xboole_0(A_7,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_185,plain,(
    ! [B_30] :
      ( k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_30)) = k7_relat_1('#skF_1',k3_xboole_0('#skF_4',B_30))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_8])).

tff(c_201,plain,(
    ! [B_31] : k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_31)) = k7_relat_1('#skF_1',k3_xboole_0('#skF_4',B_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_185])).

tff(c_213,plain,(
    k7_relat_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) = k7_relat_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_201])).

tff(c_226,plain,(
    k7_relat_1('#skF_2','#skF_3') = k7_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_213])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.20  
% 1.87/1.20  %Foreground sorts:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Background operators:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Foreground operators:
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.20  
% 1.87/1.21  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C, D]: ((r1_tarski(C, D) & (k7_relat_1(A, D) = k7_relat_1(B, D))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t188_relat_1)).
% 1.87/1.21  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.87/1.21  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.87/1.21  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.87/1.21  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.87/1.21  tff(c_10, plain, (k7_relat_1('#skF_2', '#skF_3')!=k7_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.21  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.21  tff(c_65, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.21  tff(c_100, plain, (![B_26, A_27]: (k1_setfam_1(k2_tarski(B_26, A_27))=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_65])).
% 1.87/1.21  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.21  tff(c_123, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_100, c_6])).
% 1.87/1.21  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.21  tff(c_56, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.21  tff(c_60, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_14, c_56])).
% 1.87/1.21  tff(c_138, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_123, c_60])).
% 1.87/1.21  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.21  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.21  tff(c_12, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.21  tff(c_80, plain, (![C_23, A_24, B_25]: (k7_relat_1(k7_relat_1(C_23, A_24), B_25)=k7_relat_1(C_23, k3_xboole_0(A_24, B_25)) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.21  tff(c_95, plain, (![B_25]: (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), B_25)=k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_25)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 1.87/1.21  tff(c_176, plain, (![B_30]: (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), B_30)=k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_95])).
% 1.87/1.21  tff(c_8, plain, (![C_9, A_7, B_8]: (k7_relat_1(k7_relat_1(C_9, A_7), B_8)=k7_relat_1(C_9, k3_xboole_0(A_7, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.21  tff(c_185, plain, (![B_30]: (k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_30))=k7_relat_1('#skF_1', k3_xboole_0('#skF_4', B_30)) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_8])).
% 1.87/1.21  tff(c_201, plain, (![B_31]: (k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_31))=k7_relat_1('#skF_1', k3_xboole_0('#skF_4', B_31)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_185])).
% 1.87/1.21  tff(c_213, plain, (k7_relat_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))=k7_relat_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_138, c_201])).
% 1.87/1.21  tff(c_226, plain, (k7_relat_1('#skF_2', '#skF_3')=k7_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_213])).
% 1.87/1.21  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_226])).
% 1.87/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  Inference rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Ref     : 0
% 1.87/1.21  #Sup     : 53
% 1.87/1.21  #Fact    : 0
% 1.87/1.21  #Define  : 0
% 1.87/1.21  #Split   : 0
% 1.87/1.21  #Chain   : 0
% 1.87/1.21  #Close   : 0
% 1.87/1.21  
% 1.87/1.21  Ordering : KBO
% 1.87/1.21  
% 1.87/1.21  Simplification rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Subsume      : 1
% 1.87/1.21  #Demod        : 13
% 1.87/1.21  #Tautology    : 38
% 1.87/1.21  #SimpNegUnit  : 1
% 1.87/1.21  #BackRed      : 1
% 1.87/1.21  
% 1.87/1.21  #Partial instantiations: 0
% 1.87/1.21  #Strategies tried      : 1
% 1.87/1.21  
% 1.87/1.21  Timing (in seconds)
% 1.87/1.21  ----------------------
% 1.87/1.21  Preprocessing        : 0.27
% 1.87/1.21  Parsing              : 0.15
% 1.87/1.21  CNF conversion       : 0.02
% 1.87/1.21  Main loop            : 0.16
% 1.87/1.21  Inferencing          : 0.06
% 1.87/1.21  Reduction            : 0.06
% 1.87/1.21  Demodulation         : 0.05
% 1.87/1.21  BG Simplification    : 0.01
% 1.87/1.21  Subsumption          : 0.02
% 1.87/1.21  Abstraction          : 0.01
% 1.87/1.21  MUC search           : 0.00
% 1.87/1.21  Cooper               : 0.00
% 1.87/1.21  Total                : 0.46
% 1.87/1.21  Index Insertion      : 0.00
% 1.87/1.21  Index Deletion       : 0.00
% 1.87/1.21  Index Matching       : 0.00
% 1.87/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
