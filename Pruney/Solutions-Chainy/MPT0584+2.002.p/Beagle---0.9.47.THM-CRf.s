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
% Statistics : Number of formulae       :   35 (  48 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  69 expanded)
%              Number of equality atoms :   19 (  36 expanded)
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
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_10,plain,(
    k7_relat_1('#skF_2','#skF_3') != k7_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_93,plain,(
    ! [C_23,A_24,B_25] :
      ( k7_relat_1(k7_relat_1(C_23,A_24),B_25) = k7_relat_1(C_23,k3_xboole_0(A_24,B_25))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [B_25] :
      ( k7_relat_1(k7_relat_1('#skF_1','#skF_4'),B_25) = k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_25))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_113,plain,(
    ! [B_26] : k7_relat_1(k7_relat_1('#skF_1','#skF_4'),B_26) = k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_108])).

tff(c_8,plain,(
    ! [C_9,A_7,B_8] :
      ( k7_relat_1(k7_relat_1(C_9,A_7),B_8) = k7_relat_1(C_9,k3_xboole_0(A_7,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [B_26] :
      ( k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_26)) = k7_relat_1('#skF_1',k3_xboole_0('#skF_4',B_26))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_186,plain,(
    ! [B_31] : k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_31)) = k7_relat_1('#skF_1',k3_xboole_0('#skF_4',B_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_122])).

tff(c_201,plain,(
    k7_relat_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) = k7_relat_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_186])).

tff(c_216,plain,(
    k7_relat_1('#skF_2','#skF_3') = k7_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_201])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.17  
% 1.87/1.18  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C, D]: ((r1_tarski(C, D) & (k7_relat_1(A, D) = k7_relat_1(B, D))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t188_relat_1)).
% 1.87/1.18  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.87/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.87/1.18  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.87/1.18  tff(c_10, plain, (k7_relat_1('#skF_2', '#skF_3')!=k7_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.18  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.18  tff(c_56, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_60, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_14, c_56])).
% 1.87/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.18  tff(c_64, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_60, c_2])).
% 1.87/1.18  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.18  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.18  tff(c_12, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.18  tff(c_93, plain, (![C_23, A_24, B_25]: (k7_relat_1(k7_relat_1(C_23, A_24), B_25)=k7_relat_1(C_23, k3_xboole_0(A_24, B_25)) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.18  tff(c_108, plain, (![B_25]: (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), B_25)=k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_25)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_93])).
% 1.87/1.18  tff(c_113, plain, (![B_26]: (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), B_26)=k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_108])).
% 1.87/1.18  tff(c_8, plain, (![C_9, A_7, B_8]: (k7_relat_1(k7_relat_1(C_9, A_7), B_8)=k7_relat_1(C_9, k3_xboole_0(A_7, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.18  tff(c_122, plain, (![B_26]: (k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_26))=k7_relat_1('#skF_1', k3_xboole_0('#skF_4', B_26)) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 1.87/1.18  tff(c_186, plain, (![B_31]: (k7_relat_1('#skF_2', k3_xboole_0('#skF_4', B_31))=k7_relat_1('#skF_1', k3_xboole_0('#skF_4', B_31)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_122])).
% 1.87/1.18  tff(c_201, plain, (k7_relat_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))=k7_relat_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64, c_186])).
% 1.87/1.18  tff(c_216, plain, (k7_relat_1('#skF_2', '#skF_3')=k7_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_201])).
% 1.87/1.18  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_216])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 51
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 0
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 0
% 1.87/1.18  #Demod        : 15
% 1.87/1.18  #Tautology    : 27
% 1.87/1.18  #SimpNegUnit  : 1
% 1.87/1.18  #BackRed      : 1
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.26
% 1.87/1.18  Parsing              : 0.14
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.16
% 1.87/1.18  Inferencing          : 0.06
% 1.87/1.18  Reduction            : 0.06
% 1.87/1.18  Demodulation         : 0.05
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.45
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
