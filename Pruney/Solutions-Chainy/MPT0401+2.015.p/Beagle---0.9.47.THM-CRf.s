%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:40 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  46 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_14,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_6] : k3_tarski(k1_tarski(A_6)) = k2_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_49,plain,(
    ! [A_6] : k3_tarski(k1_tarski(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_18,plain,(
    r1_setfam_1('#skF_2',k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,k3_tarski(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k3_tarski(A_11),k3_tarski(B_12))
      | ~ r1_setfam_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(A_31,C_32)
      | ~ r1_tarski(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,(
    ! [A_46,B_47,A_48] :
      ( r1_tarski(A_46,k3_tarski(B_47))
      | ~ r1_tarski(A_46,k3_tarski(A_48))
      | ~ r1_setfam_1(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_181,plain,(
    ! [A_49,B_50,B_51] :
      ( r1_tarski(A_49,k3_tarski(B_50))
      | ~ r1_setfam_1(B_51,B_50)
      | ~ r2_hidden(A_49,B_51) ) ),
    inference(resolution,[status(thm)],[c_8,c_160])).

tff(c_183,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k3_tarski(k1_tarski('#skF_1')))
      | ~ r2_hidden(A_49,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_181])).

tff(c_186,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,'#skF_1')
      | ~ r2_hidden(A_52,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_183])).

tff(c_189,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_186])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.84/1.18  
% 1.84/1.18  %Foreground sorts:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Background operators:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Foreground operators:
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.18  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.84/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.18  
% 1.84/1.19  tff(f_53, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 1.84/1.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.84/1.19  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.84/1.19  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.84/1.19  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.84/1.19  tff(f_45, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 1.84/1.19  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.84/1.19  tff(c_14, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.19  tff(c_16, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.19  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.19  tff(c_6, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.19  tff(c_37, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.19  tff(c_46, plain, (![A_6]: (k3_tarski(k1_tarski(A_6))=k2_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_37])).
% 1.84/1.19  tff(c_49, plain, (![A_6]: (k3_tarski(k1_tarski(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 1.84/1.19  tff(c_18, plain, (r1_setfam_1('#skF_2', k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.19  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, k3_tarski(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.19  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k3_tarski(A_11), k3_tarski(B_12)) | ~r1_setfam_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.19  tff(c_95, plain, (![A_31, C_32, B_33]: (r1_tarski(A_31, C_32) | ~r1_tarski(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.19  tff(c_160, plain, (![A_46, B_47, A_48]: (r1_tarski(A_46, k3_tarski(B_47)) | ~r1_tarski(A_46, k3_tarski(A_48)) | ~r1_setfam_1(A_48, B_47))), inference(resolution, [status(thm)], [c_12, c_95])).
% 1.84/1.19  tff(c_181, plain, (![A_49, B_50, B_51]: (r1_tarski(A_49, k3_tarski(B_50)) | ~r1_setfam_1(B_51, B_50) | ~r2_hidden(A_49, B_51))), inference(resolution, [status(thm)], [c_8, c_160])).
% 1.84/1.19  tff(c_183, plain, (![A_49]: (r1_tarski(A_49, k3_tarski(k1_tarski('#skF_1'))) | ~r2_hidden(A_49, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_181])).
% 1.84/1.19  tff(c_186, plain, (![A_52]: (r1_tarski(A_52, '#skF_1') | ~r2_hidden(A_52, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_183])).
% 1.84/1.19  tff(c_189, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_186])).
% 1.84/1.19  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_189])).
% 1.84/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  Inference rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Ref     : 0
% 1.84/1.19  #Sup     : 47
% 1.84/1.19  #Fact    : 0
% 1.84/1.19  #Define  : 0
% 1.84/1.19  #Split   : 0
% 1.84/1.19  #Chain   : 0
% 1.84/1.19  #Close   : 0
% 1.84/1.19  
% 1.84/1.19  Ordering : KBO
% 1.84/1.19  
% 1.84/1.19  Simplification rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Subsume      : 4
% 1.84/1.19  #Demod        : 5
% 1.84/1.19  #Tautology    : 8
% 1.84/1.19  #SimpNegUnit  : 1
% 1.84/1.19  #BackRed      : 0
% 1.84/1.19  
% 1.84/1.19  #Partial instantiations: 0
% 1.84/1.19  #Strategies tried      : 1
% 1.84/1.19  
% 1.84/1.19  Timing (in seconds)
% 1.84/1.19  ----------------------
% 1.84/1.20  Preprocessing        : 0.27
% 1.84/1.20  Parsing              : 0.15
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.16
% 1.94/1.20  Inferencing          : 0.06
% 1.94/1.20  Reduction            : 0.04
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.03
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.45
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
