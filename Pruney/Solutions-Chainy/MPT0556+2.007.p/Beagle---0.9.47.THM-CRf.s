%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:06 EST 2020

% Result     : Theorem 12.35s
% Output     : CNFRefutation 12.35s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  75 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [C_10,A_8,B_9] :
      ( r1_tarski(k9_relat_1(C_10,A_8),k9_relat_1(C_10,B_9))
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    ! [B_32,A_33,C_34] :
      ( r1_tarski(k9_relat_1(B_32,A_33),k9_relat_1(C_34,A_33))
      | ~ r1_tarski(B_32,C_34)
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_374,plain,(
    ! [B_53,A_54,C_55] :
      ( k2_xboole_0(k9_relat_1(B_53,A_54),k9_relat_1(C_55,A_54)) = k9_relat_1(C_55,A_54)
      | ~ r1_tarski(B_53,C_55)
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_142,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,k2_xboole_0(C_21,B_22))
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_20,B_2,A_1] :
      ( r1_tarski(A_20,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_20,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_4389,plain,(
    ! [A_165,C_166,A_167,B_168] :
      ( r1_tarski(A_165,k9_relat_1(C_166,A_167))
      | ~ r1_tarski(A_165,k9_relat_1(B_168,A_167))
      | ~ r1_tarski(B_168,C_166)
      | ~ v1_relat_1(C_166)
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_105])).

tff(c_21062,plain,(
    ! [C_539,A_540,C_541,B_542] :
      ( r1_tarski(k9_relat_1(C_539,A_540),k9_relat_1(C_541,B_542))
      | ~ r1_tarski(C_539,C_541)
      | ~ v1_relat_1(C_541)
      | ~ r1_tarski(A_540,B_542)
      | ~ v1_relat_1(C_539) ) ),
    inference(resolution,[status(thm)],[c_8,c_4389])).

tff(c_12,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_21116,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_21062,c_12])).

tff(c_21145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_18,c_16,c_21116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.35/4.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.35/4.92  
% 12.35/4.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.35/4.92  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.35/4.92  
% 12.35/4.92  %Foreground sorts:
% 12.35/4.92  
% 12.35/4.92  
% 12.35/4.92  %Background operators:
% 12.35/4.92  
% 12.35/4.92  
% 12.35/4.92  %Foreground operators:
% 12.35/4.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.35/4.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.35/4.92  tff('#skF_2', type, '#skF_2': $i).
% 12.35/4.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.35/4.92  tff('#skF_3', type, '#skF_3': $i).
% 12.35/4.92  tff('#skF_1', type, '#skF_1': $i).
% 12.35/4.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.35/4.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.35/4.92  tff('#skF_4', type, '#skF_4': $i).
% 12.35/4.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.35/4.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.35/4.92  
% 12.35/4.93  tff(f_62, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 12.35/4.93  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 12.35/4.93  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 12.35/4.93  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.35/4.93  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.35/4.93  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 12.35/4.93  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.35/4.93  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.35/4.93  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.35/4.93  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.35/4.93  tff(c_8, plain, (![C_10, A_8, B_9]: (r1_tarski(k9_relat_1(C_10, A_8), k9_relat_1(C_10, B_9)) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.35/4.93  tff(c_142, plain, (![B_32, A_33, C_34]: (r1_tarski(k9_relat_1(B_32, A_33), k9_relat_1(C_34, A_33)) | ~r1_tarski(B_32, C_34) | ~v1_relat_1(C_34) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.35/4.93  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.35/4.93  tff(c_374, plain, (![B_53, A_54, C_55]: (k2_xboole_0(k9_relat_1(B_53, A_54), k9_relat_1(C_55, A_54))=k9_relat_1(C_55, A_54) | ~r1_tarski(B_53, C_55) | ~v1_relat_1(C_55) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_142, c_6])).
% 12.35/4.93  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.35/4.93  tff(c_90, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, k2_xboole_0(C_21, B_22)) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.35/4.93  tff(c_105, plain, (![A_20, B_2, A_1]: (r1_tarski(A_20, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_20, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 12.35/4.93  tff(c_4389, plain, (![A_165, C_166, A_167, B_168]: (r1_tarski(A_165, k9_relat_1(C_166, A_167)) | ~r1_tarski(A_165, k9_relat_1(B_168, A_167)) | ~r1_tarski(B_168, C_166) | ~v1_relat_1(C_166) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_374, c_105])).
% 12.35/4.93  tff(c_21062, plain, (![C_539, A_540, C_541, B_542]: (r1_tarski(k9_relat_1(C_539, A_540), k9_relat_1(C_541, B_542)) | ~r1_tarski(C_539, C_541) | ~v1_relat_1(C_541) | ~r1_tarski(A_540, B_542) | ~v1_relat_1(C_539))), inference(resolution, [status(thm)], [c_8, c_4389])).
% 12.35/4.93  tff(c_12, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.35/4.93  tff(c_21116, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_21062, c_12])).
% 12.35/4.93  tff(c_21145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_18, c_16, c_21116])).
% 12.35/4.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.35/4.93  
% 12.35/4.93  Inference rules
% 12.35/4.93  ----------------------
% 12.35/4.93  #Ref     : 0
% 12.35/4.93  #Sup     : 6972
% 12.35/4.93  #Fact    : 0
% 12.35/4.93  #Define  : 0
% 12.35/4.93  #Split   : 9
% 12.35/4.93  #Chain   : 0
% 12.35/4.93  #Close   : 0
% 12.35/4.93  
% 12.35/4.93  Ordering : KBO
% 12.35/4.93  
% 12.35/4.93  Simplification rules
% 12.35/4.93  ----------------------
% 12.35/4.93  #Subsume      : 3131
% 12.35/4.93  #Demod        : 972
% 12.35/4.93  #Tautology    : 242
% 12.35/4.93  #SimpNegUnit  : 0
% 12.35/4.93  #BackRed      : 0
% 12.35/4.93  
% 12.35/4.93  #Partial instantiations: 0
% 12.35/4.93  #Strategies tried      : 1
% 12.35/4.93  
% 12.35/4.93  Timing (in seconds)
% 12.35/4.93  ----------------------
% 12.35/4.93  Preprocessing        : 0.29
% 12.35/4.93  Parsing              : 0.16
% 12.35/4.93  CNF conversion       : 0.02
% 12.35/4.93  Main loop            : 3.79
% 12.35/4.93  Inferencing          : 0.71
% 12.35/4.93  Reduction            : 1.07
% 12.35/4.93  Demodulation         : 0.83
% 12.35/4.93  BG Simplification    : 0.12
% 12.35/4.93  Subsumption          : 1.68
% 12.35/4.93  Abstraction          : 0.13
% 12.35/4.93  MUC search           : 0.00
% 12.35/4.93  Cooper               : 0.00
% 12.35/4.93  Total                : 4.10
% 12.35/4.93  Index Insertion      : 0.00
% 12.35/4.93  Index Deletion       : 0.00
% 12.35/4.93  Index Matching       : 0.00
% 12.35/4.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
