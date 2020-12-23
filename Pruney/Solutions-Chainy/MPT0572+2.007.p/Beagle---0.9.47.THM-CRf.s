%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:49 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   39 (  56 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  67 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_186,plain,(
    ! [C_35,A_36,B_37] :
      ( k2_xboole_0(k10_relat_1(C_35,A_36),k10_relat_1(C_35,B_37)) = k10_relat_1(C_35,k2_xboole_0(A_36,B_37))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_17,A_18] : k2_xboole_0(B_17,A_18) = k2_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_33,plain,(
    ! [A_18,B_17] : r1_tarski(A_18,k2_xboole_0(B_17,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_10])).

tff(c_231,plain,(
    ! [C_41,B_42,A_43] :
      ( r1_tarski(k10_relat_1(C_41,B_42),k10_relat_1(C_41,k2_xboole_0(A_43,B_42)))
      | ~ v1_relat_1(C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_33])).

tff(c_310,plain,(
    ! [C_53,B_54,A_55] :
      ( r1_tarski(k10_relat_1(C_53,k3_xboole_0(B_54,A_55)),k10_relat_1(C_53,A_55))
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_231])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_248,plain,(
    ! [C_44,A_45,B_46] :
      ( r1_tarski(k10_relat_1(C_44,k3_xboole_0(A_45,B_46)),k10_relat_1(C_44,A_45))
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_231])).

tff(c_175,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(A_32,k3_xboole_0(B_33,C_34))
      | ~ r1_tarski(A_32,C_34)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_175,c_14])).

tff(c_247,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_251,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_248,c_247])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_251])).

tff(c_262,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_313,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_262])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.09/1.24  
% 2.09/1.24  %Foreground sorts:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Background operators:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Foreground operators:
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.24  
% 2.09/1.25  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_relat_1)).
% 2.09/1.25  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.09/1.25  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.09/1.25  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.09/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.09/1.25  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.09/1.25  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.09/1.25  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.25  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.25  tff(c_100, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k3_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.25  tff(c_115, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_100])).
% 2.09/1.25  tff(c_186, plain, (![C_35, A_36, B_37]: (k2_xboole_0(k10_relat_1(C_35, A_36), k10_relat_1(C_35, B_37))=k10_relat_1(C_35, k2_xboole_0(A_36, B_37)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.25  tff(c_18, plain, (![B_17, A_18]: (k2_xboole_0(B_17, A_18)=k2_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.25  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.25  tff(c_33, plain, (![A_18, B_17]: (r1_tarski(A_18, k2_xboole_0(B_17, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_10])).
% 2.09/1.25  tff(c_231, plain, (![C_41, B_42, A_43]: (r1_tarski(k10_relat_1(C_41, B_42), k10_relat_1(C_41, k2_xboole_0(A_43, B_42))) | ~v1_relat_1(C_41))), inference(superposition, [status(thm), theory('equality')], [c_186, c_33])).
% 2.09/1.25  tff(c_310, plain, (![C_53, B_54, A_55]: (r1_tarski(k10_relat_1(C_53, k3_xboole_0(B_54, A_55)), k10_relat_1(C_53, A_55)) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_115, c_231])).
% 2.09/1.25  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.25  tff(c_248, plain, (![C_44, A_45, B_46]: (r1_tarski(k10_relat_1(C_44, k3_xboole_0(A_45, B_46)), k10_relat_1(C_44, A_45)) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_8, c_231])).
% 2.09/1.25  tff(c_175, plain, (![A_32, B_33, C_34]: (r1_tarski(A_32, k3_xboole_0(B_33, C_34)) | ~r1_tarski(A_32, C_34) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.25  tff(c_14, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.25  tff(c_185, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_175, c_14])).
% 2.09/1.25  tff(c_247, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_185])).
% 2.09/1.25  tff(c_251, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_248, c_247])).
% 2.09/1.25  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_251])).
% 2.09/1.25  tff(c_262, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_185])).
% 2.09/1.25  tff(c_313, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_262])).
% 2.09/1.25  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_313])).
% 2.09/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  Inference rules
% 2.09/1.25  ----------------------
% 2.09/1.25  #Ref     : 0
% 2.09/1.25  #Sup     : 79
% 2.09/1.25  #Fact    : 0
% 2.09/1.25  #Define  : 0
% 2.09/1.25  #Split   : 1
% 2.09/1.25  #Chain   : 0
% 2.09/1.25  #Close   : 0
% 2.09/1.25  
% 2.09/1.25  Ordering : KBO
% 2.09/1.25  
% 2.09/1.25  Simplification rules
% 2.09/1.25  ----------------------
% 2.09/1.25  #Subsume      : 13
% 2.09/1.25  #Demod        : 15
% 2.09/1.25  #Tautology    : 39
% 2.09/1.25  #SimpNegUnit  : 0
% 2.09/1.25  #BackRed      : 0
% 2.09/1.25  
% 2.09/1.25  #Partial instantiations: 0
% 2.09/1.25  #Strategies tried      : 1
% 2.09/1.25  
% 2.09/1.25  Timing (in seconds)
% 2.09/1.25  ----------------------
% 2.09/1.25  Preprocessing        : 0.26
% 2.09/1.25  Parsing              : 0.15
% 2.09/1.25  CNF conversion       : 0.02
% 2.09/1.25  Main loop            : 0.21
% 2.09/1.25  Inferencing          : 0.08
% 2.09/1.25  Reduction            : 0.08
% 2.09/1.25  Demodulation         : 0.06
% 2.09/1.25  BG Simplification    : 0.01
% 2.09/1.25  Subsumption          : 0.04
% 2.09/1.25  Abstraction          : 0.01
% 2.09/1.25  MUC search           : 0.00
% 2.09/1.25  Cooper               : 0.00
% 2.09/1.25  Total                : 0.50
% 2.09/1.25  Index Insertion      : 0.00
% 2.09/1.25  Index Deletion       : 0.00
% 2.09/1.25  Index Matching       : 0.00
% 2.09/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
