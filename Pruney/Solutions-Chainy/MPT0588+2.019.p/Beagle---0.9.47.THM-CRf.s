%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  46 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k7_relat_1(A_36,B_37))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [B_64,A_65] :
      ( k3_xboole_0(k1_relat_1(B_64),A_65) = k1_relat_1(k7_relat_1(B_64,A_65))
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_68,A_69)),k1_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_4])).

tff(c_28,plain,(
    ! [B_44,A_43] :
      ( k7_relat_1(B_44,A_43) = B_44
      | ~ r1_tarski(k1_relat_1(B_44),A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1622,plain,(
    ! [B_146,A_147] :
      ( k7_relat_1(k7_relat_1(B_146,A_147),k1_relat_1(B_146)) = k7_relat_1(B_146,A_147)
      | ~ v1_relat_1(k7_relat_1(B_146,A_147))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_162,c_28])).

tff(c_24,plain,(
    ! [C_40,A_38,B_39] :
      ( k7_relat_1(k7_relat_1(C_40,A_38),B_39) = k7_relat_1(C_40,k3_xboole_0(A_38,B_39))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6640,plain,(
    ! [B_225,A_226] :
      ( k7_relat_1(B_225,k3_xboole_0(A_226,k1_relat_1(B_225))) = k7_relat_1(B_225,A_226)
      | ~ v1_relat_1(B_225)
      | ~ v1_relat_1(k7_relat_1(B_225,A_226))
      | ~ v1_relat_1(B_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1622,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_33,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_6790,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6640,c_33])).

tff(c_6858,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6790])).

tff(c_6863,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_6858])).

tff(c_6867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.53  
% 7.51/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.53  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.51/2.53  
% 7.51/2.53  %Foreground sorts:
% 7.51/2.53  
% 7.51/2.53  
% 7.51/2.53  %Background operators:
% 7.51/2.53  
% 7.51/2.53  
% 7.51/2.53  %Foreground operators:
% 7.51/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.51/2.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.51/2.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.51/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.51/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.51/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.51/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.51/2.53  tff('#skF_1', type, '#skF_1': $i).
% 7.51/2.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.51/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.51/2.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.51/2.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.51/2.53  
% 7.51/2.54  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 7.51/2.54  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.51/2.54  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 7.51/2.54  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.51/2.54  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 7.51/2.54  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 7.51/2.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.51/2.54  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.51/2.54  tff(c_22, plain, (![A_36, B_37]: (v1_relat_1(k7_relat_1(A_36, B_37)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.51/2.54  tff(c_128, plain, (![B_64, A_65]: (k3_xboole_0(k1_relat_1(B_64), A_65)=k1_relat_1(k7_relat_1(B_64, A_65)) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.51/2.54  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.51/2.54  tff(c_162, plain, (![B_68, A_69]: (r1_tarski(k1_relat_1(k7_relat_1(B_68, A_69)), k1_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_128, c_4])).
% 7.51/2.54  tff(c_28, plain, (![B_44, A_43]: (k7_relat_1(B_44, A_43)=B_44 | ~r1_tarski(k1_relat_1(B_44), A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.51/2.54  tff(c_1622, plain, (![B_146, A_147]: (k7_relat_1(k7_relat_1(B_146, A_147), k1_relat_1(B_146))=k7_relat_1(B_146, A_147) | ~v1_relat_1(k7_relat_1(B_146, A_147)) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_162, c_28])).
% 7.51/2.54  tff(c_24, plain, (![C_40, A_38, B_39]: (k7_relat_1(k7_relat_1(C_40, A_38), B_39)=k7_relat_1(C_40, k3_xboole_0(A_38, B_39)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.51/2.54  tff(c_6640, plain, (![B_225, A_226]: (k7_relat_1(B_225, k3_xboole_0(A_226, k1_relat_1(B_225)))=k7_relat_1(B_225, A_226) | ~v1_relat_1(B_225) | ~v1_relat_1(k7_relat_1(B_225, A_226)) | ~v1_relat_1(B_225))), inference(superposition, [status(thm), theory('equality')], [c_1622, c_24])).
% 7.51/2.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.51/2.54  tff(c_30, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.51/2.54  tff(c_33, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 7.51/2.54  tff(c_6790, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6640, c_33])).
% 7.51/2.54  tff(c_6858, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6790])).
% 7.51/2.54  tff(c_6863, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_6858])).
% 7.51/2.54  tff(c_6867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_6863])).
% 7.51/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.54  
% 7.51/2.54  Inference rules
% 7.51/2.54  ----------------------
% 7.51/2.54  #Ref     : 0
% 7.51/2.54  #Sup     : 1867
% 7.51/2.54  #Fact    : 0
% 7.51/2.54  #Define  : 0
% 7.51/2.54  #Split   : 0
% 7.51/2.54  #Chain   : 0
% 7.51/2.54  #Close   : 0
% 7.51/2.54  
% 7.51/2.54  Ordering : KBO
% 7.51/2.54  
% 7.51/2.54  Simplification rules
% 7.51/2.54  ----------------------
% 7.51/2.54  #Subsume      : 223
% 7.51/2.54  #Demod        : 633
% 7.51/2.54  #Tautology    : 307
% 7.51/2.54  #SimpNegUnit  : 0
% 7.51/2.54  #BackRed      : 0
% 7.51/2.54  
% 7.51/2.54  #Partial instantiations: 0
% 7.51/2.54  #Strategies tried      : 1
% 7.51/2.54  
% 7.51/2.54  Timing (in seconds)
% 7.51/2.54  ----------------------
% 7.51/2.54  Preprocessing        : 0.32
% 7.51/2.54  Parsing              : 0.17
% 7.51/2.54  CNF conversion       : 0.02
% 7.51/2.54  Main loop            : 1.47
% 7.51/2.54  Inferencing          : 0.42
% 7.51/2.54  Reduction            : 0.60
% 7.51/2.54  Demodulation         : 0.50
% 7.51/2.54  BG Simplification    : 0.07
% 7.51/2.54  Subsumption          : 0.31
% 7.51/2.54  Abstraction          : 0.08
% 7.51/2.54  MUC search           : 0.00
% 7.51/2.54  Cooper               : 0.00
% 7.51/2.54  Total                : 1.81
% 7.51/2.54  Index Insertion      : 0.00
% 7.51/2.54  Index Deletion       : 0.00
% 7.51/2.54  Index Matching       : 0.00
% 7.51/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
