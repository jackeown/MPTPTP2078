%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:37 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  34 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_wellord2 > k1_setfam_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k1_wellord2(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k2_wellord1(k1_wellord2(B_14),A_13) = k1_wellord2(A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,k2_zfmisc_1(B_33,B_33)) = k2_wellord1(A_32,B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_53])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [B_26,A_27] : r1_tarski(k3_xboole_0(B_26,A_27),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_186,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k2_wellord1(A_38,B_39),k2_zfmisc_1(B_39,B_39))
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_106])).

tff(c_189,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_wellord2(A_13),k2_zfmisc_1(A_13,A_13))
      | ~ v1_relat_1(k1_wellord2(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_186])).

tff(c_192,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k1_wellord2(A_40),k2_zfmisc_1(A_40,A_40))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_209,plain,(
    ! [A_3] : r1_tarski(k1_wellord2(A_3),k2_zfmisc_1(A_3,A_3)) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_16,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.29  % Computer   : n025.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 11:42:50 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.01  
% 1.62/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.02  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_wellord2 > k1_setfam_1 > #skF_1
% 1.62/1.02  
% 1.62/1.02  %Foreground sorts:
% 1.62/1.02  
% 1.62/1.02  
% 1.62/1.02  %Background operators:
% 1.62/1.02  
% 1.62/1.02  
% 1.62/1.02  %Foreground operators:
% 1.62/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.02  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.62/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.62/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.02  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.62/1.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.62/1.02  
% 1.62/1.03  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.62/1.03  tff(f_40, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.62/1.03  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 1.62/1.03  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 1.62/1.03  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.62/1.03  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.62/1.03  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.62/1.03  tff(f_47, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 1.62/1.03  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.03  tff(c_12, plain, (![A_12]: (v1_relat_1(k1_wellord2(A_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.03  tff(c_14, plain, (![B_14, A_13]: (k2_wellord1(k1_wellord2(B_14), A_13)=k1_wellord2(A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.03  tff(c_150, plain, (![A_32, B_33]: (k3_xboole_0(A_32, k2_zfmisc_1(B_33, B_33))=k2_wellord1(A_32, B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.03  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.03  tff(c_53, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.03  tff(c_68, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_53])).
% 1.62/1.03  tff(c_8, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.03  tff(c_91, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_68, c_8])).
% 1.62/1.03  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.03  tff(c_106, plain, (![B_26, A_27]: (r1_tarski(k3_xboole_0(B_26, A_27), A_27))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 1.62/1.03  tff(c_186, plain, (![A_38, B_39]: (r1_tarski(k2_wellord1(A_38, B_39), k2_zfmisc_1(B_39, B_39)) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_150, c_106])).
% 1.62/1.03  tff(c_189, plain, (![A_13, B_14]: (r1_tarski(k1_wellord2(A_13), k2_zfmisc_1(A_13, A_13)) | ~v1_relat_1(k1_wellord2(B_14)) | ~r1_tarski(A_13, B_14))), inference(superposition, [status(thm), theory('equality')], [c_14, c_186])).
% 1.62/1.03  tff(c_192, plain, (![A_40, B_41]: (r1_tarski(k1_wellord2(A_40), k2_zfmisc_1(A_40, A_40)) | ~r1_tarski(A_40, B_41))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_189])).
% 1.62/1.03  tff(c_209, plain, (![A_3]: (r1_tarski(k1_wellord2(A_3), k2_zfmisc_1(A_3, A_3)))), inference(resolution, [status(thm)], [c_4, c_192])).
% 1.62/1.03  tff(c_16, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.03  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_16])).
% 1.62/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.03  
% 1.62/1.03  Inference rules
% 1.62/1.03  ----------------------
% 1.62/1.03  #Ref     : 0
% 1.62/1.03  #Sup     : 48
% 1.62/1.03  #Fact    : 0
% 1.62/1.03  #Define  : 0
% 1.62/1.03  #Split   : 0
% 1.62/1.03  #Chain   : 0
% 1.62/1.03  #Close   : 0
% 1.62/1.03  
% 1.62/1.03  Ordering : KBO
% 1.62/1.03  
% 1.62/1.03  Simplification rules
% 1.62/1.03  ----------------------
% 1.62/1.03  #Subsume      : 1
% 1.62/1.03  #Demod        : 10
% 1.62/1.03  #Tautology    : 31
% 1.62/1.03  #SimpNegUnit  : 0
% 1.62/1.03  #BackRed      : 1
% 1.62/1.03  
% 1.62/1.03  #Partial instantiations: 0
% 1.62/1.03  #Strategies tried      : 1
% 1.62/1.03  
% 1.62/1.03  Timing (in seconds)
% 1.62/1.03  ----------------------
% 1.62/1.04  Preprocessing        : 0.27
% 1.62/1.04  Parsing              : 0.14
% 1.62/1.04  CNF conversion       : 0.02
% 1.62/1.04  Main loop            : 0.16
% 1.62/1.04  Inferencing          : 0.06
% 1.62/1.04  Reduction            : 0.05
% 1.62/1.04  Demodulation         : 0.04
% 1.62/1.04  BG Simplification    : 0.01
% 1.62/1.04  Subsumption          : 0.03
% 1.62/1.04  Abstraction          : 0.01
% 1.62/1.04  MUC search           : 0.00
% 1.62/1.04  Cooper               : 0.00
% 1.62/1.04  Total                : 0.46
% 1.62/1.04  Index Insertion      : 0.00
% 1.62/1.04  Index Deletion       : 0.00
% 1.62/1.04  Index Matching       : 0.00
% 1.62/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
