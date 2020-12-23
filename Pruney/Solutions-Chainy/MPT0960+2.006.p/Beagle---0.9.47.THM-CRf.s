%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:37 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  34 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_wellord2 > k1_setfam_1 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

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

tff(f_29,axiom,(
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

tff(c_6,plain,(
    ! [A_5] : r1_tarski(A_5,k1_zfmisc_1(k3_tarski(A_5))) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_11] : v1_relat_1(k1_wellord2(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k2_wellord1(k1_wellord2(B_13),A_12) = k1_wellord2(A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,k2_zfmisc_1(B_31,B_31)) = k2_wellord1(A_30,B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [B_22,A_23] : k1_setfam_1(k2_tarski(B_22,A_23)) = k3_xboole_0(A_23,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_8,plain,(
    ! [A_6,B_7] : k1_setfam_1(k2_tarski(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [B_24,A_25] : r1_tarski(k3_xboole_0(B_24,A_25),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_186,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k2_wellord1(A_36,B_37),k2_zfmisc_1(B_37,B_37))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_106])).

tff(c_189,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_wellord2(A_12),k2_zfmisc_1(A_12,A_12))
      | ~ v1_relat_1(k1_wellord2(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_186])).

tff(c_192,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_wellord2(A_38),k2_zfmisc_1(A_38,A_38))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_209,plain,(
    ! [A_5] : r1_tarski(k1_wellord2(A_5),k2_zfmisc_1(A_5,A_5)) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_16,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:23:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.15  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_wellord2 > k1_setfam_1 > #skF_1
% 1.65/1.15  
% 1.65/1.15  %Foreground sorts:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Background operators:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Foreground operators:
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.15  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.65/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.65/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.15  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.65/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.65/1.15  
% 1.65/1.16  tff(f_31, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 1.65/1.16  tff(f_40, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.65/1.16  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 1.65/1.16  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 1.65/1.16  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.65/1.16  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.65/1.16  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.65/1.16  tff(f_47, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 1.65/1.16  tff(c_6, plain, (![A_5]: (r1_tarski(A_5, k1_zfmisc_1(k3_tarski(A_5))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.16  tff(c_12, plain, (![A_11]: (v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.65/1.16  tff(c_14, plain, (![B_13, A_12]: (k2_wellord1(k1_wellord2(B_13), A_12)=k1_wellord2(A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.16  tff(c_150, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k2_zfmisc_1(B_31, B_31))=k2_wellord1(A_30, B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.16  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.16  tff(c_53, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.16  tff(c_68, plain, (![B_22, A_23]: (k1_setfam_1(k2_tarski(B_22, A_23))=k3_xboole_0(A_23, B_22))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.65/1.16  tff(c_8, plain, (![A_6, B_7]: (k1_setfam_1(k2_tarski(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.16  tff(c_91, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_68, c_8])).
% 1.65/1.16  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.16  tff(c_106, plain, (![B_24, A_25]: (r1_tarski(k3_xboole_0(B_24, A_25), A_25))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 1.65/1.16  tff(c_186, plain, (![A_36, B_37]: (r1_tarski(k2_wellord1(A_36, B_37), k2_zfmisc_1(B_37, B_37)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_150, c_106])).
% 1.65/1.16  tff(c_189, plain, (![A_12, B_13]: (r1_tarski(k1_wellord2(A_12), k2_zfmisc_1(A_12, A_12)) | ~v1_relat_1(k1_wellord2(B_13)) | ~r1_tarski(A_12, B_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_186])).
% 1.65/1.16  tff(c_192, plain, (![A_38, B_39]: (r1_tarski(k1_wellord2(A_38), k2_zfmisc_1(A_38, A_38)) | ~r1_tarski(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_189])).
% 1.65/1.16  tff(c_209, plain, (![A_5]: (r1_tarski(k1_wellord2(A_5), k2_zfmisc_1(A_5, A_5)))), inference(resolution, [status(thm)], [c_6, c_192])).
% 1.65/1.16  tff(c_16, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.16  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_16])).
% 1.65/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  Inference rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Ref     : 0
% 1.65/1.16  #Sup     : 48
% 1.65/1.16  #Fact    : 0
% 1.65/1.16  #Define  : 0
% 1.65/1.16  #Split   : 0
% 1.65/1.16  #Chain   : 0
% 1.65/1.16  #Close   : 0
% 1.65/1.16  
% 1.65/1.16  Ordering : KBO
% 1.65/1.16  
% 1.65/1.16  Simplification rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Subsume      : 1
% 1.65/1.16  #Demod        : 10
% 1.65/1.16  #Tautology    : 31
% 1.65/1.16  #SimpNegUnit  : 0
% 1.65/1.16  #BackRed      : 1
% 1.65/1.16  
% 1.65/1.16  #Partial instantiations: 0
% 1.65/1.16  #Strategies tried      : 1
% 1.65/1.16  
% 1.65/1.16  Timing (in seconds)
% 1.65/1.16  ----------------------
% 1.65/1.16  Preprocessing        : 0.25
% 1.65/1.16  Parsing              : 0.14
% 1.65/1.16  CNF conversion       : 0.01
% 1.65/1.16  Main loop            : 0.14
% 1.65/1.16  Inferencing          : 0.05
% 1.65/1.16  Reduction            : 0.05
% 1.65/1.16  Demodulation         : 0.04
% 1.65/1.16  BG Simplification    : 0.01
% 1.65/1.16  Subsumption          : 0.02
% 1.65/1.16  Abstraction          : 0.01
% 1.65/1.16  MUC search           : 0.00
% 1.65/1.16  Cooper               : 0.00
% 1.65/1.16  Total                : 0.42
% 1.65/1.16  Index Insertion      : 0.00
% 1.65/1.16  Index Deletion       : 0.00
% 1.65/1.16  Index Matching       : 0.00
% 1.65/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
