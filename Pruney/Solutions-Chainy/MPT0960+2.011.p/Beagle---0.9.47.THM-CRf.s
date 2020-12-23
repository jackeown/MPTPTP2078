%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :    6 (   6 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

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

tff(c_87,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,k2_zfmisc_1(B_27,B_27)) = k2_wellord1(A_26,B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [B_18,A_19] : k3_xboole_0(B_18,A_19) = k3_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [B_18,A_19] : r1_tarski(k3_xboole_0(B_18,A_19),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_123,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k2_wellord1(A_32,B_33),k2_zfmisc_1(B_33,B_33))
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_35])).

tff(c_126,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_wellord2(A_12),k2_zfmisc_1(A_12,A_12))
      | ~ v1_relat_1(k1_wellord2(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_129,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_wellord2(A_34),k2_zfmisc_1(A_34,A_34))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_147,plain,(
    ! [A_5] : r1_tarski(k1_wellord2(A_5),k2_zfmisc_1(A_5,A_5)) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_16,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.17  
% 1.75/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.17  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_wellord2 > k1_setfam_1 > #skF_1
% 1.75/1.17  
% 1.75/1.17  %Foreground sorts:
% 1.75/1.17  
% 1.75/1.17  
% 1.75/1.17  %Background operators:
% 1.75/1.17  
% 1.75/1.17  
% 1.75/1.17  %Foreground operators:
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.17  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.75/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.75/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.17  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.75/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.75/1.17  
% 1.75/1.18  tff(f_31, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 1.75/1.18  tff(f_40, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.75/1.18  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 1.75/1.18  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 1.75/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.75/1.18  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.75/1.18  tff(f_47, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 1.75/1.18  tff(c_6, plain, (![A_5]: (r1_tarski(A_5, k1_zfmisc_1(k3_tarski(A_5))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.75/1.18  tff(c_12, plain, (![A_11]: (v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.75/1.18  tff(c_14, plain, (![B_13, A_12]: (k2_wellord1(k1_wellord2(B_13), A_12)=k1_wellord2(A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.75/1.18  tff(c_87, plain, (![A_26, B_27]: (k3_xboole_0(A_26, k2_zfmisc_1(B_27, B_27))=k2_wellord1(A_26, B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.75/1.18  tff(c_20, plain, (![B_18, A_19]: (k3_xboole_0(B_18, A_19)=k3_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.18  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.18  tff(c_35, plain, (![B_18, A_19]: (r1_tarski(k3_xboole_0(B_18, A_19), A_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4])).
% 1.75/1.18  tff(c_123, plain, (![A_32, B_33]: (r1_tarski(k2_wellord1(A_32, B_33), k2_zfmisc_1(B_33, B_33)) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_87, c_35])).
% 1.75/1.18  tff(c_126, plain, (![A_12, B_13]: (r1_tarski(k1_wellord2(A_12), k2_zfmisc_1(A_12, A_12)) | ~v1_relat_1(k1_wellord2(B_13)) | ~r1_tarski(A_12, B_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 1.75/1.18  tff(c_129, plain, (![A_34, B_35]: (r1_tarski(k1_wellord2(A_34), k2_zfmisc_1(A_34, A_34)) | ~r1_tarski(A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_126])).
% 1.75/1.18  tff(c_147, plain, (![A_5]: (r1_tarski(k1_wellord2(A_5), k2_zfmisc_1(A_5, A_5)))), inference(resolution, [status(thm)], [c_6, c_129])).
% 1.75/1.18  tff(c_16, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.75/1.18  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_16])).
% 1.75/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.18  
% 1.75/1.18  Inference rules
% 1.75/1.18  ----------------------
% 1.75/1.18  #Ref     : 0
% 1.75/1.18  #Sup     : 32
% 1.75/1.18  #Fact    : 0
% 1.75/1.18  #Define  : 0
% 1.86/1.18  #Split   : 0
% 1.86/1.18  #Chain   : 0
% 1.86/1.18  #Close   : 0
% 1.86/1.18  
% 1.86/1.18  Ordering : KBO
% 1.86/1.18  
% 1.86/1.18  Simplification rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Subsume      : 0
% 1.86/1.18  #Demod        : 7
% 1.86/1.18  #Tautology    : 18
% 1.86/1.18  #SimpNegUnit  : 0
% 1.86/1.18  #BackRed      : 1
% 1.86/1.18  
% 1.86/1.18  #Partial instantiations: 0
% 1.86/1.18  #Strategies tried      : 1
% 1.86/1.18  
% 1.86/1.18  Timing (in seconds)
% 1.86/1.18  ----------------------
% 1.86/1.19  Preprocessing        : 0.26
% 1.86/1.19  Parsing              : 0.15
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.12
% 1.86/1.19  Inferencing          : 0.05
% 1.86/1.19  Reduction            : 0.04
% 1.86/1.19  Demodulation         : 0.03
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.02
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.42
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
