%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_10] : v1_relat_1(k1_wellord2(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k2_wellord1(k1_wellord2(B_12),A_11) = k1_wellord2(A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,k2_zfmisc_1(B_26,B_26)) = k2_wellord1(A_25,B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(k2_zfmisc_1(B_37,B_37),A_38) = k2_wellord1(A_38,B_37)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_212,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k2_wellord1(A_39,B_40),k2_zfmisc_1(B_40,B_40))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_10])).

tff(c_217,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_wellord2(A_11),k2_zfmisc_1(A_11,A_11))
      | ~ v1_relat_1(k1_wellord2(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_234,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_wellord2(A_43),k2_zfmisc_1(A_43,A_43))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_217])).

tff(c_252,plain,(
    ! [B_4] : r1_tarski(k1_wellord2(B_4),k2_zfmisc_1(B_4,B_4)) ),
    inference(resolution,[status(thm)],[c_8,c_234])).

tff(c_18,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.24  
% 1.89/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_1
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.08/1.25  
% 2.08/1.26  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.26  tff(f_42, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.08/1.26  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.08/1.26  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 2.08/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.08/1.26  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.08/1.26  tff(f_49, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.08/1.26  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.26  tff(c_14, plain, (![A_10]: (v1_relat_1(k1_wellord2(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.26  tff(c_16, plain, (![B_12, A_11]: (k2_wellord1(k1_wellord2(B_12), A_11)=k1_wellord2(A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.26  tff(c_94, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k2_zfmisc_1(B_26, B_26))=k2_wellord1(A_25, B_26) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.26  tff(c_166, plain, (![B_37, A_38]: (k3_xboole_0(k2_zfmisc_1(B_37, B_37), A_38)=k2_wellord1(A_38, B_37) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_94, c_2])).
% 2.08/1.26  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.26  tff(c_212, plain, (![A_39, B_40]: (r1_tarski(k2_wellord1(A_39, B_40), k2_zfmisc_1(B_40, B_40)) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_166, c_10])).
% 2.08/1.26  tff(c_217, plain, (![A_11, B_12]: (r1_tarski(k1_wellord2(A_11), k2_zfmisc_1(A_11, A_11)) | ~v1_relat_1(k1_wellord2(B_12)) | ~r1_tarski(A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_212])).
% 2.08/1.26  tff(c_234, plain, (![A_43, B_44]: (r1_tarski(k1_wellord2(A_43), k2_zfmisc_1(A_43, A_43)) | ~r1_tarski(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_217])).
% 2.08/1.26  tff(c_252, plain, (![B_4]: (r1_tarski(k1_wellord2(B_4), k2_zfmisc_1(B_4, B_4)))), inference(resolution, [status(thm)], [c_8, c_234])).
% 2.08/1.26  tff(c_18, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.26  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_18])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 62
% 2.08/1.26  #Fact    : 0
% 2.08/1.26  #Define  : 0
% 2.08/1.26  #Split   : 0
% 2.08/1.26  #Chain   : 0
% 2.08/1.26  #Close   : 0
% 2.08/1.26  
% 2.08/1.26  Ordering : KBO
% 2.08/1.26  
% 2.08/1.26  Simplification rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Subsume      : 12
% 2.08/1.26  #Demod        : 9
% 2.08/1.26  #Tautology    : 20
% 2.08/1.26  #SimpNegUnit  : 0
% 2.08/1.26  #BackRed      : 1
% 2.08/1.26  
% 2.08/1.26  #Partial instantiations: 0
% 2.08/1.26  #Strategies tried      : 1
% 2.08/1.26  
% 2.08/1.26  Timing (in seconds)
% 2.08/1.26  ----------------------
% 2.08/1.27  Preprocessing        : 0.26
% 2.08/1.27  Parsing              : 0.14
% 2.08/1.27  CNF conversion       : 0.02
% 2.08/1.27  Main loop            : 0.19
% 2.08/1.27  Inferencing          : 0.07
% 2.08/1.27  Reduction            : 0.06
% 2.08/1.27  Demodulation         : 0.05
% 2.08/1.27  BG Simplification    : 0.01
% 2.08/1.27  Subsumption          : 0.04
% 2.08/1.27  Abstraction          : 0.01
% 2.08/1.27  MUC search           : 0.00
% 2.08/1.27  Cooper               : 0.00
% 2.08/1.27  Total                : 0.48
% 2.08/1.27  Index Insertion      : 0.00
% 2.08/1.27  Index Deletion       : 0.00
% 2.08/1.27  Index Matching       : 0.00
% 2.08/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
