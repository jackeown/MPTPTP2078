%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_36,axiom,(
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

tff(f_45,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k1_wellord2(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k2_wellord1(k1_wellord2(B_12),A_11) = k1_wellord2(A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,k2_zfmisc_1(B_25,B_25)) = k2_wellord1(A_24,B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [B_18,A_19] : k3_xboole_0(B_18,A_19) = k3_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [B_18,A_19] : r1_tarski(k3_xboole_0(B_18,A_19),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4])).

tff(c_112,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k2_wellord1(A_30,B_31),k2_zfmisc_1(B_31,B_31))
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_33])).

tff(c_115,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_wellord2(A_11),k2_zfmisc_1(A_11,A_11))
      | ~ v1_relat_1(k1_wellord2(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_112])).

tff(c_118,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_wellord2(A_32),k2_zfmisc_1(A_32,A_32))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_115])).

tff(c_136,plain,(
    ! [A_5] : r1_tarski(k1_wellord2(A_5),k2_zfmisc_1(A_5,A_5)) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_14,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:57:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_1
% 1.68/1.14  
% 1.68/1.14  %Foreground sorts:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Background operators:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Foreground operators:
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.14  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.68/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.14  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.68/1.14  
% 1.68/1.14  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.68/1.14  tff(f_38, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.68/1.14  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 1.68/1.14  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 1.68/1.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.68/1.14  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.68/1.14  tff(f_45, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 1.68/1.14  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.14  tff(c_10, plain, (![A_10]: (v1_relat_1(k1_wellord2(A_10)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.14  tff(c_12, plain, (![B_12, A_11]: (k2_wellord1(k1_wellord2(B_12), A_11)=k1_wellord2(A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.14  tff(c_76, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k2_zfmisc_1(B_25, B_25))=k2_wellord1(A_24, B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.68/1.14  tff(c_18, plain, (![B_18, A_19]: (k3_xboole_0(B_18, A_19)=k3_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.14  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.14  tff(c_33, plain, (![B_18, A_19]: (r1_tarski(k3_xboole_0(B_18, A_19), A_19))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4])).
% 1.68/1.14  tff(c_112, plain, (![A_30, B_31]: (r1_tarski(k2_wellord1(A_30, B_31), k2_zfmisc_1(B_31, B_31)) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_76, c_33])).
% 1.68/1.14  tff(c_115, plain, (![A_11, B_12]: (r1_tarski(k1_wellord2(A_11), k2_zfmisc_1(A_11, A_11)) | ~v1_relat_1(k1_wellord2(B_12)) | ~r1_tarski(A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_112])).
% 1.68/1.14  tff(c_118, plain, (![A_32, B_33]: (r1_tarski(k1_wellord2(A_32), k2_zfmisc_1(A_32, A_32)) | ~r1_tarski(A_32, B_33))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_115])).
% 1.68/1.14  tff(c_136, plain, (![A_5]: (r1_tarski(k1_wellord2(A_5), k2_zfmisc_1(A_5, A_5)))), inference(resolution, [status(thm)], [c_6, c_118])).
% 1.68/1.14  tff(c_14, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.68/1.14  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_14])).
% 1.68/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  Inference rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Ref     : 0
% 1.68/1.14  #Sup     : 30
% 1.68/1.14  #Fact    : 0
% 1.68/1.14  #Define  : 0
% 1.68/1.14  #Split   : 0
% 1.68/1.14  #Chain   : 0
% 1.68/1.14  #Close   : 0
% 1.68/1.14  
% 1.68/1.14  Ordering : KBO
% 1.68/1.14  
% 1.68/1.14  Simplification rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Subsume      : 0
% 1.68/1.14  #Demod        : 7
% 1.68/1.14  #Tautology    : 16
% 1.68/1.15  #SimpNegUnit  : 0
% 1.68/1.15  #BackRed      : 1
% 1.68/1.15  
% 1.68/1.15  #Partial instantiations: 0
% 1.68/1.15  #Strategies tried      : 1
% 1.68/1.15  
% 1.68/1.15  Timing (in seconds)
% 1.68/1.15  ----------------------
% 1.68/1.15  Preprocessing        : 0.25
% 1.68/1.15  Parsing              : 0.14
% 1.68/1.15  CNF conversion       : 0.02
% 1.68/1.15  Main loop            : 0.13
% 1.68/1.15  Inferencing          : 0.05
% 1.68/1.15  Reduction            : 0.04
% 1.68/1.15  Demodulation         : 0.03
% 1.68/1.15  BG Simplification    : 0.01
% 1.68/1.15  Subsumption          : 0.02
% 1.68/1.15  Abstraction          : 0.01
% 1.68/1.15  MUC search           : 0.00
% 1.68/1.15  Cooper               : 0.00
% 1.68/1.15  Total                : 0.40
% 1.68/1.15  Index Insertion      : 0.00
% 1.68/1.15  Index Deletion       : 0.00
% 1.68/1.15  Index Matching       : 0.00
% 1.68/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
