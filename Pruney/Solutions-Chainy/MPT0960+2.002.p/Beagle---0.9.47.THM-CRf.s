%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:37 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   35 (  36 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k1_wellord2 > k1_setfam_1 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_23] : v1_relat_1(k1_wellord2(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( k2_wellord1(k1_wellord2(B_25),A_24) = k1_wellord2(A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_304,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,k2_zfmisc_1(B_67,B_67)) = k2_wellord1(A_66,B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_110,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_92])).

tff(c_24,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_136,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_24])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_151,plain,(
    ! [B_42,A_43] : r1_tarski(k3_xboole_0(B_42,A_43),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_14])).

tff(c_360,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k2_wellord1(A_72,B_73),k2_zfmisc_1(B_73,B_73))
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_151])).

tff(c_365,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_wellord2(A_24),k2_zfmisc_1(A_24,A_24))
      | ~ v1_relat_1(k1_wellord2(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_360])).

tff(c_389,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_wellord2(A_76),k2_zfmisc_1(A_76,A_76))
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_365])).

tff(c_410,plain,(
    ! [B_8] : r1_tarski(k1_wellord2(B_8),k2_zfmisc_1(B_8,B_8)) ),
    inference(resolution,[status(thm)],[c_12,c_389])).

tff(c_34,plain,(
    ~ r1_tarski(k1_wellord2('#skF_2'),k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:40:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.32  
% 2.09/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.32  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k1_wellord2 > k1_setfam_1 > #skF_1 > #skF_2
% 2.09/1.32  
% 2.09/1.32  %Foreground sorts:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Background operators:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Foreground operators:
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.32  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.09/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.09/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.32  
% 2.09/1.33  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.33  tff(f_62, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.09/1.33  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.09/1.33  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 2.09/1.33  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.33  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.09/1.33  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.09/1.33  tff(f_69, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.09/1.33  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.33  tff(c_30, plain, (![A_23]: (v1_relat_1(k1_wellord2(A_23)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.33  tff(c_32, plain, (![B_25, A_24]: (k2_wellord1(k1_wellord2(B_25), A_24)=k1_wellord2(A_24) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.33  tff(c_304, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k2_zfmisc_1(B_67, B_67))=k2_wellord1(A_66, B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.33  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.33  tff(c_92, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.33  tff(c_110, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_16, c_92])).
% 2.09/1.33  tff(c_24, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.33  tff(c_136, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_110, c_24])).
% 2.09/1.33  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.33  tff(c_151, plain, (![B_42, A_43]: (r1_tarski(k3_xboole_0(B_42, A_43), A_43))), inference(superposition, [status(thm), theory('equality')], [c_136, c_14])).
% 2.09/1.33  tff(c_360, plain, (![A_72, B_73]: (r1_tarski(k2_wellord1(A_72, B_73), k2_zfmisc_1(B_73, B_73)) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_304, c_151])).
% 2.09/1.33  tff(c_365, plain, (![A_24, B_25]: (r1_tarski(k1_wellord2(A_24), k2_zfmisc_1(A_24, A_24)) | ~v1_relat_1(k1_wellord2(B_25)) | ~r1_tarski(A_24, B_25))), inference(superposition, [status(thm), theory('equality')], [c_32, c_360])).
% 2.09/1.33  tff(c_389, plain, (![A_76, B_77]: (r1_tarski(k1_wellord2(A_76), k2_zfmisc_1(A_76, A_76)) | ~r1_tarski(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_365])).
% 2.09/1.33  tff(c_410, plain, (![B_8]: (r1_tarski(k1_wellord2(B_8), k2_zfmisc_1(B_8, B_8)))), inference(resolution, [status(thm)], [c_12, c_389])).
% 2.09/1.33  tff(c_34, plain, (~r1_tarski(k1_wellord2('#skF_2'), k2_zfmisc_1('#skF_2', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.33  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_410, c_34])).
% 2.09/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  Inference rules
% 2.09/1.33  ----------------------
% 2.38/1.33  #Ref     : 0
% 2.38/1.33  #Sup     : 103
% 2.38/1.33  #Fact    : 0
% 2.38/1.33  #Define  : 0
% 2.38/1.33  #Split   : 0
% 2.38/1.33  #Chain   : 0
% 2.38/1.33  #Close   : 0
% 2.38/1.33  
% 2.38/1.33  Ordering : KBO
% 2.38/1.33  
% 2.38/1.33  Simplification rules
% 2.38/1.33  ----------------------
% 2.38/1.33  #Subsume      : 13
% 2.38/1.33  #Demod        : 24
% 2.38/1.33  #Tautology    : 47
% 2.38/1.33  #SimpNegUnit  : 0
% 2.38/1.33  #BackRed      : 1
% 2.38/1.33  
% 2.38/1.33  #Partial instantiations: 0
% 2.38/1.33  #Strategies tried      : 1
% 2.38/1.33  
% 2.38/1.33  Timing (in seconds)
% 2.38/1.33  ----------------------
% 2.38/1.34  Preprocessing        : 0.27
% 2.38/1.34  Parsing              : 0.15
% 2.38/1.34  CNF conversion       : 0.02
% 2.38/1.34  Main loop            : 0.29
% 2.38/1.34  Inferencing          : 0.13
% 2.38/1.34  Reduction            : 0.09
% 2.38/1.34  Demodulation         : 0.07
% 2.38/1.34  BG Simplification    : 0.01
% 2.38/1.34  Subsumption          : 0.05
% 2.38/1.34  Abstraction          : 0.01
% 2.38/1.34  MUC search           : 0.00
% 2.38/1.34  Cooper               : 0.00
% 2.38/1.34  Total                : 0.59
% 2.38/1.34  Index Insertion      : 0.00
% 2.38/1.34  Index Deletion       : 0.00
% 2.38/1.34  Index Matching       : 0.00
% 2.38/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
