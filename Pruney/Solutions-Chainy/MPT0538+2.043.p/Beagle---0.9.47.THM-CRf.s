%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  63 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_32,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_1'(A_37),A_37)
      | v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [B_77,A_78] :
      ( ~ r2_hidden(B_77,A_78)
      | k4_xboole_0(A_78,k1_tarski(B_77)) != A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_135,plain,(
    ! [B_79] : ~ r2_hidden(B_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_129])).

tff(c_140,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_38,plain,(
    ! [A_60] :
      ( k8_relat_1(k1_xboole_0,A_60) = k1_xboole_0
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_144,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_38])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_227,plain,(
    ! [A_92,B_93,C_94] :
      ( k8_relat_1(k3_xboole_0(A_92,B_93),C_94) = k8_relat_1(A_92,k8_relat_1(B_93,C_94))
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_253,plain,(
    ! [A_95,C_96] :
      ( k8_relat_1(A_95,k8_relat_1(k1_xboole_0,C_96)) = k8_relat_1(k1_xboole_0,C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_227])).

tff(c_293,plain,(
    ! [A_95] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(A_95,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_253])).

tff(c_300,plain,(
    ! [A_95] : k8_relat_1(A_95,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_144,c_293])).

tff(c_40,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.14/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.14/1.25  
% 2.14/1.26  tff(f_62, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.14/1.26  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.14/1.26  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.14/1.26  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 2.14/1.26  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.14/1.26  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 2.14/1.26  tff(f_77, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 2.14/1.26  tff(c_32, plain, (![A_37]: (r2_hidden('#skF_1'(A_37), A_37) | v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.26  tff(c_6, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.26  tff(c_129, plain, (![B_77, A_78]: (~r2_hidden(B_77, A_78) | k4_xboole_0(A_78, k1_tarski(B_77))!=A_78)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.26  tff(c_135, plain, (![B_79]: (~r2_hidden(B_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_129])).
% 2.14/1.26  tff(c_140, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_135])).
% 2.14/1.26  tff(c_38, plain, (![A_60]: (k8_relat_1(k1_xboole_0, A_60)=k1_xboole_0 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.26  tff(c_144, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_140, c_38])).
% 2.14/1.26  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.26  tff(c_227, plain, (![A_92, B_93, C_94]: (k8_relat_1(k3_xboole_0(A_92, B_93), C_94)=k8_relat_1(A_92, k8_relat_1(B_93, C_94)) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.26  tff(c_253, plain, (![A_95, C_96]: (k8_relat_1(A_95, k8_relat_1(k1_xboole_0, C_96))=k8_relat_1(k1_xboole_0, C_96) | ~v1_relat_1(C_96))), inference(superposition, [status(thm), theory('equality')], [c_4, c_227])).
% 2.14/1.26  tff(c_293, plain, (![A_95]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(A_95, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_144, c_253])).
% 2.14/1.26  tff(c_300, plain, (![A_95]: (k8_relat_1(A_95, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_144, c_293])).
% 2.14/1.26  tff(c_40, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.26  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_40])).
% 2.14/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  Inference rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Ref     : 0
% 2.14/1.26  #Sup     : 61
% 2.14/1.26  #Fact    : 0
% 2.14/1.26  #Define  : 0
% 2.14/1.26  #Split   : 0
% 2.14/1.26  #Chain   : 0
% 2.14/1.26  #Close   : 0
% 2.14/1.26  
% 2.14/1.26  Ordering : KBO
% 2.14/1.26  
% 2.14/1.26  Simplification rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Subsume      : 0
% 2.14/1.26  #Demod        : 8
% 2.14/1.26  #Tautology    : 45
% 2.14/1.26  #SimpNegUnit  : 2
% 2.14/1.26  #BackRed      : 1
% 2.14/1.26  
% 2.14/1.26  #Partial instantiations: 0
% 2.14/1.26  #Strategies tried      : 1
% 2.14/1.26  
% 2.24/1.26  Timing (in seconds)
% 2.24/1.26  ----------------------
% 2.24/1.27  Preprocessing        : 0.33
% 2.24/1.27  Parsing              : 0.17
% 2.24/1.27  CNF conversion       : 0.02
% 2.24/1.27  Main loop            : 0.17
% 2.24/1.27  Inferencing          : 0.07
% 2.24/1.27  Reduction            : 0.05
% 2.24/1.27  Demodulation         : 0.03
% 2.24/1.27  BG Simplification    : 0.02
% 2.24/1.27  Subsumption          : 0.02
% 2.24/1.27  Abstraction          : 0.01
% 2.24/1.27  MUC search           : 0.00
% 2.24/1.27  Cooper               : 0.00
% 2.24/1.27  Total                : 0.53
% 2.24/1.27  Index Insertion      : 0.00
% 2.24/1.27  Index Deletion       : 0.00
% 2.24/1.27  Index Matching       : 0.00
% 2.24/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
