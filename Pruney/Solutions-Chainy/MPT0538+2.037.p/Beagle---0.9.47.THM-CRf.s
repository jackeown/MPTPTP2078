%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:27 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   40 (  40 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_18,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [B_48,A_49] :
      ( ~ r2_hidden(B_48,A_49)
      | k4_xboole_0(A_49,k1_tarski(B_48)) != A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [B_50] : ~ r2_hidden(B_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_124,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_20,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [A_34] :
      ( k5_relat_1(k1_xboole_0,A_34) = k1_xboole_0
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [A_27] : k5_relat_1(k1_xboole_0,k6_relat_1(A_27)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_125,plain,(
    ! [B_51,A_52] :
      ( k5_relat_1(B_51,k6_relat_1(A_52)) = k8_relat_1(A_52,B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_138,plain,(
    ! [A_27] :
      ( k8_relat_1(A_27,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_125])).

tff(c_165,plain,(
    ! [A_27] : k8_relat_1(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_138])).

tff(c_28,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  %$ r2_hidden > v1_relat_1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.87/1.22  
% 1.87/1.22  %Foreground sorts:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Background operators:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Foreground operators:
% 1.87/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.87/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.22  
% 1.87/1.23  tff(f_48, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.87/1.23  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.87/1.23  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.87/1.23  tff(f_50, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.87/1.23  tff(f_60, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 1.87/1.23  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.87/1.23  tff(f_63, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.87/1.23  tff(c_18, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.87/1.23  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.23  tff(c_109, plain, (![B_48, A_49]: (~r2_hidden(B_48, A_49) | k4_xboole_0(A_49, k1_tarski(B_48))!=A_49)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.23  tff(c_119, plain, (![B_50]: (~r2_hidden(B_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_109])).
% 1.87/1.23  tff(c_124, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_119])).
% 1.87/1.23  tff(c_20, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.23  tff(c_46, plain, (![A_34]: (k5_relat_1(k1_xboole_0, A_34)=k1_xboole_0 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.23  tff(c_50, plain, (![A_27]: (k5_relat_1(k1_xboole_0, k6_relat_1(A_27))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_46])).
% 1.87/1.23  tff(c_125, plain, (![B_51, A_52]: (k5_relat_1(B_51, k6_relat_1(A_52))=k8_relat_1(A_52, B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.87/1.23  tff(c_138, plain, (![A_27]: (k8_relat_1(A_27, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_125])).
% 1.87/1.23  tff(c_165, plain, (![A_27]: (k8_relat_1(A_27, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_138])).
% 1.87/1.23  tff(c_28, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.87/1.23  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_28])).
% 1.87/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.23  
% 1.87/1.23  Inference rules
% 1.87/1.23  ----------------------
% 1.87/1.23  #Ref     : 0
% 1.87/1.23  #Sup     : 32
% 1.87/1.23  #Fact    : 0
% 1.87/1.23  #Define  : 0
% 1.87/1.23  #Split   : 0
% 1.87/1.23  #Chain   : 0
% 1.87/1.23  #Close   : 0
% 1.87/1.23  
% 1.87/1.23  Ordering : KBO
% 1.87/1.23  
% 1.87/1.23  Simplification rules
% 1.87/1.23  ----------------------
% 1.87/1.23  #Subsume      : 0
% 1.87/1.23  #Demod        : 3
% 1.87/1.23  #Tautology    : 24
% 1.87/1.23  #SimpNegUnit  : 0
% 1.87/1.23  #BackRed      : 1
% 1.87/1.23  
% 1.87/1.23  #Partial instantiations: 0
% 1.87/1.23  #Strategies tried      : 1
% 1.87/1.23  
% 1.87/1.23  Timing (in seconds)
% 1.87/1.23  ----------------------
% 1.89/1.23  Preprocessing        : 0.30
% 1.89/1.23  Parsing              : 0.16
% 1.89/1.23  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.12
% 1.89/1.23  Inferencing          : 0.05
% 1.89/1.23  Reduction            : 0.04
% 1.89/1.23  Demodulation         : 0.03
% 1.89/1.23  BG Simplification    : 0.01
% 1.89/1.23  Subsumption          : 0.01
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.44
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
