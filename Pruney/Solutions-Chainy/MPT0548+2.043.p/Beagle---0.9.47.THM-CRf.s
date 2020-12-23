%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   42 (  42 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_22,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_61,C_62,B_63] :
      ( ~ r2_hidden(A_61,C_62)
      | ~ r1_xboole_0(k2_tarski(A_61,B_63),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [A_67] : ~ r2_hidden(A_67,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_50] : k7_relat_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [B_68,A_69] :
      ( k2_relat_1(k7_relat_1(B_68,A_69)) = k9_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [A_50] :
      ( k9_relat_1(k1_xboole_0,A_50) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_94,plain,(
    ! [A_50] : k9_relat_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_28,c_90])).

tff(c_32,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.17  
% 1.96/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.17  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.96/1.17  
% 1.96/1.17  %Foreground sorts:
% 1.96/1.17  
% 1.96/1.17  
% 1.96/1.17  %Background operators:
% 1.96/1.17  
% 1.96/1.17  
% 1.96/1.17  %Foreground operators:
% 1.96/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.96/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.96/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.17  
% 1.96/1.18  tff(f_54, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.96/1.18  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.96/1.18  tff(f_44, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.96/1.18  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.96/1.18  tff(f_56, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.96/1.18  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.96/1.18  tff(f_66, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.96/1.18  tff(c_22, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.96/1.18  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.18  tff(c_60, plain, (![A_61, C_62, B_63]: (~r2_hidden(A_61, C_62) | ~r1_xboole_0(k2_tarski(A_61, B_63), C_62))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.96/1.18  tff(c_75, plain, (![A_67]: (~r2_hidden(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_60])).
% 1.96/1.18  tff(c_80, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_75])).
% 1.96/1.18  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.18  tff(c_24, plain, (![A_50]: (k7_relat_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.18  tff(c_81, plain, (![B_68, A_69]: (k2_relat_1(k7_relat_1(B_68, A_69))=k9_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.18  tff(c_90, plain, (![A_50]: (k9_relat_1(k1_xboole_0, A_50)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_81])).
% 1.96/1.18  tff(c_94, plain, (![A_50]: (k9_relat_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_28, c_90])).
% 1.96/1.18  tff(c_32, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.18  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_32])).
% 1.96/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.18  
% 1.96/1.18  Inference rules
% 1.96/1.18  ----------------------
% 1.96/1.18  #Ref     : 0
% 1.96/1.18  #Sup     : 15
% 1.96/1.18  #Fact    : 0
% 1.96/1.18  #Define  : 0
% 1.96/1.18  #Split   : 0
% 1.96/1.18  #Chain   : 0
% 1.96/1.18  #Close   : 0
% 1.96/1.18  
% 1.96/1.18  Ordering : KBO
% 1.96/1.18  
% 1.96/1.18  Simplification rules
% 1.96/1.18  ----------------------
% 1.96/1.18  #Subsume      : 0
% 1.96/1.18  #Demod        : 3
% 1.96/1.18  #Tautology    : 12
% 1.96/1.18  #SimpNegUnit  : 0
% 1.96/1.18  #BackRed      : 1
% 1.96/1.18  
% 1.96/1.18  #Partial instantiations: 0
% 1.96/1.18  #Strategies tried      : 1
% 1.96/1.18  
% 1.96/1.18  Timing (in seconds)
% 1.96/1.18  ----------------------
% 1.96/1.18  Preprocessing        : 0.30
% 1.96/1.18  Parsing              : 0.16
% 1.96/1.18  CNF conversion       : 0.02
% 1.96/1.18  Main loop            : 0.10
% 1.96/1.18  Inferencing          : 0.04
% 1.96/1.18  Reduction            : 0.03
% 1.96/1.18  Demodulation         : 0.02
% 1.96/1.18  BG Simplification    : 0.01
% 1.96/1.18  Subsumption          : 0.01
% 1.96/1.18  Abstraction          : 0.01
% 1.96/1.18  MUC search           : 0.00
% 1.96/1.18  Cooper               : 0.00
% 1.96/1.18  Total                : 0.42
% 1.96/1.18  Index Insertion      : 0.00
% 1.96/1.18  Index Deletion       : 0.00
% 1.96/1.18  Index Matching       : 0.00
% 1.96/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
