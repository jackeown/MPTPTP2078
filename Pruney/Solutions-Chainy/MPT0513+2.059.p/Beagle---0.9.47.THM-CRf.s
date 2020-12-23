%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:06 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_67,plain,(
    ! [B_15,A_16] :
      ( k7_relat_1(B_15,A_16) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_16)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    ! [A_16] :
      ( k7_relat_1(k1_xboole_0,A_16) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_72,plain,(
    ! [A_16] : k7_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2,c_70])).

tff(c_18,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.72/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.18  
% 1.72/1.19  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.72/1.19  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.72/1.19  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.72/1.19  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.72/1.19  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.72/1.19  tff(f_47, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.72/1.19  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.19  tff(c_50, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.19  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_50])).
% 1.72/1.19  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.19  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.19  tff(c_67, plain, (![B_15, A_16]: (k7_relat_1(B_15, A_16)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.72/1.19  tff(c_70, plain, (![A_16]: (k7_relat_1(k1_xboole_0, A_16)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_67])).
% 1.72/1.19  tff(c_72, plain, (![A_16]: (k7_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2, c_70])).
% 1.72/1.19  tff(c_18, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.19  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_18])).
% 1.72/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.19  
% 1.72/1.19  Inference rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Ref     : 0
% 1.72/1.19  #Sup     : 15
% 1.72/1.19  #Fact    : 0
% 1.72/1.19  #Define  : 0
% 1.72/1.19  #Split   : 0
% 1.72/1.19  #Chain   : 0
% 1.72/1.19  #Close   : 0
% 1.72/1.19  
% 1.72/1.19  Ordering : KBO
% 1.72/1.19  
% 1.72/1.19  Simplification rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Subsume      : 0
% 1.72/1.19  #Demod        : 4
% 1.72/1.19  #Tautology    : 13
% 1.72/1.19  #SimpNegUnit  : 0
% 1.72/1.19  #BackRed      : 1
% 1.72/1.19  
% 1.72/1.19  #Partial instantiations: 0
% 1.72/1.19  #Strategies tried      : 1
% 1.72/1.19  
% 1.72/1.19  Timing (in seconds)
% 1.72/1.19  ----------------------
% 1.72/1.19  Preprocessing        : 0.30
% 1.72/1.19  Parsing              : 0.16
% 1.72/1.19  CNF conversion       : 0.02
% 1.72/1.19  Main loop            : 0.10
% 1.72/1.19  Inferencing          : 0.04
% 1.72/1.19  Reduction            : 0.03
% 1.72/1.19  Demodulation         : 0.02
% 1.72/1.19  BG Simplification    : 0.01
% 1.72/1.19  Subsumption          : 0.02
% 1.72/1.19  Abstraction          : 0.00
% 1.72/1.19  MUC search           : 0.00
% 1.72/1.19  Cooper               : 0.00
% 1.72/1.19  Total                : 0.42
% 1.72/1.19  Index Insertion      : 0.00
% 1.72/1.19  Index Deletion       : 0.00
% 1.72/1.19  Index Matching       : 0.00
% 1.72/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
