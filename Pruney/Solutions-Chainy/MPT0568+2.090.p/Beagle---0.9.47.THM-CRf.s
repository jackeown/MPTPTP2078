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
% DateTime   : Thu Dec  3 10:01:32 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   30 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  42 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_67,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_98,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),B_60)
      | r2_hidden('#skF_2'(A_59,B_60),A_59)
      | B_60 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,B_48)
      | ~ r1_xboole_0(k1_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [A_47] : ~ r2_hidden(A_47,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_67])).

tff(c_105,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_60),B_60)
      | k1_xboole_0 = B_60 ) ),
    inference(resolution,[status(thm)],[c_98,c_72])).

tff(c_38,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [A_43] : v1_relat_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_265,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden(k4_tarski(A_86,'#skF_3'(A_86,B_87,C_88)),C_88)
      | ~ r2_hidden(A_86,k10_relat_1(C_88,B_87))
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_277,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden(A_86,k10_relat_1(k1_xboole_0,B_87))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_265,c_72])).

tff(c_283,plain,(
    ! [A_89,B_90] : ~ r2_hidden(A_89,k10_relat_1(k1_xboole_0,B_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_277])).

tff(c_318,plain,(
    ! [B_90] : k10_relat_1(k1_xboole_0,B_90) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_283])).

tff(c_40,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.11  
% 1.85/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.12  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.85/1.12  
% 1.85/1.12  %Foreground sorts:
% 1.85/1.12  
% 1.85/1.12  
% 1.85/1.12  %Background operators:
% 1.85/1.12  
% 1.85/1.12  
% 1.85/1.12  %Foreground operators:
% 1.85/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.85/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.85/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.85/1.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.85/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.85/1.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.12  
% 1.85/1.12  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.85/1.12  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.85/1.12  tff(f_53, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.85/1.12  tff(f_67, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.85/1.12  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.85/1.12  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.85/1.12  tff(f_70, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.85/1.13  tff(c_98, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), B_60) | r2_hidden('#skF_2'(A_59, B_60), A_59) | B_60=A_59)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.13  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.13  tff(c_67, plain, (![A_47, B_48]: (~r2_hidden(A_47, B_48) | ~r1_xboole_0(k1_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.13  tff(c_72, plain, (![A_47]: (~r2_hidden(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_67])).
% 1.85/1.13  tff(c_105, plain, (![B_60]: (r2_hidden('#skF_1'(k1_xboole_0, B_60), B_60) | k1_xboole_0=B_60)), inference(resolution, [status(thm)], [c_98, c_72])).
% 1.85/1.13  tff(c_38, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.13  tff(c_46, plain, (![A_43]: (v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.13  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_46])).
% 1.85/1.13  tff(c_265, plain, (![A_86, B_87, C_88]: (r2_hidden(k4_tarski(A_86, '#skF_3'(A_86, B_87, C_88)), C_88) | ~r2_hidden(A_86, k10_relat_1(C_88, B_87)) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.85/1.13  tff(c_277, plain, (![A_86, B_87]: (~r2_hidden(A_86, k10_relat_1(k1_xboole_0, B_87)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_265, c_72])).
% 1.85/1.13  tff(c_283, plain, (![A_89, B_90]: (~r2_hidden(A_89, k10_relat_1(k1_xboole_0, B_90)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_277])).
% 1.85/1.13  tff(c_318, plain, (![B_90]: (k10_relat_1(k1_xboole_0, B_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_283])).
% 1.85/1.13  tff(c_40, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.85/1.13  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_40])).
% 1.85/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.13  
% 1.85/1.13  Inference rules
% 1.85/1.13  ----------------------
% 1.85/1.13  #Ref     : 0
% 1.85/1.13  #Sup     : 58
% 1.85/1.13  #Fact    : 0
% 1.85/1.13  #Define  : 0
% 1.85/1.13  #Split   : 0
% 1.85/1.13  #Chain   : 0
% 1.85/1.13  #Close   : 0
% 1.85/1.13  
% 1.85/1.13  Ordering : KBO
% 1.85/1.13  
% 1.85/1.13  Simplification rules
% 1.85/1.13  ----------------------
% 1.85/1.13  #Subsume      : 15
% 1.85/1.13  #Demod        : 12
% 1.85/1.13  #Tautology    : 23
% 1.85/1.13  #SimpNegUnit  : 0
% 1.85/1.13  #BackRed      : 2
% 1.85/1.13  
% 1.85/1.13  #Partial instantiations: 0
% 1.85/1.13  #Strategies tried      : 1
% 1.85/1.13  
% 1.85/1.13  Timing (in seconds)
% 1.85/1.13  ----------------------
% 1.85/1.13  Preprocessing        : 0.28
% 1.85/1.13  Parsing              : 0.15
% 1.85/1.13  CNF conversion       : 0.02
% 1.85/1.13  Main loop            : 0.18
% 1.85/1.13  Inferencing          : 0.08
% 1.85/1.13  Reduction            : 0.05
% 1.85/1.13  Demodulation         : 0.04
% 1.85/1.13  BG Simplification    : 0.01
% 1.85/1.13  Subsumption          : 0.03
% 1.85/1.13  Abstraction          : 0.01
% 1.85/1.13  MUC search           : 0.00
% 1.85/1.13  Cooper               : 0.00
% 1.85/1.13  Total                : 0.48
% 1.85/1.13  Index Insertion      : 0.00
% 1.85/1.13  Index Deletion       : 0.00
% 1.85/1.13  Index Matching       : 0.00
% 1.85/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
