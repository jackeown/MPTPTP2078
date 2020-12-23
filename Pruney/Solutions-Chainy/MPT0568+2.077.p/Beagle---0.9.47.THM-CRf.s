%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:30 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_66,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [A_21,B_22] : ~ r2_hidden(A_21,k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_134,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden('#skF_2'(A_37,B_38,C_39),k2_relat_1(C_39))
      | ~ r2_hidden(A_37,k10_relat_1(C_39,B_38))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_2'(A_37,B_38,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_37,k10_relat_1(k1_xboole_0,B_38))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_134])).

tff(c_143,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_2'(A_37,B_38,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_37,k10_relat_1(k1_xboole_0,B_38)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_140])).

tff(c_145,plain,(
    ! [A_40,B_41] : ~ r2_hidden(A_40,k10_relat_1(k1_xboole_0,B_41)) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_143])).

tff(c_156,plain,(
    ! [B_42] : v1_xboole_0(k10_relat_1(k1_xboole_0,B_42)) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [B_27,A_28] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_162,plain,(
    ! [B_42] : k10_relat_1(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_95])).

tff(c_34,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.87/1.19  
% 1.87/1.19  %Foreground sorts:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Background operators:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Foreground operators:
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.87/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.19  
% 1.87/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.87/1.20  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.87/1.20  tff(f_49, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.87/1.20  tff(f_66, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.87/1.20  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.87/1.20  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.87/1.20  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.87/1.20  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.87/1.20  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.87/1.20  tff(f_69, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.87/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.20  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.20  tff(c_72, plain, (![A_21, B_22]: (~r2_hidden(A_21, k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.20  tff(c_78, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_72])).
% 1.87/1.20  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.87/1.20  tff(c_18, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.20  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_18])).
% 1.87/1.20  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.20  tff(c_134, plain, (![A_37, B_38, C_39]: (r2_hidden('#skF_2'(A_37, B_38, C_39), k2_relat_1(C_39)) | ~r2_hidden(A_37, k10_relat_1(C_39, B_38)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.20  tff(c_140, plain, (![A_37, B_38]: (r2_hidden('#skF_2'(A_37, B_38, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_37, k10_relat_1(k1_xboole_0, B_38)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_134])).
% 1.87/1.20  tff(c_143, plain, (![A_37, B_38]: (r2_hidden('#skF_2'(A_37, B_38, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_37, k10_relat_1(k1_xboole_0, B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_140])).
% 1.87/1.20  tff(c_145, plain, (![A_40, B_41]: (~r2_hidden(A_40, k10_relat_1(k1_xboole_0, B_41)))), inference(negUnitSimplification, [status(thm)], [c_78, c_143])).
% 1.87/1.20  tff(c_156, plain, (![B_42]: (v1_xboole_0(k10_relat_1(k1_xboole_0, B_42)))), inference(resolution, [status(thm)], [c_4, c_145])).
% 1.87/1.20  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.20  tff(c_92, plain, (![B_27, A_28]: (~v1_xboole_0(B_27) | B_27=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.87/1.20  tff(c_95, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_6, c_92])).
% 1.87/1.20  tff(c_162, plain, (![B_42]: (k10_relat_1(k1_xboole_0, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_156, c_95])).
% 1.87/1.20  tff(c_34, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.87/1.20  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_34])).
% 1.87/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  Inference rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Ref     : 0
% 1.87/1.20  #Sup     : 31
% 1.87/1.20  #Fact    : 0
% 1.87/1.20  #Define  : 0
% 1.87/1.20  #Split   : 0
% 1.87/1.20  #Chain   : 0
% 1.87/1.20  #Close   : 0
% 1.87/1.20  
% 1.87/1.20  Ordering : KBO
% 1.87/1.20  
% 1.87/1.20  Simplification rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Subsume      : 2
% 1.87/1.20  #Demod        : 6
% 1.87/1.20  #Tautology    : 18
% 1.87/1.20  #SimpNegUnit  : 1
% 1.87/1.20  #BackRed      : 3
% 1.87/1.20  
% 1.87/1.20  #Partial instantiations: 0
% 1.87/1.20  #Strategies tried      : 1
% 1.87/1.20  
% 1.87/1.20  Timing (in seconds)
% 1.87/1.20  ----------------------
% 1.87/1.20  Preprocessing        : 0.28
% 1.87/1.20  Parsing              : 0.15
% 1.87/1.20  CNF conversion       : 0.02
% 1.87/1.20  Main loop            : 0.15
% 1.87/1.20  Inferencing          : 0.06
% 1.87/1.20  Reduction            : 0.04
% 1.87/1.20  Demodulation         : 0.03
% 1.87/1.20  BG Simplification    : 0.01
% 1.87/1.20  Subsumption          : 0.03
% 1.87/1.20  Abstraction          : 0.01
% 1.87/1.20  MUC search           : 0.00
% 1.87/1.20  Cooper               : 0.00
% 1.87/1.20  Total                : 0.46
% 1.87/1.20  Index Insertion      : 0.00
% 1.87/1.20  Index Deletion       : 0.00
% 1.87/1.20  Index Matching       : 0.00
% 1.87/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
