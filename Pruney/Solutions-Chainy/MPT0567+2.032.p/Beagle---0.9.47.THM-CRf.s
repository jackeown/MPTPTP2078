%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   48 (  49 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  47 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_34,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden('#skF_2'(A_47,B_48,C_49),B_48)
      | ~ r2_hidden(A_47,k10_relat_1(C_49,B_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_126,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_20,plain,(
    ! [B_15] : k4_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_tarski(B_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_143,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_20])).

tff(c_86,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_32] :
      ( k1_tarski(A_32) = k1_xboole_0
      | ~ r2_hidden(A_32,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_161,plain,(
    ! [A_32] : ~ r2_hidden(A_32,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_91])).

tff(c_176,plain,(
    ! [A_50,C_51] :
      ( ~ r2_hidden(A_50,k10_relat_1(C_51,k1_xboole_0))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_170,c_161])).

tff(c_187,plain,(
    ! [C_52] :
      ( ~ v1_relat_1(C_52)
      | k10_relat_1(C_52,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_176])).

tff(c_190,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_187])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.88/1.19  
% 1.93/1.20  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.93/1.20  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.93/1.20  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.93/1.20  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.93/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.93/1.20  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.93/1.20  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.93/1.20  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.93/1.20  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.93/1.20  tff(c_34, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.20  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.20  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.20  tff(c_170, plain, (![A_47, B_48, C_49]: (r2_hidden('#skF_2'(A_47, B_48, C_49), B_48) | ~r2_hidden(A_47, k10_relat_1(C_49, B_48)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.20  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.20  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.20  tff(c_114, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.20  tff(c_123, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_114])).
% 1.93/1.20  tff(c_126, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_123])).
% 1.93/1.20  tff(c_20, plain, (![B_15]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.20  tff(c_143, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_20])).
% 1.93/1.20  tff(c_86, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.93/1.20  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.20  tff(c_91, plain, (![A_32]: (k1_tarski(A_32)=k1_xboole_0 | ~r2_hidden(A_32, k1_xboole_0))), inference(resolution, [status(thm)], [c_86, c_8])).
% 1.93/1.20  tff(c_161, plain, (![A_32]: (~r2_hidden(A_32, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_143, c_91])).
% 1.93/1.20  tff(c_176, plain, (![A_50, C_51]: (~r2_hidden(A_50, k10_relat_1(C_51, k1_xboole_0)) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_170, c_161])).
% 1.93/1.20  tff(c_187, plain, (![C_52]: (~v1_relat_1(C_52) | k10_relat_1(C_52, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_176])).
% 1.93/1.20  tff(c_190, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_187])).
% 1.93/1.20  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_190])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 31
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 0
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 0
% 1.93/1.20  #Demod        : 3
% 1.93/1.20  #Tautology    : 24
% 1.93/1.20  #SimpNegUnit  : 2
% 1.93/1.20  #BackRed      : 2
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.21  Preprocessing        : 0.30
% 1.93/1.21  Parsing              : 0.16
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.12
% 1.93/1.21  Inferencing          : 0.05
% 1.93/1.21  Reduction            : 0.04
% 1.93/1.21  Demodulation         : 0.03
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.02
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.45
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
