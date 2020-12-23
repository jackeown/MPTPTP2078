%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:25 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   48 (  48 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_69,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_61,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_103,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden(A_48,B_49)
      | ~ r1_xboole_0(k1_tarski(A_48),B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_48] : ~ r2_hidden(A_48,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_114,plain,(
    ! [B_58] : r1_tarski(k1_xboole_0,B_58) ),
    inference(resolution,[status(thm)],[c_103,c_84])).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_57,plain,(
    ! [A_43] : v1_relat_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_57])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_94,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k10_relat_1(B_55,A_56),k1_relat_1(B_55))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,(
    ! [A_56] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_56),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_94])).

tff(c_119,plain,(
    ! [A_60] : r1_tarski(k10_relat_1(k1_xboole_0,A_60),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_99])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,(
    ! [A_60] :
      ( k10_relat_1(k1_xboole_0,A_60) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,A_60)) ) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_124,plain,(
    ! [A_60] : k10_relat_1(k1_xboole_0,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_121])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.24  
% 2.01/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.01/1.25  
% 2.01/1.25  %Foreground sorts:
% 2.01/1.25  
% 2.01/1.25  
% 2.01/1.25  %Background operators:
% 2.01/1.25  
% 2.01/1.25  
% 2.01/1.25  %Foreground operators:
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.01/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.01/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.25  
% 2.01/1.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.01/1.25  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.01/1.25  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.01/1.25  tff(f_69, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.01/1.25  tff(f_61, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.01/1.25  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.01/1.25  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.01/1.26  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.01/1.26  tff(f_72, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.01/1.26  tff(c_103, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), A_57) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.26  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.01/1.26  tff(c_79, plain, (![A_48, B_49]: (~r2_hidden(A_48, B_49) | ~r1_xboole_0(k1_tarski(A_48), B_49))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.01/1.26  tff(c_84, plain, (![A_48]: (~r2_hidden(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_79])).
% 2.01/1.26  tff(c_114, plain, (![B_58]: (r1_tarski(k1_xboole_0, B_58))), inference(resolution, [status(thm)], [c_103, c_84])).
% 2.01/1.26  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.26  tff(c_57, plain, (![A_43]: (v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.01/1.26  tff(c_59, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_57])).
% 2.01/1.26  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.01/1.26  tff(c_94, plain, (![B_55, A_56]: (r1_tarski(k10_relat_1(B_55, A_56), k1_relat_1(B_55)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.01/1.26  tff(c_99, plain, (![A_56]: (r1_tarski(k10_relat_1(k1_xboole_0, A_56), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_94])).
% 2.01/1.26  tff(c_119, plain, (![A_60]: (r1_tarski(k10_relat_1(k1_xboole_0, A_60), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_99])).
% 2.01/1.26  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.01/1.26  tff(c_121, plain, (![A_60]: (k10_relat_1(k1_xboole_0, A_60)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k10_relat_1(k1_xboole_0, A_60)))), inference(resolution, [status(thm)], [c_119, c_8])).
% 2.01/1.26  tff(c_124, plain, (![A_60]: (k10_relat_1(k1_xboole_0, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_121])).
% 2.01/1.26  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.01/1.26  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_42])).
% 2.01/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  Inference rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Ref     : 0
% 2.01/1.26  #Sup     : 19
% 2.01/1.26  #Fact    : 0
% 2.01/1.26  #Define  : 0
% 2.01/1.26  #Split   : 0
% 2.01/1.26  #Chain   : 0
% 2.01/1.26  #Close   : 0
% 2.01/1.26  
% 2.01/1.26  Ordering : KBO
% 2.01/1.26  
% 2.01/1.26  Simplification rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Subsume      : 0
% 2.01/1.26  #Demod        : 8
% 2.01/1.26  #Tautology    : 14
% 2.01/1.26  #SimpNegUnit  : 0
% 2.01/1.26  #BackRed      : 2
% 2.01/1.26  
% 2.01/1.26  #Partial instantiations: 0
% 2.01/1.26  #Strategies tried      : 1
% 2.01/1.26  
% 2.01/1.26  Timing (in seconds)
% 2.01/1.26  ----------------------
% 2.01/1.26  Preprocessing        : 0.33
% 2.01/1.26  Parsing              : 0.18
% 2.01/1.26  CNF conversion       : 0.02
% 2.01/1.26  Main loop            : 0.11
% 2.01/1.26  Inferencing          : 0.04
% 2.01/1.26  Reduction            : 0.04
% 2.01/1.26  Demodulation         : 0.03
% 2.01/1.26  BG Simplification    : 0.01
% 2.01/1.26  Subsumption          : 0.02
% 2.01/1.26  Abstraction          : 0.01
% 2.01/1.26  MUC search           : 0.00
% 2.01/1.26  Cooper               : 0.00
% 2.01/1.26  Total                : 0.47
% 2.01/1.26  Index Insertion      : 0.00
% 2.01/1.26  Index Deletion       : 0.00
% 2.01/1.26  Index Matching       : 0.00
% 2.01/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
