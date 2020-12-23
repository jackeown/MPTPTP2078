%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   49 (  49 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_60,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_28,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_1'(A_18),A_18)
      | v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_129])).

tff(c_161,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_16,plain,(
    ! [C_13,B_12] : ~ r2_hidden(C_13,k4_xboole_0(B_12,k1_tarski(C_13))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_185,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_16])).

tff(c_190,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_185])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_36] : k7_relat_1(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_148,plain,(
    ! [B_57,A_58] :
      ( k2_relat_1(k7_relat_1(B_57,A_58)) = k9_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_157,plain,(
    ! [A_36] :
      ( k9_relat_1(k1_xboole_0,A_36) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_148])).

tff(c_160,plain,(
    ! [A_36] :
      ( k9_relat_1(k1_xboole_0,A_36) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_157])).

tff(c_221,plain,(
    ! [A_36] : k9_relat_1(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_160])).

tff(c_38,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:12:14 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  %$ r2_hidden > v1_relat_1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.94/1.20  
% 1.94/1.20  %Foreground sorts:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Background operators:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Foreground operators:
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.94/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.94/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.20  
% 1.94/1.21  tff(f_58, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.94/1.21  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.94/1.21  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.94/1.21  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.94/1.21  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.94/1.21  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.94/1.21  tff(f_60, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.94/1.21  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.94/1.21  tff(f_70, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.94/1.21  tff(c_28, plain, (![A_18]: (r2_hidden('#skF_1'(A_18), A_18) | v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.21  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.21  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.21  tff(c_129, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.21  tff(c_144, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_129])).
% 1.94/1.21  tff(c_161, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_144])).
% 1.94/1.21  tff(c_16, plain, (![C_13, B_12]: (~r2_hidden(C_13, k4_xboole_0(B_12, k1_tarski(C_13))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.94/1.21  tff(c_185, plain, (![C_60]: (~r2_hidden(C_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_161, c_16])).
% 1.94/1.21  tff(c_190, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_185])).
% 1.94/1.21  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.94/1.21  tff(c_30, plain, (![A_36]: (k7_relat_1(k1_xboole_0, A_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.21  tff(c_148, plain, (![B_57, A_58]: (k2_relat_1(k7_relat_1(B_57, A_58))=k9_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.21  tff(c_157, plain, (![A_36]: (k9_relat_1(k1_xboole_0, A_36)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_148])).
% 1.94/1.21  tff(c_160, plain, (![A_36]: (k9_relat_1(k1_xboole_0, A_36)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_157])).
% 1.94/1.21  tff(c_221, plain, (![A_36]: (k9_relat_1(k1_xboole_0, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_160])).
% 1.94/1.21  tff(c_38, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.21  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_38])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 44
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 0
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 1
% 1.94/1.21  #Demod        : 5
% 1.94/1.21  #Tautology    : 34
% 1.94/1.21  #SimpNegUnit  : 0
% 1.94/1.21  #BackRed      : 1
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.30
% 1.94/1.21  Parsing              : 0.16
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.13
% 1.94/1.21  Inferencing          : 0.05
% 1.94/1.21  Reduction            : 0.04
% 1.94/1.21  Demodulation         : 0.03
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.02
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.46
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
