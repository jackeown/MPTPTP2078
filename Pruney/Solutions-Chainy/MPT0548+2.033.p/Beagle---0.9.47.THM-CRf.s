%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:39 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   51 (  51 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_32,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_130,plain,(
    ! [A_70] : k4_xboole_0(A_70,A_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_126])).

tff(c_22,plain,(
    ! [C_29,B_28] : ~ r2_hidden(C_29,k4_xboole_0(B_28,k1_tarski(C_29))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_154,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_149])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_50] : k7_relat_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_155,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(k7_relat_1(B_75,A_76)) = k9_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_164,plain,(
    ! [A_50] :
      ( k9_relat_1(k1_xboole_0,A_50) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_155])).

tff(c_168,plain,(
    ! [A_50] : k9_relat_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_38,c_164])).

tff(c_42,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.31  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.02/1.31  
% 2.02/1.31  %Foreground sorts:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Background operators:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Foreground operators:
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.02/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.02/1.31  
% 2.02/1.32  tff(f_62, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.02/1.32  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.02/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.02/1.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.02/1.32  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.02/1.32  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.02/1.32  tff(f_64, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.02/1.32  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.02/1.32  tff(f_74, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.02/1.32  tff(c_32, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.32  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.32  tff(c_117, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.32  tff(c_126, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 2.02/1.32  tff(c_130, plain, (![A_70]: (k4_xboole_0(A_70, A_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_126])).
% 2.02/1.32  tff(c_22, plain, (![C_29, B_28]: (~r2_hidden(C_29, k4_xboole_0(B_28, k1_tarski(C_29))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.32  tff(c_149, plain, (![C_74]: (~r2_hidden(C_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_22])).
% 2.02/1.32  tff(c_154, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_149])).
% 2.02/1.32  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.02/1.32  tff(c_34, plain, (![A_50]: (k7_relat_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.02/1.32  tff(c_155, plain, (![B_75, A_76]: (k2_relat_1(k7_relat_1(B_75, A_76))=k9_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.32  tff(c_164, plain, (![A_50]: (k9_relat_1(k1_xboole_0, A_50)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_155])).
% 2.02/1.32  tff(c_168, plain, (![A_50]: (k9_relat_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_38, c_164])).
% 2.02/1.32  tff(c_42, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.32  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_42])).
% 2.02/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  Inference rules
% 2.02/1.32  ----------------------
% 2.02/1.32  #Ref     : 0
% 2.02/1.32  #Sup     : 33
% 2.02/1.32  #Fact    : 0
% 2.02/1.32  #Define  : 0
% 2.02/1.32  #Split   : 0
% 2.02/1.32  #Chain   : 0
% 2.02/1.32  #Close   : 0
% 2.02/1.32  
% 2.02/1.32  Ordering : KBO
% 2.02/1.32  
% 2.02/1.32  Simplification rules
% 2.02/1.32  ----------------------
% 2.02/1.32  #Subsume      : 1
% 2.02/1.32  #Demod        : 5
% 2.02/1.32  #Tautology    : 26
% 2.02/1.32  #SimpNegUnit  : 0
% 2.02/1.32  #BackRed      : 1
% 2.02/1.32  
% 2.02/1.32  #Partial instantiations: 0
% 2.02/1.32  #Strategies tried      : 1
% 2.02/1.32  
% 2.02/1.32  Timing (in seconds)
% 2.02/1.32  ----------------------
% 2.02/1.33  Preprocessing        : 0.32
% 2.02/1.33  Parsing              : 0.17
% 2.02/1.33  CNF conversion       : 0.02
% 2.02/1.33  Main loop            : 0.12
% 2.02/1.33  Inferencing          : 0.04
% 2.02/1.33  Reduction            : 0.04
% 2.02/1.33  Demodulation         : 0.03
% 2.02/1.33  BG Simplification    : 0.01
% 2.02/1.33  Subsumption          : 0.01
% 2.02/1.33  Abstraction          : 0.01
% 2.02/1.33  MUC search           : 0.00
% 2.02/1.33  Cooper               : 0.00
% 2.02/1.33  Total                : 0.46
% 2.02/1.33  Index Insertion      : 0.00
% 2.02/1.33  Index Deletion       : 0.00
% 2.02/1.33  Index Matching       : 0.00
% 2.02/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
