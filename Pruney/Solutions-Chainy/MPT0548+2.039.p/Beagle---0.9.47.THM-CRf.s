%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   15 (  15 expanded)
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

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_30,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [C_55,B_56] : ~ r2_hidden(C_55,k4_xboole_0(B_56,k1_tarski(C_55))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [C_57] : ~ r2_hidden(C_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_73])).

tff(c_82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_48] : k7_relat_1(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_167,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(k7_relat_1(B_75,A_76)) = k9_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_176,plain,(
    ! [A_48] :
      ( k9_relat_1(k1_xboole_0,A_48) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_180,plain,(
    ! [A_48] : k9_relat_1(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_36,c_176])).

tff(c_40,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.17  
% 1.94/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.17  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.94/1.17  
% 1.94/1.17  %Foreground sorts:
% 1.94/1.17  
% 1.94/1.17  
% 1.94/1.17  %Background operators:
% 1.94/1.17  
% 1.94/1.17  
% 1.94/1.17  %Foreground operators:
% 1.94/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.94/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.94/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.94/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.94/1.17  
% 1.94/1.18  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.94/1.18  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.94/1.18  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.94/1.18  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.94/1.18  tff(f_62, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.94/1.18  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.94/1.18  tff(f_72, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.94/1.18  tff(c_30, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.18  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.18  tff(c_73, plain, (![C_55, B_56]: (~r2_hidden(C_55, k4_xboole_0(B_56, k1_tarski(C_55))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.94/1.18  tff(c_77, plain, (![C_57]: (~r2_hidden(C_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_73])).
% 1.94/1.18  tff(c_82, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_77])).
% 1.94/1.18  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.94/1.18  tff(c_32, plain, (![A_48]: (k7_relat_1(k1_xboole_0, A_48)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.18  tff(c_167, plain, (![B_75, A_76]: (k2_relat_1(k7_relat_1(B_75, A_76))=k9_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.18  tff(c_176, plain, (![A_48]: (k9_relat_1(k1_xboole_0, A_48)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_167])).
% 1.94/1.18  tff(c_180, plain, (![A_48]: (k9_relat_1(k1_xboole_0, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_36, c_176])).
% 1.94/1.18  tff(c_40, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.18  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_40])).
% 1.94/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  Inference rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Ref     : 0
% 1.94/1.18  #Sup     : 37
% 1.94/1.18  #Fact    : 0
% 1.94/1.18  #Define  : 0
% 1.94/1.18  #Split   : 0
% 1.94/1.18  #Chain   : 0
% 1.94/1.18  #Close   : 0
% 1.94/1.18  
% 1.94/1.18  Ordering : KBO
% 1.94/1.18  
% 1.94/1.18  Simplification rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Subsume      : 2
% 1.94/1.18  #Demod        : 4
% 1.94/1.18  #Tautology    : 29
% 1.94/1.18  #SimpNegUnit  : 2
% 1.94/1.18  #BackRed      : 1
% 1.94/1.18  
% 1.94/1.18  #Partial instantiations: 0
% 1.94/1.18  #Strategies tried      : 1
% 1.94/1.18  
% 1.94/1.18  Timing (in seconds)
% 1.94/1.18  ----------------------
% 1.94/1.19  Preprocessing        : 0.31
% 1.94/1.19  Parsing              : 0.17
% 1.94/1.19  CNF conversion       : 0.02
% 1.94/1.19  Main loop            : 0.13
% 1.94/1.19  Inferencing          : 0.05
% 1.94/1.19  Reduction            : 0.04
% 1.94/1.19  Demodulation         : 0.03
% 1.94/1.19  BG Simplification    : 0.01
% 1.94/1.19  Subsumption          : 0.02
% 1.94/1.19  Abstraction          : 0.01
% 1.94/1.19  MUC search           : 0.00
% 1.94/1.19  Cooper               : 0.00
% 1.94/1.19  Total                : 0.47
% 1.94/1.19  Index Insertion      : 0.00
% 1.94/1.19  Index Deletion       : 0.00
% 1.94/1.19  Index Matching       : 0.00
% 1.94/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
