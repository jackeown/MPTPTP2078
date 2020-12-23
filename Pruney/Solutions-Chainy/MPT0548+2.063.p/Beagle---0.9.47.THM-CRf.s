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
% DateTime   : Thu Dec  3 10:00:43 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_39])).

tff(c_280,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k4_tarski('#skF_2'(A_62,B_63,C_64),A_62),C_64)
      | ~ r2_hidden(A_62,k9_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [C_27,B_28] : ~ r2_hidden(C_27,k4_xboole_0(B_28,k1_tarski(C_27))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_292,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden(A_62,k9_relat_1(k1_xboole_0,B_63))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_280,c_61])).

tff(c_298,plain,(
    ! [A_65,B_66] : ~ r2_hidden(A_65,k9_relat_1(k1_xboole_0,B_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_292])).

tff(c_320,plain,(
    ! [B_66] : k9_relat_1(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_298])).

tff(c_34,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  %$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.06/1.23  
% 2.06/1.23  %Foreground sorts:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Background operators:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Foreground operators:
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.23  
% 2.06/1.24  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.24  tff(f_66, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.06/1.24  tff(f_54, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.06/1.24  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.06/1.24  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.06/1.24  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.06/1.24  tff(f_69, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.06/1.24  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.24  tff(c_32, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.24  tff(c_39, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.24  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_39])).
% 2.06/1.24  tff(c_280, plain, (![A_62, B_63, C_64]: (r2_hidden(k4_tarski('#skF_2'(A_62, B_63, C_64), A_62), C_64) | ~r2_hidden(A_62, k9_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.24  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.24  tff(c_58, plain, (![C_27, B_28]: (~r2_hidden(C_27, k4_xboole_0(B_28, k1_tarski(C_27))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.24  tff(c_61, plain, (![C_27]: (~r2_hidden(C_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 2.06/1.24  tff(c_292, plain, (![A_62, B_63]: (~r2_hidden(A_62, k9_relat_1(k1_xboole_0, B_63)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_280, c_61])).
% 2.06/1.24  tff(c_298, plain, (![A_65, B_66]: (~r2_hidden(A_65, k9_relat_1(k1_xboole_0, B_66)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_292])).
% 2.06/1.24  tff(c_320, plain, (![B_66]: (k9_relat_1(k1_xboole_0, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_298])).
% 2.06/1.24  tff(c_34, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.06/1.24  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_34])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 64
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 0
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 10
% 2.06/1.24  #Demod        : 14
% 2.06/1.24  #Tautology    : 36
% 2.06/1.24  #SimpNegUnit  : 4
% 2.06/1.24  #BackRed      : 2
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.24  Preprocessing        : 0.29
% 2.06/1.24  Parsing              : 0.15
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.17
% 2.06/1.24  Inferencing          : 0.07
% 2.06/1.24  Reduction            : 0.05
% 2.06/1.24  Demodulation         : 0.04
% 2.06/1.24  BG Simplification    : 0.01
% 2.06/1.24  Subsumption          : 0.03
% 2.06/1.24  Abstraction          : 0.01
% 2.06/1.24  MUC search           : 0.00
% 2.06/1.24  Cooper               : 0.00
% 2.06/1.24  Total                : 0.48
% 2.06/1.24  Index Insertion      : 0.00
% 2.06/1.24  Index Deletion       : 0.00
% 2.06/1.24  Index Matching       : 0.00
% 2.06/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
