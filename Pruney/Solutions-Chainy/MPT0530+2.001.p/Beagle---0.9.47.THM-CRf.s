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
% DateTime   : Thu Dec  3 10:00:14 EST 2020

% Result     : Theorem 13.17s
% Output     : CNFRefutation 13.26s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 105 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 182 expanded)
%              Number of equality atoms :   27 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_58,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_538,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_100,B_101),B_102),A_100)
      | r1_tarski(k4_xboole_0(A_100,B_101),B_102) ) ),
    inference(resolution,[status(thm)],[c_113,c_12])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_129,plain,(
    ! [A_6,B_7,B_50] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_50),B_7)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_50) ) ),
    inference(resolution,[status(thm)],[c_113,c_10])).

tff(c_585,plain,(
    ! [A_103,B_104] : r1_tarski(k4_xboole_0(A_103,A_103),B_104) ),
    inference(resolution,[status(thm)],[c_538,c_129])).

tff(c_42,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_130,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_141,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_602,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_585,c_141])).

tff(c_44,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_621,plain,(
    ! [A_105] : k4_xboole_0(A_105,k1_xboole_0) = k3_xboole_0(A_105,A_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_44])).

tff(c_636,plain,(
    ! [A_105] : k4_xboole_0(A_105,k1_xboole_0) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_621])).

tff(c_56,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_481,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_2'(A_97,B_98,C_99),A_97)
      | r2_hidden('#skF_3'(A_97,B_98,C_99),C_99)
      | k4_xboole_0(A_97,B_98) = C_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5795,plain,(
    ! [A_370,B_371,C_372,B_373] :
      ( r2_hidden('#skF_2'(A_370,B_371,C_372),B_373)
      | ~ r1_tarski(A_370,B_373)
      | r2_hidden('#skF_3'(A_370,B_371,C_372),C_372)
      | k4_xboole_0(A_370,B_371) = C_372 ) ),
    inference(resolution,[status(thm)],[c_481,c_2])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5879,plain,(
    ! [A_370,B_373,C_372] :
      ( ~ r1_tarski(A_370,B_373)
      | r2_hidden('#skF_3'(A_370,B_373,C_372),C_372)
      | k4_xboole_0(A_370,B_373) = C_372 ) ),
    inference(resolution,[status(thm)],[c_5795,c_22])).

tff(c_7148,plain,(
    ! [A_404,B_405,C_406] :
      ( ~ r1_tarski(A_404,B_405)
      | r2_hidden('#skF_3'(A_404,B_405,C_406),C_406)
      | k4_xboole_0(A_404,B_405) = C_406 ) ),
    inference(resolution,[status(thm)],[c_5795,c_22])).

tff(c_92,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,(
    ! [D_11,A_47,B_48] :
      ( ~ r2_hidden(D_11,k4_xboole_0(A_47,B_48))
      | ~ r2_hidden(D_11,k3_xboole_0(A_47,B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_10])).

tff(c_618,plain,(
    ! [D_11,A_105] :
      ( ~ r2_hidden(D_11,k1_xboole_0)
      | ~ r2_hidden(D_11,k3_xboole_0(A_105,A_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_104])).

tff(c_635,plain,(
    ! [D_11,A_105] :
      ( ~ r2_hidden(D_11,k1_xboole_0)
      | ~ r2_hidden(D_11,A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_618])).

tff(c_20871,plain,(
    ! [A_669,B_670,A_671] :
      ( ~ r2_hidden('#skF_3'(A_669,B_670,k1_xboole_0),A_671)
      | ~ r1_tarski(A_669,B_670)
      | k4_xboole_0(A_669,B_670) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7148,c_635])).

tff(c_20980,plain,(
    ! [A_672,B_673] :
      ( ~ r1_tarski(A_672,B_673)
      | k4_xboole_0(A_672,B_673) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5879,c_20871])).

tff(c_21007,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_20980])).

tff(c_21331,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_21007,c_44])).

tff(c_21442,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_21331])).

tff(c_52,plain,(
    ! [A_29,B_30,C_31] :
      ( k8_relat_1(k3_xboole_0(A_29,B_30),C_31) = k8_relat_1(A_29,k8_relat_1(B_30,C_31))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42219,plain,(
    ! [C_942] :
      ( k8_relat_1('#skF_6',k8_relat_1('#skF_7',C_942)) = k8_relat_1('#skF_6',C_942)
      | ~ v1_relat_1(C_942) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21442,c_52])).

tff(c_54,plain,(
    k8_relat_1('#skF_6',k8_relat_1('#skF_7','#skF_8')) != k8_relat_1('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42228,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_42219,c_54])).

tff(c_42240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_42228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.17/5.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.26/5.70  
% 13.26/5.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.26/5.70  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 13.26/5.70  
% 13.26/5.70  %Foreground sorts:
% 13.26/5.70  
% 13.26/5.70  
% 13.26/5.70  %Background operators:
% 13.26/5.70  
% 13.26/5.70  
% 13.26/5.70  %Foreground operators:
% 13.26/5.70  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 13.26/5.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.26/5.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.26/5.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.26/5.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.26/5.70  tff('#skF_7', type, '#skF_7': $i).
% 13.26/5.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.26/5.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.26/5.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.26/5.70  tff('#skF_6', type, '#skF_6': $i).
% 13.26/5.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.26/5.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.26/5.70  tff('#skF_8', type, '#skF_8': $i).
% 13.26/5.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.26/5.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.26/5.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.26/5.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.26/5.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.26/5.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.26/5.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.26/5.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.26/5.70  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.26/5.70  
% 13.26/5.72  tff(f_78, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 13.26/5.72  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.26/5.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.26/5.72  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.26/5.72  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.26/5.72  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.26/5.72  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.26/5.72  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 13.26/5.72  tff(c_58, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.26/5.72  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.26/5.72  tff(c_113, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.26/5.72  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.26/5.72  tff(c_538, plain, (![A_100, B_101, B_102]: (r2_hidden('#skF_1'(k4_xboole_0(A_100, B_101), B_102), A_100) | r1_tarski(k4_xboole_0(A_100, B_101), B_102))), inference(resolution, [status(thm)], [c_113, c_12])).
% 13.26/5.72  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.26/5.72  tff(c_129, plain, (![A_6, B_7, B_50]: (~r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_50), B_7) | r1_tarski(k4_xboole_0(A_6, B_7), B_50))), inference(resolution, [status(thm)], [c_113, c_10])).
% 13.26/5.72  tff(c_585, plain, (![A_103, B_104]: (r1_tarski(k4_xboole_0(A_103, A_103), B_104))), inference(resolution, [status(thm)], [c_538, c_129])).
% 13.26/5.72  tff(c_42, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.26/5.72  tff(c_130, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.26/5.72  tff(c_141, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_130])).
% 13.26/5.72  tff(c_602, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_585, c_141])).
% 13.26/5.72  tff(c_44, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.26/5.72  tff(c_621, plain, (![A_105]: (k4_xboole_0(A_105, k1_xboole_0)=k3_xboole_0(A_105, A_105))), inference(superposition, [status(thm), theory('equality')], [c_602, c_44])).
% 13.26/5.72  tff(c_636, plain, (![A_105]: (k4_xboole_0(A_105, k1_xboole_0)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_621])).
% 13.26/5.72  tff(c_56, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.26/5.72  tff(c_481, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_2'(A_97, B_98, C_99), A_97) | r2_hidden('#skF_3'(A_97, B_98, C_99), C_99) | k4_xboole_0(A_97, B_98)=C_99)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.26/5.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.26/5.72  tff(c_5795, plain, (![A_370, B_371, C_372, B_373]: (r2_hidden('#skF_2'(A_370, B_371, C_372), B_373) | ~r1_tarski(A_370, B_373) | r2_hidden('#skF_3'(A_370, B_371, C_372), C_372) | k4_xboole_0(A_370, B_371)=C_372)), inference(resolution, [status(thm)], [c_481, c_2])).
% 13.26/5.72  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.26/5.72  tff(c_5879, plain, (![A_370, B_373, C_372]: (~r1_tarski(A_370, B_373) | r2_hidden('#skF_3'(A_370, B_373, C_372), C_372) | k4_xboole_0(A_370, B_373)=C_372)), inference(resolution, [status(thm)], [c_5795, c_22])).
% 13.26/5.72  tff(c_7148, plain, (![A_404, B_405, C_406]: (~r1_tarski(A_404, B_405) | r2_hidden('#skF_3'(A_404, B_405, C_406), C_406) | k4_xboole_0(A_404, B_405)=C_406)), inference(resolution, [status(thm)], [c_5795, c_22])).
% 13.26/5.72  tff(c_92, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.26/5.72  tff(c_104, plain, (![D_11, A_47, B_48]: (~r2_hidden(D_11, k4_xboole_0(A_47, B_48)) | ~r2_hidden(D_11, k3_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_10])).
% 13.26/5.72  tff(c_618, plain, (![D_11, A_105]: (~r2_hidden(D_11, k1_xboole_0) | ~r2_hidden(D_11, k3_xboole_0(A_105, A_105)))), inference(superposition, [status(thm), theory('equality')], [c_602, c_104])).
% 13.26/5.72  tff(c_635, plain, (![D_11, A_105]: (~r2_hidden(D_11, k1_xboole_0) | ~r2_hidden(D_11, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_618])).
% 13.26/5.72  tff(c_20871, plain, (![A_669, B_670, A_671]: (~r2_hidden('#skF_3'(A_669, B_670, k1_xboole_0), A_671) | ~r1_tarski(A_669, B_670) | k4_xboole_0(A_669, B_670)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7148, c_635])).
% 13.26/5.72  tff(c_20980, plain, (![A_672, B_673]: (~r1_tarski(A_672, B_673) | k4_xboole_0(A_672, B_673)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5879, c_20871])).
% 13.26/5.72  tff(c_21007, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_20980])).
% 13.26/5.72  tff(c_21331, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_21007, c_44])).
% 13.26/5.72  tff(c_21442, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_636, c_21331])).
% 13.26/5.72  tff(c_52, plain, (![A_29, B_30, C_31]: (k8_relat_1(k3_xboole_0(A_29, B_30), C_31)=k8_relat_1(A_29, k8_relat_1(B_30, C_31)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.26/5.72  tff(c_42219, plain, (![C_942]: (k8_relat_1('#skF_6', k8_relat_1('#skF_7', C_942))=k8_relat_1('#skF_6', C_942) | ~v1_relat_1(C_942))), inference(superposition, [status(thm), theory('equality')], [c_21442, c_52])).
% 13.26/5.72  tff(c_54, plain, (k8_relat_1('#skF_6', k8_relat_1('#skF_7', '#skF_8'))!=k8_relat_1('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.26/5.72  tff(c_42228, plain, (~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_42219, c_54])).
% 13.26/5.72  tff(c_42240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_42228])).
% 13.26/5.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.26/5.72  
% 13.26/5.72  Inference rules
% 13.26/5.72  ----------------------
% 13.26/5.72  #Ref     : 0
% 13.26/5.72  #Sup     : 10675
% 13.26/5.72  #Fact    : 0
% 13.26/5.72  #Define  : 0
% 13.26/5.72  #Split   : 2
% 13.26/5.72  #Chain   : 0
% 13.26/5.72  #Close   : 0
% 13.26/5.72  
% 13.26/5.72  Ordering : KBO
% 13.26/5.72  
% 13.26/5.72  Simplification rules
% 13.26/5.72  ----------------------
% 13.26/5.72  #Subsume      : 3235
% 13.26/5.72  #Demod        : 9890
% 13.26/5.72  #Tautology    : 3691
% 13.26/5.72  #SimpNegUnit  : 0
% 13.26/5.72  #BackRed      : 109
% 13.26/5.72  
% 13.26/5.72  #Partial instantiations: 0
% 13.26/5.72  #Strategies tried      : 1
% 13.26/5.72  
% 13.26/5.72  Timing (in seconds)
% 13.26/5.72  ----------------------
% 13.26/5.72  Preprocessing        : 0.31
% 13.26/5.72  Parsing              : 0.16
% 13.26/5.72  CNF conversion       : 0.02
% 13.26/5.72  Main loop            : 4.63
% 13.26/5.72  Inferencing          : 1.03
% 13.26/5.72  Reduction            : 1.67
% 13.26/5.72  Demodulation         : 1.36
% 13.26/5.72  BG Simplification    : 0.11
% 13.26/5.72  Subsumption          : 1.51
% 13.26/5.72  Abstraction          : 0.18
% 13.26/5.72  MUC search           : 0.00
% 13.26/5.72  Cooper               : 0.00
% 13.26/5.72  Total                : 4.98
% 13.26/5.72  Index Insertion      : 0.00
% 13.26/5.72  Index Deletion       : 0.00
% 13.26/5.72  Index Matching       : 0.00
% 13.26/5.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
