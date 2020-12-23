%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:25 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   67 (  75 expanded)
%              Number of leaves         :   39 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  58 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_38,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_2'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,(
    ! [A_10,C_81] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_81,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_131,plain,(
    ! [C_82] : ~ r2_hidden(C_82,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_127])).

tff(c_136,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_345,plain,(
    ! [B_100,A_101] :
      ( k3_xboole_0(B_100,k2_zfmisc_1(k1_relat_1(B_100),A_101)) = k8_relat_1(A_101,B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k4_xboole_0(B_88,A_87)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_156])).

tff(c_191,plain,(
    ! [A_90] : k2_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_165])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [A_90] : k2_xboole_0(k1_xboole_0,A_90) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_2])).

tff(c_143,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_152,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k4_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_143])).

tff(c_169,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_152])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_175,plain,(
    ! [A_89] : k5_xboole_0(k1_xboole_0,A_89) = k2_xboole_0(k1_xboole_0,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_18])).

tff(c_264,plain,(
    ! [A_95] : k5_xboole_0(k1_xboole_0,A_95) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_175])).

tff(c_8,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_275,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,B_9) = k3_xboole_0(k1_xboole_0,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_8])).

tff(c_297,plain,(
    ! [B_9] : k3_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_275])).

tff(c_355,plain,(
    ! [A_101] :
      ( k8_relat_1(A_101,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_297])).

tff(c_374,plain,(
    ! [A_101] : k8_relat_1(A_101,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_355])).

tff(c_42,plain,(
    k8_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.14/1.30  
% 2.14/1.30  %Foreground sorts:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Background operators:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Foreground operators:
% 2.14/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.14/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.14/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.14/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.14/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.14/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.14/1.30  
% 2.14/1.31  tff(f_77, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.14/1.31  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.14/1.31  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.14/1.31  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.14/1.31  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 2.14/1.31  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.14/1.31  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.14/1.31  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.14/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.14/1.31  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.14/1.31  tff(f_84, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 2.14/1.31  tff(c_38, plain, (![A_45]: (r2_hidden('#skF_2'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.31  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.31  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.31  tff(c_120, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.31  tff(c_127, plain, (![A_10, C_81]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_120])).
% 2.14/1.31  tff(c_131, plain, (![C_82]: (~r2_hidden(C_82, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_127])).
% 2.14/1.31  tff(c_136, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_131])).
% 2.14/1.31  tff(c_345, plain, (![B_100, A_101]: (k3_xboole_0(B_100, k2_zfmisc_1(k1_relat_1(B_100), A_101))=k8_relat_1(A_101, B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.14/1.31  tff(c_12, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.31  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.31  tff(c_156, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k4_xboole_0(B_88, A_87))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.31  tff(c_165, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_156])).
% 2.14/1.31  tff(c_191, plain, (![A_90]: (k2_xboole_0(A_90, k1_xboole_0)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_165])).
% 2.14/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.31  tff(c_197, plain, (![A_90]: (k2_xboole_0(k1_xboole_0, A_90)=A_90)), inference(superposition, [status(thm), theory('equality')], [c_191, c_2])).
% 2.14/1.31  tff(c_143, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.31  tff(c_152, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k4_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_143])).
% 2.14/1.31  tff(c_169, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_152])).
% 2.14/1.31  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.31  tff(c_175, plain, (![A_89]: (k5_xboole_0(k1_xboole_0, A_89)=k2_xboole_0(k1_xboole_0, A_89))), inference(superposition, [status(thm), theory('equality')], [c_169, c_18])).
% 2.14/1.31  tff(c_264, plain, (![A_95]: (k5_xboole_0(k1_xboole_0, A_95)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_175])).
% 2.14/1.31  tff(c_8, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.31  tff(c_275, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, B_9)=k3_xboole_0(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_264, c_8])).
% 2.14/1.31  tff(c_297, plain, (![B_9]: (k3_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_275])).
% 2.14/1.31  tff(c_355, plain, (![A_101]: (k8_relat_1(A_101, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_345, c_297])).
% 2.14/1.31  tff(c_374, plain, (![A_101]: (k8_relat_1(A_101, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_355])).
% 2.14/1.31  tff(c_42, plain, (k8_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.14/1.31  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_374, c_42])).
% 2.14/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  Inference rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Ref     : 0
% 2.14/1.31  #Sup     : 77
% 2.14/1.31  #Fact    : 0
% 2.14/1.31  #Define  : 0
% 2.14/1.31  #Split   : 0
% 2.14/1.31  #Chain   : 0
% 2.14/1.31  #Close   : 0
% 2.14/1.31  
% 2.14/1.31  Ordering : KBO
% 2.14/1.31  
% 2.14/1.31  Simplification rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Subsume      : 1
% 2.14/1.31  #Demod        : 27
% 2.14/1.31  #Tautology    : 61
% 2.14/1.31  #SimpNegUnit  : 2
% 2.14/1.31  #BackRed      : 1
% 2.14/1.31  
% 2.14/1.31  #Partial instantiations: 0
% 2.14/1.31  #Strategies tried      : 1
% 2.14/1.31  
% 2.14/1.31  Timing (in seconds)
% 2.14/1.31  ----------------------
% 2.37/1.31  Preprocessing        : 0.34
% 2.37/1.31  Parsing              : 0.18
% 2.37/1.31  CNF conversion       : 0.02
% 2.37/1.31  Main loop            : 0.20
% 2.37/1.31  Inferencing          : 0.08
% 2.37/1.31  Reduction            : 0.07
% 2.37/1.31  Demodulation         : 0.05
% 2.37/1.31  BG Simplification    : 0.02
% 2.37/1.31  Subsumption          : 0.02
% 2.37/1.31  Abstraction          : 0.01
% 2.37/1.31  MUC search           : 0.00
% 2.37/1.31  Cooper               : 0.00
% 2.37/1.31  Total                : 0.57
% 2.37/1.31  Index Insertion      : 0.00
% 2.37/1.31  Index Deletion       : 0.00
% 2.37/1.32  Index Matching       : 0.00
% 2.37/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
