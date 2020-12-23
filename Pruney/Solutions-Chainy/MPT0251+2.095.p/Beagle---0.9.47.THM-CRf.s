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
% DateTime   : Thu Dec  3 09:50:59 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  90 expanded)
%              Number of equality atoms :   40 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    ! [B_59,A_60] : k5_xboole_0(B_59,A_60) = k5_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_14])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_265,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_291,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_265])).

tff(c_294,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_291])).

tff(c_610,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_678,plain,(
    ! [A_7,C_91] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_610])).

tff(c_723,plain,(
    ! [A_7,C_91] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_678])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tarski(A_47),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_203,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1575,plain,(
    ! [A_132,B_133] :
      ( k3_xboole_0(k1_tarski(A_132),B_133) = k1_tarski(A_132)
      | ~ r2_hidden(A_132,B_133) ) ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1589,plain,(
    ! [A_132,B_133] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_132),B_133),k1_tarski(A_132)) = k2_xboole_0(k1_tarski(A_132),B_133)
      | ~ r2_hidden(A_132,B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_18])).

tff(c_2472,plain,(
    ! [A_151,B_152] :
      ( k2_xboole_0(k1_tarski(A_151),B_152) = B_152
      | ~ r2_hidden(A_151,B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_4,c_1589])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_288,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_265])).

tff(c_668,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k5_xboole_0(B_18,k3_xboole_0(A_17,B_18))) = k2_xboole_0(A_17,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_610])).

tff(c_722,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_668])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_478,plain,(
    ! [A_86,B_87] : k5_xboole_0(k5_xboole_0(A_86,B_87),k3_xboole_0(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1993,plain,(
    ! [A_141,B_142] : k5_xboole_0(k5_xboole_0(A_141,B_142),k3_xboole_0(B_142,A_141)) = k2_xboole_0(B_142,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_478])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k5_xboole_0(k5_xboole_0(A_14,B_15),C_16) = k5_xboole_0(A_14,k5_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2017,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k5_xboole_0(B_142,k3_xboole_0(B_142,A_141))) = k2_xboole_0(B_142,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_16])).

tff(c_2130,plain,(
    ! [B_142,A_141] : k2_xboole_0(B_142,A_141) = k2_xboole_0(A_141,B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_6,c_2017])).

tff(c_3276,plain,(
    ! [B_163,A_164] :
      ( k2_xboole_0(B_163,k1_tarski(A_164)) = B_163
      | ~ r2_hidden(A_164,B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2472,c_2130])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2155,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_40])).

tff(c_3295,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3276,c_2155])).

tff(c_3350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.78  
% 4.23/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.78  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.23/1.78  
% 4.23/1.78  %Foreground sorts:
% 4.23/1.78  
% 4.23/1.78  
% 4.23/1.78  %Background operators:
% 4.23/1.78  
% 4.23/1.78  
% 4.23/1.78  %Foreground operators:
% 4.23/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.23/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.23/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.23/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.23/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.23/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.23/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.23/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.23/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.23/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.78  
% 4.23/1.80  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.23/1.80  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.23/1.80  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.23/1.80  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.23/1.80  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.23/1.80  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.23/1.80  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.23/1.80  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.23/1.80  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.23/1.80  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.23/1.80  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.23/1.80  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.23/1.80  tff(c_110, plain, (![B_59, A_60]: (k5_xboole_0(B_59, A_60)=k5_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.23/1.80  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.23/1.80  tff(c_126, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_110, c_14])).
% 4.23/1.80  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.23/1.80  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.23/1.80  tff(c_265, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.23/1.80  tff(c_291, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_265])).
% 4.23/1.80  tff(c_294, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_291])).
% 4.23/1.80  tff(c_610, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.23/1.80  tff(c_678, plain, (![A_7, C_91]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_294, c_610])).
% 4.23/1.80  tff(c_723, plain, (![A_7, C_91]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_678])).
% 4.23/1.80  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.23/1.80  tff(c_36, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.23/1.80  tff(c_203, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.23/1.80  tff(c_1575, plain, (![A_132, B_133]: (k3_xboole_0(k1_tarski(A_132), B_133)=k1_tarski(A_132) | ~r2_hidden(A_132, B_133))), inference(resolution, [status(thm)], [c_36, c_203])).
% 4.23/1.80  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.23/1.80  tff(c_1589, plain, (![A_132, B_133]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_132), B_133), k1_tarski(A_132))=k2_xboole_0(k1_tarski(A_132), B_133) | ~r2_hidden(A_132, B_133))), inference(superposition, [status(thm), theory('equality')], [c_1575, c_18])).
% 4.23/1.80  tff(c_2472, plain, (![A_151, B_152]: (k2_xboole_0(k1_tarski(A_151), B_152)=B_152 | ~r2_hidden(A_151, B_152))), inference(demodulation, [status(thm), theory('equality')], [c_723, c_4, c_1589])).
% 4.23/1.80  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.80  tff(c_288, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_265])).
% 4.23/1.80  tff(c_668, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k5_xboole_0(B_18, k3_xboole_0(A_17, B_18)))=k2_xboole_0(A_17, B_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_610])).
% 4.23/1.80  tff(c_722, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_668])).
% 4.23/1.80  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.23/1.80  tff(c_478, plain, (![A_86, B_87]: (k5_xboole_0(k5_xboole_0(A_86, B_87), k3_xboole_0(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.23/1.80  tff(c_1993, plain, (![A_141, B_142]: (k5_xboole_0(k5_xboole_0(A_141, B_142), k3_xboole_0(B_142, A_141))=k2_xboole_0(B_142, A_141))), inference(superposition, [status(thm), theory('equality')], [c_4, c_478])).
% 4.23/1.80  tff(c_16, plain, (![A_14, B_15, C_16]: (k5_xboole_0(k5_xboole_0(A_14, B_15), C_16)=k5_xboole_0(A_14, k5_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.23/1.80  tff(c_2017, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k5_xboole_0(B_142, k3_xboole_0(B_142, A_141)))=k2_xboole_0(B_142, A_141))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_16])).
% 4.23/1.80  tff(c_2130, plain, (![B_142, A_141]: (k2_xboole_0(B_142, A_141)=k2_xboole_0(A_141, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_722, c_6, c_2017])).
% 4.23/1.80  tff(c_3276, plain, (![B_163, A_164]: (k2_xboole_0(B_163, k1_tarski(A_164))=B_163 | ~r2_hidden(A_164, B_163))), inference(superposition, [status(thm), theory('equality')], [c_2472, c_2130])).
% 4.23/1.80  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.23/1.80  tff(c_2155, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_40])).
% 4.23/1.80  tff(c_3295, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3276, c_2155])).
% 4.23/1.80  tff(c_3350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3295])).
% 4.23/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.80  
% 4.23/1.80  Inference rules
% 4.23/1.80  ----------------------
% 4.23/1.80  #Ref     : 0
% 4.23/1.80  #Sup     : 828
% 4.23/1.80  #Fact    : 0
% 4.23/1.80  #Define  : 0
% 4.23/1.80  #Split   : 0
% 4.23/1.80  #Chain   : 0
% 4.23/1.80  #Close   : 0
% 4.23/1.80  
% 4.23/1.80  Ordering : KBO
% 4.23/1.80  
% 4.23/1.80  Simplification rules
% 4.23/1.80  ----------------------
% 4.23/1.80  #Subsume      : 41
% 4.23/1.80  #Demod        : 485
% 4.23/1.80  #Tautology    : 458
% 4.23/1.80  #SimpNegUnit  : 0
% 4.23/1.80  #BackRed      : 2
% 4.23/1.80  
% 4.23/1.80  #Partial instantiations: 0
% 4.23/1.80  #Strategies tried      : 1
% 4.23/1.80  
% 4.23/1.80  Timing (in seconds)
% 4.23/1.80  ----------------------
% 4.23/1.80  Preprocessing        : 0.31
% 4.23/1.80  Parsing              : 0.16
% 4.23/1.80  CNF conversion       : 0.02
% 4.23/1.80  Main loop            : 0.67
% 4.23/1.80  Inferencing          : 0.22
% 4.23/1.80  Reduction            : 0.30
% 4.23/1.80  Demodulation         : 0.26
% 4.23/1.80  BG Simplification    : 0.03
% 4.23/1.80  Subsumption          : 0.08
% 4.23/1.80  Abstraction          : 0.04
% 4.23/1.80  MUC search           : 0.00
% 4.23/1.80  Cooper               : 0.00
% 4.23/1.80  Total                : 1.01
% 4.23/1.80  Index Insertion      : 0.00
% 4.23/1.80  Index Deletion       : 0.00
% 4.23/1.80  Index Matching       : 0.00
% 4.23/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
