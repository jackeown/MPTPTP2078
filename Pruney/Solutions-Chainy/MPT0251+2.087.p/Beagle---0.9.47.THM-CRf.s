%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:58 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :   70 ( 141 expanded)
%              Number of equality atoms :   46 ( 100 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_225,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_230,plain,(
    ! [B_49] : k3_xboole_0(B_49,B_49) = B_49 ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_240,plain,(
    ! [B_49] : k2_xboole_0(B_49,B_49) = B_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_14])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_161,plain,(
    ! [B_9] : k3_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_129])).

tff(c_252,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_315,plain,(
    ! [B_55] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_252])).

tff(c_229,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_261,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_252])).

tff(c_321,plain,(
    ! [B_55] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_261])).

tff(c_329,plain,(
    ! [B_55] : k4_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_321])).

tff(c_98,plain,(
    ! [A_39] : k2_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_371,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),B_60) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_387,plain,(
    ! [A_39] : k4_xboole_0(k1_xboole_0,A_39) = k4_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_371])).

tff(c_408,plain,(
    ! [A_39] : k4_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_387])).

tff(c_482,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_491,plain,(
    ! [A_39] : k5_xboole_0(A_39,k1_xboole_0) = k2_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_482])).

tff(c_503,plain,(
    ! [A_39] : k5_xboole_0(A_39,k1_xboole_0) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_491])).

tff(c_412,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_261])).

tff(c_24,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_728,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_tarski(k2_tarski(A_89,B_90),C_91)
      | ~ r2_hidden(B_90,C_91)
      | ~ r2_hidden(A_89,C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1785,plain,(
    ! [A_116,C_117] :
      ( r1_tarski(k1_tarski(A_116),C_117)
      | ~ r2_hidden(A_116,C_117)
      | ~ r2_hidden(A_116,C_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_728])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2010,plain,(
    ! [A_123,C_124] :
      ( k3_xboole_0(k1_tarski(A_123),C_124) = k1_tarski(A_123)
      | ~ r2_hidden(A_123,C_124) ) ),
    inference(resolution,[status(thm)],[c_1785,c_16])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2022,plain,(
    ! [A_123,C_124] :
      ( k5_xboole_0(k1_tarski(A_123),k1_tarski(A_123)) = k4_xboole_0(k1_tarski(A_123),C_124)
      | ~ r2_hidden(A_123,C_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2010,c_10])).

tff(c_2049,plain,(
    ! [A_125,C_126] :
      ( k4_xboole_0(k1_tarski(A_125),C_126) = k1_xboole_0
      | ~ r2_hidden(A_125,C_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_2022])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2063,plain,(
    ! [C_126,A_125] :
      ( k2_xboole_0(C_126,k1_tarski(A_125)) = k5_xboole_0(C_126,k1_xboole_0)
      | ~ r2_hidden(A_125,C_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2049,c_22])).

tff(c_2105,plain,(
    ! [C_128,A_129] :
      ( k2_xboole_0(C_128,k1_tarski(A_129)) = C_128
      | ~ r2_hidden(A_129,C_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_2063])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_2187,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2105,c_44])).

tff(c_2247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:41:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.54  
% 3.44/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.54  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.44/1.54  
% 3.44/1.54  %Foreground sorts:
% 3.44/1.54  
% 3.44/1.54  
% 3.44/1.54  %Background operators:
% 3.44/1.54  
% 3.44/1.54  
% 3.44/1.54  %Foreground operators:
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.54  
% 3.44/1.56  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.44/1.56  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.56  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.44/1.56  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.44/1.56  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.44/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.44/1.56  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.44/1.56  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.44/1.56  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.44/1.56  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.44/1.56  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.56  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.44/1.56  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.44/1.56  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.56  tff(c_225, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_230, plain, (![B_49]: (k3_xboole_0(B_49, B_49)=B_49)), inference(resolution, [status(thm)], [c_8, c_225])).
% 3.44/1.56  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.56  tff(c_240, plain, (![B_49]: (k2_xboole_0(B_49, B_49)=B_49)), inference(superposition, [status(thm), theory('equality')], [c_230, c_14])).
% 3.44/1.56  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.56  tff(c_82, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.56  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.56  tff(c_129, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 3.44/1.56  tff(c_161, plain, (![B_9]: (k3_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_129])).
% 3.44/1.56  tff(c_252, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.56  tff(c_315, plain, (![B_55]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_55))), inference(superposition, [status(thm), theory('equality')], [c_161, c_252])).
% 3.44/1.56  tff(c_229, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_225])).
% 3.44/1.56  tff(c_261, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_229, c_252])).
% 3.44/1.56  tff(c_321, plain, (![B_55]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_55))), inference(superposition, [status(thm), theory('equality')], [c_315, c_261])).
% 3.44/1.56  tff(c_329, plain, (![B_55]: (k4_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_321])).
% 3.44/1.56  tff(c_98, plain, (![A_39]: (k2_xboole_0(k1_xboole_0, A_39)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 3.44/1.56  tff(c_371, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), B_60)=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.56  tff(c_387, plain, (![A_39]: (k4_xboole_0(k1_xboole_0, A_39)=k4_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_98, c_371])).
% 3.44/1.56  tff(c_408, plain, (![A_39]: (k4_xboole_0(A_39, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_329, c_387])).
% 3.44/1.56  tff(c_482, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.56  tff(c_491, plain, (![A_39]: (k5_xboole_0(A_39, k1_xboole_0)=k2_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_408, c_482])).
% 3.44/1.56  tff(c_503, plain, (![A_39]: (k5_xboole_0(A_39, k1_xboole_0)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_240, c_491])).
% 3.44/1.56  tff(c_412, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_408, c_261])).
% 3.44/1.56  tff(c_24, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.56  tff(c_728, plain, (![A_89, B_90, C_91]: (r1_tarski(k2_tarski(A_89, B_90), C_91) | ~r2_hidden(B_90, C_91) | ~r2_hidden(A_89, C_91))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.44/1.56  tff(c_1785, plain, (![A_116, C_117]: (r1_tarski(k1_tarski(A_116), C_117) | ~r2_hidden(A_116, C_117) | ~r2_hidden(A_116, C_117))), inference(superposition, [status(thm), theory('equality')], [c_24, c_728])).
% 3.44/1.56  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.56  tff(c_2010, plain, (![A_123, C_124]: (k3_xboole_0(k1_tarski(A_123), C_124)=k1_tarski(A_123) | ~r2_hidden(A_123, C_124))), inference(resolution, [status(thm)], [c_1785, c_16])).
% 3.44/1.56  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.56  tff(c_2022, plain, (![A_123, C_124]: (k5_xboole_0(k1_tarski(A_123), k1_tarski(A_123))=k4_xboole_0(k1_tarski(A_123), C_124) | ~r2_hidden(A_123, C_124))), inference(superposition, [status(thm), theory('equality')], [c_2010, c_10])).
% 3.44/1.56  tff(c_2049, plain, (![A_125, C_126]: (k4_xboole_0(k1_tarski(A_125), C_126)=k1_xboole_0 | ~r2_hidden(A_125, C_126))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_2022])).
% 3.44/1.56  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.56  tff(c_2063, plain, (![C_126, A_125]: (k2_xboole_0(C_126, k1_tarski(A_125))=k5_xboole_0(C_126, k1_xboole_0) | ~r2_hidden(A_125, C_126))), inference(superposition, [status(thm), theory('equality')], [c_2049, c_22])).
% 3.44/1.56  tff(c_2105, plain, (![C_128, A_129]: (k2_xboole_0(C_128, k1_tarski(A_129))=C_128 | ~r2_hidden(A_129, C_128))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_2063])).
% 3.44/1.56  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.56  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.44/1.56  tff(c_44, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 3.44/1.56  tff(c_2187, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2105, c_44])).
% 3.44/1.56  tff(c_2247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2187])).
% 3.44/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.56  
% 3.44/1.56  Inference rules
% 3.44/1.56  ----------------------
% 3.44/1.56  #Ref     : 0
% 3.44/1.56  #Sup     : 522
% 3.44/1.56  #Fact    : 0
% 3.44/1.56  #Define  : 0
% 3.44/1.56  #Split   : 0
% 3.44/1.56  #Chain   : 0
% 3.44/1.56  #Close   : 0
% 3.44/1.56  
% 3.44/1.56  Ordering : KBO
% 3.44/1.56  
% 3.44/1.56  Simplification rules
% 3.44/1.56  ----------------------
% 3.44/1.56  #Subsume      : 31
% 3.44/1.56  #Demod        : 563
% 3.44/1.56  #Tautology    : 418
% 3.44/1.56  #SimpNegUnit  : 0
% 3.44/1.56  #BackRed      : 3
% 3.44/1.56  
% 3.44/1.56  #Partial instantiations: 0
% 3.44/1.56  #Strategies tried      : 1
% 3.44/1.56  
% 3.44/1.56  Timing (in seconds)
% 3.44/1.56  ----------------------
% 3.44/1.56  Preprocessing        : 0.31
% 3.44/1.56  Parsing              : 0.17
% 3.44/1.56  CNF conversion       : 0.02
% 3.44/1.56  Main loop            : 0.49
% 3.44/1.56  Inferencing          : 0.17
% 3.44/1.56  Reduction            : 0.22
% 3.44/1.56  Demodulation         : 0.18
% 3.44/1.56  BG Simplification    : 0.02
% 3.44/1.56  Subsumption          : 0.06
% 3.44/1.56  Abstraction          : 0.03
% 3.44/1.56  MUC search           : 0.00
% 3.44/1.56  Cooper               : 0.00
% 3.44/1.56  Total                : 0.84
% 3.44/1.56  Index Insertion      : 0.00
% 3.44/1.56  Index Deletion       : 0.00
% 3.44/1.56  Index Matching       : 0.00
% 3.44/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
