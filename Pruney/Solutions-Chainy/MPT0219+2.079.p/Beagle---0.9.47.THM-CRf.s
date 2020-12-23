%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:59 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 359 expanded)
%              Number of leaves         :   31 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :   58 ( 380 expanded)
%              Number of equality atoms :   48 ( 302 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_38,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_63] : k3_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_131])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_63] : k3_xboole_0(A_63,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2])).

tff(c_285,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_294,plain,(
    ! [A_63] : k5_xboole_0(A_63,k1_xboole_0) = k4_xboole_0(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_285])).

tff(c_336,plain,(
    ! [A_76] : k4_xboole_0(A_76,k1_xboole_0) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_294])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_346,plain,(
    ! [A_76] : k4_xboole_0(A_76,A_76) = k3_xboole_0(A_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_14])).

tff(c_359,plain,(
    ! [A_76] : k4_xboole_0(A_76,A_76) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_346])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_306,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_285])).

tff(c_432,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_306])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_349,plain,(
    ! [A_76] : k5_xboole_0(k1_xboole_0,A_76) = k2_xboole_0(k1_xboole_0,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_20])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_450,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2397,plain,(
    ! [A_153,B_154,C_155] : k5_xboole_0(A_153,k5_xboole_0(k3_xboole_0(A_153,B_154),C_155)) = k5_xboole_0(k4_xboole_0(A_153,B_154),C_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_450])).

tff(c_2493,plain,(
    ! [A_3,C_155] : k5_xboole_0(k4_xboole_0(A_3,A_3),C_155) = k5_xboole_0(A_3,k5_xboole_0(A_3,C_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2397])).

tff(c_3356,plain,(
    ! [A_170,C_171] : k5_xboole_0(A_170,k5_xboole_0(A_170,C_171)) = k2_xboole_0(k1_xboole_0,C_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_359,c_2493])).

tff(c_3428,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_3356])).

tff(c_3454,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3428])).

tff(c_3462,plain,(
    ! [A_76] : k5_xboole_0(k1_xboole_0,A_76) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_349])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2512,plain,(
    ! [A_3,C_155] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_155)) = k2_xboole_0(k1_xboole_0,C_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_359,c_2493])).

tff(c_3616,plain,(
    ! [A_174,C_175] : k5_xboole_0(A_174,k5_xboole_0(A_174,C_175)) = C_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_2512])).

tff(c_5658,plain,(
    ! [A_206,B_207] : k5_xboole_0(A_206,k2_xboole_0(A_206,B_207)) = k4_xboole_0(B_207,A_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3616])).

tff(c_5742,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5658])).

tff(c_5760,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_5742])).

tff(c_2466,plain,(
    ! [A_153,B_154] : k5_xboole_0(k4_xboole_0(A_153,B_154),k3_xboole_0(A_153,B_154)) = k5_xboole_0(A_153,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_2397])).

tff(c_2508,plain,(
    ! [A_153,B_154] : k5_xboole_0(k4_xboole_0(A_153,B_154),k3_xboole_0(A_153,B_154)) = A_153 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2466])).

tff(c_5764,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1'))) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5760,c_2508])).

tff(c_5800,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3462,c_2,c_5764])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5902,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5800,c_8])).

tff(c_36,plain,(
    ! [B_49,A_48] :
      ( B_49 = A_48
      | ~ r1_tarski(k1_tarski(A_48),k1_tarski(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5933,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5902,c_36])).

tff(c_5940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_5933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:51:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.99  
% 5.05/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.99  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.05/1.99  
% 5.05/1.99  %Foreground sorts:
% 5.05/1.99  
% 5.05/1.99  
% 5.05/1.99  %Background operators:
% 5.05/1.99  
% 5.05/1.99  
% 5.05/1.99  %Foreground operators:
% 5.05/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.05/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.05/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.05/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.05/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.05/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.05/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.05/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.05/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.05/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.05/1.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.05/1.99  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.05/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.05/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.05/1.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.05/1.99  
% 5.05/2.00  tff(f_70, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 5.05/2.00  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.05/2.00  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.05/2.00  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.05/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.05/2.00  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.05/2.00  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.05/2.00  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.05/2.00  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.05/2.00  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.05/2.00  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.05/2.00  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.05/2.00  tff(c_38, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.05/2.00  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.05/2.00  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.05/2.00  tff(c_131, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.05/2.00  tff(c_149, plain, (![A_63]: (k3_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_131])).
% 5.05/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.05/2.00  tff(c_157, plain, (![A_63]: (k3_xboole_0(A_63, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_149, c_2])).
% 5.05/2.00  tff(c_285, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.05/2.00  tff(c_294, plain, (![A_63]: (k5_xboole_0(A_63, k1_xboole_0)=k4_xboole_0(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_285])).
% 5.05/2.00  tff(c_336, plain, (![A_76]: (k4_xboole_0(A_76, k1_xboole_0)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_294])).
% 5.05/2.00  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.05/2.00  tff(c_346, plain, (![A_76]: (k4_xboole_0(A_76, A_76)=k3_xboole_0(A_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_336, c_14])).
% 5.05/2.00  tff(c_359, plain, (![A_76]: (k4_xboole_0(A_76, A_76)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_157, c_346])).
% 5.05/2.00  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.05/2.00  tff(c_306, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_285])).
% 5.05/2.00  tff(c_432, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_359, c_306])).
% 5.05/2.00  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.05/2.00  tff(c_349, plain, (![A_76]: (k5_xboole_0(k1_xboole_0, A_76)=k2_xboole_0(k1_xboole_0, A_76))), inference(superposition, [status(thm), theory('equality')], [c_336, c_20])).
% 5.05/2.00  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.05/2.00  tff(c_450, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.05/2.00  tff(c_2397, plain, (![A_153, B_154, C_155]: (k5_xboole_0(A_153, k5_xboole_0(k3_xboole_0(A_153, B_154), C_155))=k5_xboole_0(k4_xboole_0(A_153, B_154), C_155))), inference(superposition, [status(thm), theory('equality')], [c_6, c_450])).
% 5.05/2.00  tff(c_2493, plain, (![A_3, C_155]: (k5_xboole_0(k4_xboole_0(A_3, A_3), C_155)=k5_xboole_0(A_3, k5_xboole_0(A_3, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2397])).
% 5.05/2.00  tff(c_3356, plain, (![A_170, C_171]: (k5_xboole_0(A_170, k5_xboole_0(A_170, C_171))=k2_xboole_0(k1_xboole_0, C_171))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_359, c_2493])).
% 5.05/2.00  tff(c_3428, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_432, c_3356])).
% 5.05/2.00  tff(c_3454, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3428])).
% 5.05/2.00  tff(c_3462, plain, (![A_76]: (k5_xboole_0(k1_xboole_0, A_76)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_349])).
% 5.05/2.00  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.05/2.00  tff(c_2512, plain, (![A_3, C_155]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_155))=k2_xboole_0(k1_xboole_0, C_155))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_359, c_2493])).
% 5.05/2.00  tff(c_3616, plain, (![A_174, C_175]: (k5_xboole_0(A_174, k5_xboole_0(A_174, C_175))=C_175)), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_2512])).
% 5.05/2.00  tff(c_5658, plain, (![A_206, B_207]: (k5_xboole_0(A_206, k2_xboole_0(A_206, B_207))=k4_xboole_0(B_207, A_206))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3616])).
% 5.05/2.00  tff(c_5742, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5658])).
% 5.05/2.00  tff(c_5760, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_432, c_5742])).
% 5.05/2.00  tff(c_2466, plain, (![A_153, B_154]: (k5_xboole_0(k4_xboole_0(A_153, B_154), k3_xboole_0(A_153, B_154))=k5_xboole_0(A_153, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_432, c_2397])).
% 5.05/2.00  tff(c_2508, plain, (![A_153, B_154]: (k5_xboole_0(k4_xboole_0(A_153, B_154), k3_xboole_0(A_153, B_154))=A_153)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2466])).
% 5.05/2.00  tff(c_5764, plain, (k5_xboole_0(k1_xboole_0, k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1')))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5760, c_2508])).
% 5.05/2.00  tff(c_5800, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3462, c_2, c_5764])).
% 5.05/2.00  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.05/2.00  tff(c_5902, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5800, c_8])).
% 5.05/2.00  tff(c_36, plain, (![B_49, A_48]: (B_49=A_48 | ~r1_tarski(k1_tarski(A_48), k1_tarski(B_49)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.05/2.00  tff(c_5933, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_5902, c_36])).
% 5.05/2.00  tff(c_5940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_5933])).
% 5.05/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/2.00  
% 5.05/2.00  Inference rules
% 5.05/2.00  ----------------------
% 5.05/2.00  #Ref     : 0
% 5.05/2.00  #Sup     : 1429
% 5.05/2.00  #Fact    : 0
% 5.05/2.00  #Define  : 0
% 5.05/2.00  #Split   : 0
% 5.05/2.00  #Chain   : 0
% 5.05/2.00  #Close   : 0
% 5.05/2.00  
% 5.05/2.00  Ordering : KBO
% 5.05/2.00  
% 5.05/2.00  Simplification rules
% 5.05/2.00  ----------------------
% 5.05/2.00  #Subsume      : 35
% 5.05/2.00  #Demod        : 1716
% 5.05/2.00  #Tautology    : 1037
% 5.05/2.00  #SimpNegUnit  : 1
% 5.05/2.00  #BackRed      : 6
% 5.05/2.00  
% 5.05/2.00  #Partial instantiations: 0
% 5.05/2.00  #Strategies tried      : 1
% 5.05/2.00  
% 5.05/2.00  Timing (in seconds)
% 5.05/2.00  ----------------------
% 5.05/2.01  Preprocessing        : 0.32
% 5.05/2.01  Parsing              : 0.17
% 5.05/2.01  CNF conversion       : 0.02
% 5.05/2.01  Main loop            : 0.93
% 5.05/2.01  Inferencing          : 0.28
% 5.05/2.01  Reduction            : 0.45
% 5.05/2.01  Demodulation         : 0.38
% 5.05/2.01  BG Simplification    : 0.03
% 5.05/2.01  Subsumption          : 0.11
% 5.05/2.01  Abstraction          : 0.05
% 5.05/2.01  MUC search           : 0.00
% 5.05/2.01  Cooper               : 0.00
% 5.05/2.01  Total                : 1.28
% 5.05/2.01  Index Insertion      : 0.00
% 5.05/2.01  Index Deletion       : 0.00
% 5.05/2.01  Index Matching       : 0.00
% 5.05/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
