%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:11 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   68 (  81 expanded)
%              Number of leaves         :   34 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 (  83 expanded)
%              Number of equality atoms :   43 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_223,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_244,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k5_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_223])).

tff(c_254,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_244])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_247,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_223])).

tff(c_263,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_247])).

tff(c_42,plain,(
    ! [B_55] : k4_xboole_0(k1_tarski(B_55),k1_tarski(B_55)) != k1_tarski(B_55) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_264,plain,(
    ! [B_55] : k1_tarski(B_55) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_42])).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_52,B_53] : k3_xboole_0(k1_tarski(A_52),k2_tarski(A_52,B_53)) = k1_tarski(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k3_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k3_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_194,plain,(
    ! [A_75,B_76] :
      ( r1_xboole_0(A_75,B_76)
      | k3_xboole_0(A_75,B_76) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(B_79,A_80)
      | k3_xboole_0(A_80,B_79) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_194,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_301,plain,(
    ! [B_90,A_91] :
      ( k3_xboole_0(B_90,A_91) = k1_xboole_0
      | k3_xboole_0(A_91,B_90) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_215,c_2])).

tff(c_321,plain,(
    ! [A_17] : k3_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_301])).

tff(c_48,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_177,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = k1_xboole_0
      | ~ r1_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_177])).

tff(c_568,plain,(
    ! [A_102,B_103,C_104] : k3_xboole_0(k3_xboole_0(A_102,B_103),C_104) = k3_xboole_0(A_102,k3_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_630,plain,(
    ! [C_104] : k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_xboole_0('#skF_3',C_104)) = k3_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_568])).

tff(c_855,plain,(
    ! [C_115] : k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_xboole_0('#skF_3',C_115)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_630])).

tff(c_221,plain,(
    ! [B_79,A_80] :
      ( k3_xboole_0(B_79,A_80) = k1_xboole_0
      | k3_xboole_0(A_80,B_79) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_215,c_2])).

tff(c_974,plain,(
    ! [C_117] : k3_xboole_0(k3_xboole_0('#skF_3',C_117),k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_221])).

tff(c_1108,plain,(
    ! [B_119] : k3_xboole_0('#skF_3',k3_xboole_0(B_119,k2_tarski('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_974])).

tff(c_1165,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1108])).

tff(c_36,plain,(
    ! [B_49,A_48] :
      ( k3_xboole_0(B_49,k1_tarski(A_48)) = k1_tarski(A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1206,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_36])).

tff(c_1222,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1206])).

tff(c_1224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_1222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n017.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:52:31 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.49  
% 3.00/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.49  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.00/1.49  
% 3.00/1.49  %Foreground sorts:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Background operators:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Foreground operators:
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.00/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.00/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.00/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.49  
% 3.00/1.50  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.00/1.50  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.00/1.50  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.00/1.50  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.00/1.50  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.00/1.50  tff(f_80, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.00/1.50  tff(f_69, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.00/1.50  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.00/1.50  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.00/1.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.00/1.50  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.00/1.50  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.00/1.50  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.00/1.50  tff(c_16, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.00/1.50  tff(c_223, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.00/1.50  tff(c_244, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k5_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_223])).
% 3.00/1.50  tff(c_254, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_244])).
% 3.00/1.50  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.50  tff(c_247, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_223])).
% 3.00/1.50  tff(c_263, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_254, c_247])).
% 3.00/1.50  tff(c_42, plain, (![B_55]: (k4_xboole_0(k1_tarski(B_55), k1_tarski(B_55))!=k1_tarski(B_55))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.00/1.50  tff(c_264, plain, (![B_55]: (k1_tarski(B_55)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_263, c_42])).
% 3.00/1.50  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.00/1.50  tff(c_40, plain, (![A_52, B_53]: (k3_xboole_0(k1_tarski(A_52), k2_tarski(A_52, B_53))=k1_tarski(A_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.00/1.50  tff(c_14, plain, (![A_12, B_13, C_14]: (k3_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k3_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.50  tff(c_18, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.50  tff(c_194, plain, (![A_75, B_76]: (r1_xboole_0(A_75, B_76) | k3_xboole_0(A_75, B_76)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.50  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.50  tff(c_215, plain, (![B_79, A_80]: (r1_xboole_0(B_79, A_80) | k3_xboole_0(A_80, B_79)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_194, c_8])).
% 3.00/1.50  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.50  tff(c_301, plain, (![B_90, A_91]: (k3_xboole_0(B_90, A_91)=k1_xboole_0 | k3_xboole_0(A_91, B_90)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_215, c_2])).
% 3.00/1.50  tff(c_321, plain, (![A_17]: (k3_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_301])).
% 3.00/1.50  tff(c_48, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.00/1.50  tff(c_177, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=k1_xboole_0 | ~r1_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.50  tff(c_185, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_177])).
% 3.00/1.50  tff(c_568, plain, (![A_102, B_103, C_104]: (k3_xboole_0(k3_xboole_0(A_102, B_103), C_104)=k3_xboole_0(A_102, k3_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.50  tff(c_630, plain, (![C_104]: (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', C_104))=k3_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_185, c_568])).
% 3.00/1.50  tff(c_855, plain, (![C_115]: (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', C_115))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_321, c_630])).
% 3.00/1.50  tff(c_221, plain, (![B_79, A_80]: (k3_xboole_0(B_79, A_80)=k1_xboole_0 | k3_xboole_0(A_80, B_79)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_215, c_2])).
% 3.00/1.50  tff(c_974, plain, (![C_117]: (k3_xboole_0(k3_xboole_0('#skF_3', C_117), k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_855, c_221])).
% 3.00/1.50  tff(c_1108, plain, (![B_119]: (k3_xboole_0('#skF_3', k3_xboole_0(B_119, k2_tarski('#skF_1', '#skF_2')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_974])).
% 3.00/1.50  tff(c_1165, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40, c_1108])).
% 3.00/1.50  tff(c_36, plain, (![B_49, A_48]: (k3_xboole_0(B_49, k1_tarski(A_48))=k1_tarski(A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.50  tff(c_1206, plain, (k1_tarski('#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1165, c_36])).
% 3.00/1.50  tff(c_1222, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1206])).
% 3.00/1.50  tff(c_1224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_1222])).
% 3.00/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  Inference rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Ref     : 0
% 3.00/1.50  #Sup     : 296
% 3.00/1.50  #Fact    : 0
% 3.00/1.50  #Define  : 0
% 3.00/1.50  #Split   : 0
% 3.00/1.50  #Chain   : 0
% 3.00/1.50  #Close   : 0
% 3.00/1.50  
% 3.00/1.50  Ordering : KBO
% 3.00/1.50  
% 3.00/1.50  Simplification rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Subsume      : 12
% 3.00/1.50  #Demod        : 163
% 3.00/1.50  #Tautology    : 199
% 3.00/1.50  #SimpNegUnit  : 9
% 3.00/1.50  #BackRed      : 1
% 3.00/1.50  
% 3.00/1.50  #Partial instantiations: 0
% 3.00/1.50  #Strategies tried      : 1
% 3.00/1.50  
% 3.00/1.50  Timing (in seconds)
% 3.00/1.50  ----------------------
% 3.00/1.51  Preprocessing        : 0.32
% 3.00/1.51  Parsing              : 0.17
% 3.00/1.51  CNF conversion       : 0.02
% 3.00/1.51  Main loop            : 0.42
% 3.00/1.51  Inferencing          : 0.15
% 3.00/1.51  Reduction            : 0.16
% 3.00/1.51  Demodulation         : 0.12
% 3.00/1.51  BG Simplification    : 0.02
% 3.00/1.51  Subsumption          : 0.06
% 3.00/1.51  Abstraction          : 0.02
% 3.00/1.51  MUC search           : 0.00
% 3.00/1.51  Cooper               : 0.00
% 3.00/1.51  Total                : 0.76
% 3.00/1.51  Index Insertion      : 0.00
% 3.00/1.51  Index Deletion       : 0.00
% 3.00/1.51  Index Matching       : 0.00
% 3.00/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
