%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:59 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 301 expanded)
%              Number of leaves         :   36 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          :   60 ( 325 expanded)
%              Number of equality atoms :   53 ( 214 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_77,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_50,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_52,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_8])).

tff(c_155,plain,(
    ! [A_83,B_84] : k3_tarski(k2_tarski(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_155])).

tff(c_170,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_164])).

tff(c_185,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_14])).

tff(c_192,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_185,c_8])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_18])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_284,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_293,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_284])).

tff(c_296,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_293])).

tff(c_46,plain,(
    ! [B_72] : k4_xboole_0(k1_tarski(B_72),k1_tarski(B_72)) != k1_tarski(B_72) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_297,plain,(
    ! [B_72] : k1_tarski(B_72) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_46])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_199,plain,(
    ! [A_9] : k5_xboole_0(A_9,'#skF_1') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_12])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_568,plain,(
    ! [A_113,B_114] : k5_xboole_0(k5_xboole_0(A_113,B_114),k2_xboole_0(A_113,B_114)) = k3_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_620,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_568])).

tff(c_626,plain,(
    ! [A_1] : k5_xboole_0('#skF_1',A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_4,c_620])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_198,plain,(
    ! [A_8] : k4_xboole_0('#skF_1',A_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_192,c_10])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_392,plain,(
    ! [A_106,B_107,C_108] : k5_xboole_0(k5_xboole_0(A_106,B_107),C_108) = k5_xboole_0(A_106,k5_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_444,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k5_xboole_0(B_110,k5_xboole_0(A_109,B_110))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_200])).

tff(c_490,plain,(
    ! [A_111] : k5_xboole_0(A_111,k5_xboole_0('#skF_1',A_111)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_444])).

tff(c_527,plain,(
    ! [B_6] : k5_xboole_0(k3_xboole_0('#skF_1',B_6),k4_xboole_0('#skF_1',B_6)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_490])).

tff(c_544,plain,(
    ! [B_6] : k3_xboole_0('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_198,c_527])).

tff(c_194,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_170])).

tff(c_617,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_568])).

tff(c_625,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_617])).

tff(c_703,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_626,c_625])).

tff(c_196,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_139])).

tff(c_704,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_196])).

tff(c_30,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_717,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_30])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  
% 2.61/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.40  
% 2.61/1.40  %Foreground sorts:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Background operators:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Foreground operators:
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.40  
% 2.61/1.42  tff(f_77, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.61/1.42  tff(f_81, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.61/1.42  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.61/1.42  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.61/1.42  tff(f_71, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.61/1.42  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.61/1.42  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.61/1.42  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.42  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.61/1.42  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.61/1.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.61/1.42  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.61/1.42  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.61/1.42  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.61/1.42  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.61/1.42  tff(c_50, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.42  tff(c_52, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.42  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.42  tff(c_125, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_14])).
% 2.61/1.42  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.42  tff(c_139, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_8])).
% 2.61/1.42  tff(c_155, plain, (![A_83, B_84]: (k3_tarski(k2_tarski(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.42  tff(c_164, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_139, c_155])).
% 2.61/1.42  tff(c_170, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_164])).
% 2.61/1.42  tff(c_185, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_170, c_14])).
% 2.61/1.42  tff(c_192, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_185, c_8])).
% 2.61/1.42  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.42  tff(c_200, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_18])).
% 2.61/1.42  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.42  tff(c_284, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.42  tff(c_293, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_284])).
% 2.61/1.42  tff(c_296, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_293])).
% 2.61/1.42  tff(c_46, plain, (![B_72]: (k4_xboole_0(k1_tarski(B_72), k1_tarski(B_72))!=k1_tarski(B_72))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.61/1.42  tff(c_297, plain, (![B_72]: (k1_tarski(B_72)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_46])).
% 2.61/1.42  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.42  tff(c_199, plain, (![A_9]: (k5_xboole_0(A_9, '#skF_1')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_12])).
% 2.61/1.42  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.42  tff(c_568, plain, (![A_113, B_114]: (k5_xboole_0(k5_xboole_0(A_113, B_114), k2_xboole_0(A_113, B_114))=k3_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.42  tff(c_620, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_568])).
% 2.61/1.42  tff(c_626, plain, (![A_1]: (k5_xboole_0('#skF_1', A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_4, c_620])).
% 2.61/1.42  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.42  tff(c_198, plain, (![A_8]: (k4_xboole_0('#skF_1', A_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_192, c_10])).
% 2.61/1.42  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.42  tff(c_392, plain, (![A_106, B_107, C_108]: (k5_xboole_0(k5_xboole_0(A_106, B_107), C_108)=k5_xboole_0(A_106, k5_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.42  tff(c_444, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k5_xboole_0(B_110, k5_xboole_0(A_109, B_110)))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_392, c_200])).
% 2.61/1.42  tff(c_490, plain, (![A_111]: (k5_xboole_0(A_111, k5_xboole_0('#skF_1', A_111))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_199, c_444])).
% 2.61/1.42  tff(c_527, plain, (![B_6]: (k5_xboole_0(k3_xboole_0('#skF_1', B_6), k4_xboole_0('#skF_1', B_6))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_490])).
% 2.61/1.42  tff(c_544, plain, (![B_6]: (k3_xboole_0('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_198, c_527])).
% 2.61/1.42  tff(c_194, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_170])).
% 2.61/1.42  tff(c_617, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_568])).
% 2.61/1.42  tff(c_625, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_544, c_617])).
% 2.61/1.42  tff(c_703, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_626, c_625])).
% 2.61/1.42  tff(c_196, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_139])).
% 2.61/1.42  tff(c_704, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_703, c_196])).
% 2.61/1.42  tff(c_30, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.42  tff(c_717, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_704, c_30])).
% 2.61/1.42  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_717])).
% 2.61/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.42  
% 2.61/1.42  Inference rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Ref     : 0
% 2.61/1.42  #Sup     : 169
% 2.61/1.42  #Fact    : 0
% 2.61/1.42  #Define  : 0
% 2.61/1.42  #Split   : 0
% 2.61/1.42  #Chain   : 0
% 2.61/1.42  #Close   : 0
% 2.61/1.42  
% 2.61/1.42  Ordering : KBO
% 2.61/1.42  
% 2.61/1.42  Simplification rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Subsume      : 0
% 2.61/1.42  #Demod        : 94
% 2.61/1.42  #Tautology    : 126
% 2.61/1.42  #SimpNegUnit  : 3
% 2.61/1.42  #BackRed      : 16
% 2.61/1.42  
% 2.61/1.42  #Partial instantiations: 0
% 2.61/1.42  #Strategies tried      : 1
% 2.61/1.42  
% 2.61/1.42  Timing (in seconds)
% 2.61/1.42  ----------------------
% 2.61/1.42  Preprocessing        : 0.34
% 2.61/1.42  Parsing              : 0.19
% 2.61/1.42  CNF conversion       : 0.02
% 2.61/1.42  Main loop            : 0.25
% 2.61/1.42  Inferencing          : 0.09
% 2.61/1.42  Reduction            : 0.09
% 2.61/1.42  Demodulation         : 0.07
% 2.61/1.42  BG Simplification    : 0.02
% 2.61/1.42  Subsumption          : 0.03
% 2.61/1.42  Abstraction          : 0.02
% 2.61/1.42  MUC search           : 0.00
% 2.61/1.42  Cooper               : 0.00
% 2.61/1.42  Total                : 0.62
% 2.61/1.42  Index Insertion      : 0.00
% 2.61/1.42  Index Deletion       : 0.00
% 2.61/1.42  Index Matching       : 0.00
% 2.61/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
