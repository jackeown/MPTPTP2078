%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 114 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 117 expanded)
%              Number of equality atoms :   45 ( 103 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_40,B_41] : r1_tarski(k1_tarski(A_40),k2_tarski(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_15] : r1_tarski(k1_tarski(A_15),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_146,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_15] : k4_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_146])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_166])).

tff(c_329,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k5_xboole_0(A_76,B_77),C_78) = k5_xboole_0(A_76,k5_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_13,B_14] : k5_xboole_0(k5_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_346,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k5_xboole_0(B_77,k3_xboole_0(A_76,B_77))) = k2_xboole_0(A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_18])).

tff(c_411,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k4_xboole_0(B_80,A_79)) = k2_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_346])).

tff(c_443,plain,(
    ! [A_15] : k2_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k5_xboole_0(k1_tarski(A_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_411])).

tff(c_463,plain,(
    ! [A_83] : k2_xboole_0(k1_tarski(A_83),k1_tarski(A_83)) = k1_tarski(A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_443])).

tff(c_108,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_108])).

tff(c_469,plain,(
    ! [A_83] : k3_tarski(k1_tarski(k1_tarski(A_83))) = k1_tarski(A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_117])).

tff(c_36,plain,(
    ! [A_36,B_37] :
      ( k5_xboole_0(k1_tarski(A_36),k1_tarski(B_37)) = k2_tarski(A_36,B_37)
      | B_37 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(k1_tarski(A_34),k1_tarski(B_35))
      | B_35 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_137,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = A_56
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k1_tarski(A_34),k1_tarski(B_35)) = k1_tarski(A_34)
      | B_35 = A_34 ) ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_2164,plain,(
    ! [B_129,A_130] :
      ( k5_xboole_0(k1_tarski(B_129),k1_tarski(A_130)) = k2_xboole_0(k1_tarski(B_129),k1_tarski(A_130))
      | B_129 = A_130 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_411])).

tff(c_2815,plain,(
    ! [A_140,B_141] :
      ( k2_xboole_0(k1_tarski(A_140),k1_tarski(B_141)) = k2_tarski(A_140,B_141)
      | B_141 = A_140
      | B_141 = A_140 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2164])).

tff(c_30,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38])).

tff(c_2845,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2815,c_39])).

tff(c_2851,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2845,c_2845,c_39])).

tff(c_2854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_117,c_20,c_2851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.82  
% 4.51/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.82  %$ r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.51/1.82  
% 4.51/1.82  %Foreground sorts:
% 4.51/1.82  
% 4.51/1.82  
% 4.51/1.82  %Background operators:
% 4.51/1.82  
% 4.51/1.82  
% 4.51/1.82  %Foreground operators:
% 4.51/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.51/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.51/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.51/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.51/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.51/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.51/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.51/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.51/1.82  
% 4.51/1.83  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.51/1.83  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.51/1.83  tff(f_57, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 4.51/1.83  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.51/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.51/1.83  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.51/1.83  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.51/1.84  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.51/1.84  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.51/1.84  tff(f_67, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 4.51/1.84  tff(f_62, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.51/1.84  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.51/1.84  tff(f_70, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 4.51/1.84  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.51/1.84  tff(c_20, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.51/1.84  tff(c_58, plain, (![A_40, B_41]: (r1_tarski(k1_tarski(A_40), k2_tarski(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.51/1.84  tff(c_61, plain, (![A_15]: (r1_tarski(k1_tarski(A_15), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_58])).
% 4.51/1.84  tff(c_146, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.84  tff(c_157, plain, (![A_15]: (k4_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_146])).
% 4.51/1.84  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/1.84  tff(c_166, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.51/1.84  tff(c_175, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_166])).
% 4.51/1.84  tff(c_329, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k5_xboole_0(A_76, B_77), C_78)=k5_xboole_0(A_76, k5_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.84  tff(c_18, plain, (![A_13, B_14]: (k5_xboole_0(k5_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.51/1.84  tff(c_346, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k5_xboole_0(B_77, k3_xboole_0(A_76, B_77)))=k2_xboole_0(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_329, c_18])).
% 4.51/1.84  tff(c_411, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k4_xboole_0(B_80, A_79))=k2_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_346])).
% 4.51/1.84  tff(c_443, plain, (![A_15]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k5_xboole_0(k1_tarski(A_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_411])).
% 4.51/1.84  tff(c_463, plain, (![A_83]: (k2_xboole_0(k1_tarski(A_83), k1_tarski(A_83))=k1_tarski(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_443])).
% 4.51/1.84  tff(c_108, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.51/1.84  tff(c_117, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_20, c_108])).
% 4.51/1.84  tff(c_469, plain, (![A_83]: (k3_tarski(k1_tarski(k1_tarski(A_83)))=k1_tarski(A_83))), inference(superposition, [status(thm), theory('equality')], [c_463, c_117])).
% 4.51/1.84  tff(c_36, plain, (![A_36, B_37]: (k5_xboole_0(k1_tarski(A_36), k1_tarski(B_37))=k2_tarski(A_36, B_37) | B_37=A_36)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.51/1.84  tff(c_34, plain, (![A_34, B_35]: (r1_xboole_0(k1_tarski(A_34), k1_tarski(B_35)) | B_35=A_34)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.51/1.84  tff(c_137, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=A_56 | ~r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.84  tff(c_144, plain, (![A_34, B_35]: (k4_xboole_0(k1_tarski(A_34), k1_tarski(B_35))=k1_tarski(A_34) | B_35=A_34)), inference(resolution, [status(thm)], [c_34, c_137])).
% 4.51/1.84  tff(c_2164, plain, (![B_129, A_130]: (k5_xboole_0(k1_tarski(B_129), k1_tarski(A_130))=k2_xboole_0(k1_tarski(B_129), k1_tarski(A_130)) | B_129=A_130)), inference(superposition, [status(thm), theory('equality')], [c_144, c_411])).
% 4.51/1.84  tff(c_2815, plain, (![A_140, B_141]: (k2_xboole_0(k1_tarski(A_140), k1_tarski(B_141))=k2_tarski(A_140, B_141) | B_141=A_140 | B_141=A_140)), inference(superposition, [status(thm), theory('equality')], [c_36, c_2164])).
% 4.51/1.84  tff(c_30, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.51/1.84  tff(c_38, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.51/1.84  tff(c_39, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38])).
% 4.51/1.84  tff(c_2845, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2815, c_39])).
% 4.51/1.84  tff(c_2851, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2845, c_2845, c_39])).
% 4.51/1.84  tff(c_2854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_117, c_20, c_2851])).
% 4.51/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.84  
% 4.51/1.84  Inference rules
% 4.51/1.84  ----------------------
% 4.51/1.84  #Ref     : 0
% 4.51/1.84  #Sup     : 669
% 4.51/1.84  #Fact    : 0
% 4.51/1.84  #Define  : 0
% 4.51/1.84  #Split   : 0
% 4.51/1.84  #Chain   : 0
% 4.51/1.84  #Close   : 0
% 4.51/1.84  
% 4.51/1.84  Ordering : KBO
% 4.51/1.84  
% 4.51/1.84  Simplification rules
% 4.51/1.84  ----------------------
% 4.51/1.84  #Subsume      : 7
% 4.51/1.84  #Demod        : 541
% 4.51/1.84  #Tautology    : 319
% 4.51/1.84  #SimpNegUnit  : 0
% 4.51/1.84  #BackRed      : 1
% 4.51/1.84  
% 4.51/1.84  #Partial instantiations: 0
% 4.51/1.84  #Strategies tried      : 1
% 4.51/1.84  
% 4.51/1.84  Timing (in seconds)
% 4.51/1.84  ----------------------
% 4.61/1.84  Preprocessing        : 0.33
% 4.61/1.84  Parsing              : 0.17
% 4.61/1.84  CNF conversion       : 0.02
% 4.61/1.84  Main loop            : 0.73
% 4.61/1.84  Inferencing          : 0.24
% 4.61/1.84  Reduction            : 0.32
% 4.61/1.84  Demodulation         : 0.27
% 4.61/1.84  BG Simplification    : 0.04
% 4.61/1.84  Subsumption          : 0.10
% 4.61/1.84  Abstraction          : 0.05
% 4.61/1.84  MUC search           : 0.00
% 4.61/1.84  Cooper               : 0.00
% 4.61/1.84  Total                : 1.09
% 4.61/1.84  Index Insertion      : 0.00
% 4.61/1.84  Index Deletion       : 0.00
% 4.61/1.84  Index Matching       : 0.00
% 4.61/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
