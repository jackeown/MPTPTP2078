%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 111 expanded)
%              Number of leaves         :   35 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 118 expanded)
%              Number of equality atoms :   48 (  93 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_68] : k3_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_351,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_366,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = k4_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_351])).

tff(c_380,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_366])).

tff(c_208,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_208])).

tff(c_438,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k4_xboole_0(B_95,A_94)) = k2_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_453,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_438])).

tff(c_462,plain,(
    ! [A_96] : k2_xboole_0(A_96,k1_xboole_0) = A_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_453])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_208])).

tff(c_489,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_219])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_494,plain,(
    ! [A_98] : k5_xboole_0(A_98,k1_xboole_0) = k2_xboole_0(A_98,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_22])).

tff(c_512,plain,(
    ! [A_98] : k2_xboole_0(A_98,A_98) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_494])).

tff(c_24,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [A_51,B_52] :
      ( k5_xboole_0(k1_tarski(A_51),k1_tarski(B_52)) = k2_tarski(A_51,B_52)
      | B_52 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(k1_tarski(A_47),k1_tarski(B_48))
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_324,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = A_81
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_815,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(k1_tarski(A_118),k1_tarski(B_119)) = k1_tarski(A_118)
      | B_119 = A_118 ) ),
    inference(resolution,[status(thm)],[c_40,c_324])).

tff(c_956,plain,(
    ! [B_139,A_140] :
      ( k5_xboole_0(k1_tarski(B_139),k1_tarski(A_140)) = k2_xboole_0(k1_tarski(B_139),k1_tarski(A_140))
      | B_139 = A_140 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_22])).

tff(c_1111,plain,(
    ! [A_154,B_155] :
      ( k2_xboole_0(k1_tarski(A_154),k1_tarski(B_155)) = k2_tarski(A_154,B_155)
      | B_155 = A_154
      | B_155 = A_154 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_956])).

tff(c_38,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_47,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_1151,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_47])).

tff(c_1155,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_1151,c_47])).

tff(c_1158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_24,c_1155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:55:02 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.46  
% 3.01/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.46  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.01/1.46  
% 3.01/1.46  %Foreground sorts:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Background operators:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Foreground operators:
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.01/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.01/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.46  
% 3.01/1.47  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.01/1.47  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.01/1.47  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.01/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.01/1.47  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.01/1.47  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.01/1.47  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.01/1.47  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.01/1.47  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.01/1.47  tff(f_77, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.01/1.47  tff(f_70, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.01/1.47  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.01/1.47  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.01/1.47  tff(f_80, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.01/1.47  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.01/1.47  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.47  tff(c_139, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.01/1.47  tff(c_152, plain, (![A_68]: (k3_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_139])).
% 3.01/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.01/1.47  tff(c_157, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_2])).
% 3.01/1.47  tff(c_351, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.47  tff(c_366, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=k4_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_351])).
% 3.01/1.47  tff(c_380, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_366])).
% 3.01/1.47  tff(c_208, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.47  tff(c_220, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_208])).
% 3.01/1.47  tff(c_438, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k4_xboole_0(B_95, A_94))=k2_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.47  tff(c_453, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_220, c_438])).
% 3.01/1.47  tff(c_462, plain, (![A_96]: (k2_xboole_0(A_96, k1_xboole_0)=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_380, c_453])).
% 3.01/1.47  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.01/1.47  tff(c_219, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_208])).
% 3.01/1.47  tff(c_489, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_462, c_219])).
% 3.01/1.47  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.47  tff(c_494, plain, (![A_98]: (k5_xboole_0(A_98, k1_xboole_0)=k2_xboole_0(A_98, A_98))), inference(superposition, [status(thm), theory('equality')], [c_489, c_22])).
% 3.01/1.47  tff(c_512, plain, (![A_98]: (k2_xboole_0(A_98, A_98)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_380, c_494])).
% 3.01/1.47  tff(c_24, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.01/1.47  tff(c_44, plain, (![A_51, B_52]: (k5_xboole_0(k1_tarski(A_51), k1_tarski(B_52))=k2_tarski(A_51, B_52) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.01/1.47  tff(c_40, plain, (![A_47, B_48]: (r1_xboole_0(k1_tarski(A_47), k1_tarski(B_48)) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.01/1.47  tff(c_324, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=A_81 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.01/1.47  tff(c_815, plain, (![A_118, B_119]: (k4_xboole_0(k1_tarski(A_118), k1_tarski(B_119))=k1_tarski(A_118) | B_119=A_118)), inference(resolution, [status(thm)], [c_40, c_324])).
% 3.01/1.47  tff(c_956, plain, (![B_139, A_140]: (k5_xboole_0(k1_tarski(B_139), k1_tarski(A_140))=k2_xboole_0(k1_tarski(B_139), k1_tarski(A_140)) | B_139=A_140)), inference(superposition, [status(thm), theory('equality')], [c_815, c_22])).
% 3.01/1.47  tff(c_1111, plain, (![A_154, B_155]: (k2_xboole_0(k1_tarski(A_154), k1_tarski(B_155))=k2_tarski(A_154, B_155) | B_155=A_154 | B_155=A_154)), inference(superposition, [status(thm), theory('equality')], [c_44, c_956])).
% 3.01/1.47  tff(c_38, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.01/1.47  tff(c_46, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.01/1.47  tff(c_47, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 3.01/1.47  tff(c_1151, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1111, c_47])).
% 3.01/1.47  tff(c_1155, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_1151, c_47])).
% 3.01/1.47  tff(c_1158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_512, c_24, c_1155])).
% 3.01/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  Inference rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Ref     : 0
% 3.01/1.47  #Sup     : 255
% 3.01/1.47  #Fact    : 0
% 3.01/1.47  #Define  : 0
% 3.01/1.47  #Split   : 0
% 3.01/1.47  #Chain   : 0
% 3.01/1.47  #Close   : 0
% 3.01/1.47  
% 3.01/1.47  Ordering : KBO
% 3.01/1.47  
% 3.01/1.47  Simplification rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Subsume      : 7
% 3.01/1.47  #Demod        : 134
% 3.01/1.47  #Tautology    : 209
% 3.01/1.47  #SimpNegUnit  : 0
% 3.01/1.47  #BackRed      : 5
% 3.01/1.47  
% 3.01/1.47  #Partial instantiations: 0
% 3.01/1.47  #Strategies tried      : 1
% 3.01/1.47  
% 3.01/1.47  Timing (in seconds)
% 3.01/1.47  ----------------------
% 3.01/1.48  Preprocessing        : 0.33
% 3.01/1.48  Parsing              : 0.18
% 3.01/1.48  CNF conversion       : 0.02
% 3.01/1.48  Main loop            : 0.35
% 3.01/1.48  Inferencing          : 0.14
% 3.01/1.48  Reduction            : 0.12
% 3.01/1.48  Demodulation         : 0.09
% 3.01/1.48  BG Simplification    : 0.02
% 3.01/1.48  Subsumption          : 0.05
% 3.01/1.48  Abstraction          : 0.02
% 3.01/1.48  MUC search           : 0.00
% 3.01/1.48  Cooper               : 0.00
% 3.01/1.48  Total                : 0.71
% 3.01/1.48  Index Insertion      : 0.00
% 3.01/1.48  Index Deletion       : 0.00
% 3.01/1.48  Index Matching       : 0.00
% 3.01/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
