%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:59 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 363 expanded)
%              Number of leaves         :   30 ( 134 expanded)
%              Depth                    :   21
%              Number of atoms          :   54 ( 384 expanded)
%              Number of equality atoms :   46 ( 306 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_36,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [B_56,A_57] : k3_xboole_0(B_56,A_57) = k3_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ r1_tarski(A_53,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [B_8] : k3_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_120,plain,(
    ! [B_56] : k3_xboole_0(B_56,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_75])).

tff(c_288,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_297,plain,(
    ! [B_56] : k5_xboole_0(B_56,k1_xboole_0) = k4_xboole_0(B_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_288])).

tff(c_339,plain,(
    ! [B_73] : k4_xboole_0(B_73,k1_xboole_0) = B_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_297])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    ! [B_73] : k4_xboole_0(B_73,B_73) = k3_xboole_0(B_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_12])).

tff(c_362,plain,(
    ! [B_73] : k4_xboole_0(B_73,B_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_349])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_309,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_288])).

tff(c_435,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_309])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_352,plain,(
    ! [B_73] : k5_xboole_0(k1_xboole_0,B_73) = k2_xboole_0(k1_xboole_0,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_18])).

tff(c_453,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_484,plain,(
    ! [A_3,C_83] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_453])).

tff(c_855,plain,(
    ! [A_102,C_103] : k5_xboole_0(A_102,k5_xboole_0(A_102,C_103)) = k2_xboole_0(k1_xboole_0,C_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_484])).

tff(c_922,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_855])).

tff(c_947,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_922])).

tff(c_854,plain,(
    ! [A_3,C_83] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_83)) = k2_xboole_0(k1_xboole_0,C_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_484])).

tff(c_1067,plain,(
    ! [A_106,C_107] : k5_xboole_0(A_106,k5_xboole_0(A_106,C_107)) = C_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_854])).

tff(c_1786,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k2_xboole_0(A_135,B_136)) = k4_xboole_0(B_136,A_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1067])).

tff(c_1835,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1786])).

tff(c_1844,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_1835])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_300,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_288])).

tff(c_1118,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_1067])).

tff(c_1848,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1844,c_1118])).

tff(c_1860,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1848])).

tff(c_1880,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_8])).

tff(c_34,plain,(
    ! [B_47,A_46] :
      ( B_47 = A_46
      | ~ r1_tarski(k1_tarski(A_46),k1_tarski(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1888,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1880,c_34])).

tff(c_1892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:23:20 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.26/1.48  
% 3.26/1.48  %Foreground sorts:
% 3.26/1.48  
% 3.26/1.48  
% 3.26/1.48  %Background operators:
% 3.26/1.48  
% 3.26/1.48  
% 3.26/1.48  %Foreground operators:
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.48  
% 3.26/1.49  tff(f_68, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.26/1.49  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.26/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.26/1.49  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.26/1.49  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.26/1.49  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.26/1.49  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.49  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.26/1.49  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.26/1.49  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.26/1.49  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.26/1.49  tff(c_36, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.49  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.49  tff(c_104, plain, (![B_56, A_57]: (k3_xboole_0(B_56, A_57)=k3_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.49  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.49  tff(c_70, plain, (![A_53]: (k1_xboole_0=A_53 | ~r1_tarski(A_53, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.49  tff(c_75, plain, (![B_8]: (k3_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_70])).
% 3.26/1.49  tff(c_120, plain, (![B_56]: (k3_xboole_0(B_56, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_75])).
% 3.26/1.49  tff(c_288, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.49  tff(c_297, plain, (![B_56]: (k5_xboole_0(B_56, k1_xboole_0)=k4_xboole_0(B_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_288])).
% 3.26/1.49  tff(c_339, plain, (![B_73]: (k4_xboole_0(B_73, k1_xboole_0)=B_73)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_297])).
% 3.26/1.49  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.49  tff(c_349, plain, (![B_73]: (k4_xboole_0(B_73, B_73)=k3_xboole_0(B_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_339, c_12])).
% 3.26/1.49  tff(c_362, plain, (![B_73]: (k4_xboole_0(B_73, B_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_349])).
% 3.26/1.49  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.49  tff(c_309, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_288])).
% 3.26/1.49  tff(c_435, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_362, c_309])).
% 3.26/1.49  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.49  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.49  tff(c_352, plain, (![B_73]: (k5_xboole_0(k1_xboole_0, B_73)=k2_xboole_0(k1_xboole_0, B_73))), inference(superposition, [status(thm), theory('equality')], [c_339, c_18])).
% 3.26/1.49  tff(c_453, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.49  tff(c_484, plain, (![A_3, C_83]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_435, c_453])).
% 3.26/1.49  tff(c_855, plain, (![A_102, C_103]: (k5_xboole_0(A_102, k5_xboole_0(A_102, C_103))=k2_xboole_0(k1_xboole_0, C_103))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_484])).
% 3.26/1.49  tff(c_922, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_435, c_855])).
% 3.26/1.49  tff(c_947, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_922])).
% 3.26/1.49  tff(c_854, plain, (![A_3, C_83]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_83))=k2_xboole_0(k1_xboole_0, C_83))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_484])).
% 3.26/1.49  tff(c_1067, plain, (![A_106, C_107]: (k5_xboole_0(A_106, k5_xboole_0(A_106, C_107))=C_107)), inference(demodulation, [status(thm), theory('equality')], [c_947, c_854])).
% 3.26/1.49  tff(c_1786, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k2_xboole_0(A_135, B_136))=k4_xboole_0(B_136, A_135))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1067])).
% 3.26/1.49  tff(c_1835, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1786])).
% 3.26/1.49  tff(c_1844, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_435, c_1835])).
% 3.26/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.49  tff(c_300, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_288])).
% 3.26/1.49  tff(c_1118, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_300, c_1067])).
% 3.26/1.49  tff(c_1848, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1844, c_1118])).
% 3.26/1.49  tff(c_1860, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1848])).
% 3.26/1.49  tff(c_1880, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1860, c_8])).
% 3.26/1.49  tff(c_34, plain, (![B_47, A_46]: (B_47=A_46 | ~r1_tarski(k1_tarski(A_46), k1_tarski(B_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.49  tff(c_1888, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1880, c_34])).
% 3.26/1.49  tff(c_1892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1888])).
% 3.26/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.49  
% 3.26/1.49  Inference rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Ref     : 0
% 3.26/1.49  #Sup     : 441
% 3.26/1.49  #Fact    : 0
% 3.26/1.49  #Define  : 0
% 3.26/1.49  #Split   : 0
% 3.26/1.49  #Chain   : 0
% 3.26/1.49  #Close   : 0
% 3.26/1.49  
% 3.26/1.49  Ordering : KBO
% 3.26/1.49  
% 3.26/1.49  Simplification rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Subsume      : 5
% 3.26/1.49  #Demod        : 336
% 3.26/1.49  #Tautology    : 324
% 3.26/1.49  #SimpNegUnit  : 1
% 3.26/1.49  #BackRed      : 4
% 3.26/1.49  
% 3.26/1.49  #Partial instantiations: 0
% 3.26/1.49  #Strategies tried      : 1
% 3.26/1.49  
% 3.26/1.49  Timing (in seconds)
% 3.26/1.49  ----------------------
% 3.26/1.50  Preprocessing        : 0.31
% 3.26/1.50  Parsing              : 0.17
% 3.26/1.50  CNF conversion       : 0.02
% 3.26/1.50  Main loop            : 0.43
% 3.26/1.50  Inferencing          : 0.16
% 3.26/1.50  Reduction            : 0.17
% 3.26/1.50  Demodulation         : 0.14
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.06
% 3.26/1.50  Abstraction          : 0.02
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.77
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
