%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:59 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 134 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :   46 ( 122 expanded)
%              Number of equality atoms :   40 ( 116 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_202,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_220,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_202])).

tff(c_224,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_220])).

tff(c_361,plain,(
    ! [A_62,B_63,C_64] : k5_xboole_0(k5_xboole_0(A_62,B_63),C_64) = k5_xboole_0(A_62,k5_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_750,plain,(
    ! [A_75,C_76] : k5_xboole_0(A_75,k5_xboole_0(A_75,C_76)) = k5_xboole_0(k1_xboole_0,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_361])).

tff(c_837,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_750])).

tff(c_869,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_837])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_871,plain,(
    ! [A_77,B_78,C_79] : k5_xboole_0(A_77,k5_xboole_0(k4_xboole_0(B_78,A_77),C_79)) = k5_xboole_0(k2_xboole_0(A_77,B_78),C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_361])).

tff(c_953,plain,(
    ! [A_77,B_78] : k5_xboole_0(k2_xboole_0(A_77,B_78),k4_xboole_0(B_78,A_77)) = k5_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_871])).

tff(c_2333,plain,(
    ! [A_106,B_107] : k5_xboole_0(k2_xboole_0(A_106,B_107),k4_xboole_0(B_107,A_106)) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_953])).

tff(c_2384,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1'))) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2333])).

tff(c_403,plain,(
    ! [A_7,C_64] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_64)) = k5_xboole_0(k1_xboole_0,C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_361])).

tff(c_987,plain,(
    ! [A_7,C_64] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_64)) = C_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_403])).

tff(c_2417,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2384,c_987])).

tff(c_2433,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_2417])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1356,plain,(
    ! [A_88,B_89,C_90] : k5_xboole_0(A_88,k5_xboole_0(k3_xboole_0(A_88,B_89),C_90)) = k5_xboole_0(k4_xboole_0(A_88,B_89),C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_361])).

tff(c_1427,plain,(
    ! [A_88,B_89] : k5_xboole_0(k4_xboole_0(A_88,B_89),k3_xboole_0(A_88,B_89)) = k5_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_1356])).

tff(c_1457,plain,(
    ! [A_88,B_89] : k5_xboole_0(k4_xboole_0(A_88,B_89),k3_xboole_0(A_88,B_89)) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1427])).

tff(c_2445,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1'))) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2433,c_1457])).

tff(c_2455,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_2,c_2445])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2478,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2455,c_6])).

tff(c_26,plain,(
    ! [B_28,A_27] :
      ( B_28 = A_27
      | ~ r1_tarski(k1_tarski(A_27),k1_tarski(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2486,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2478,c_26])).

tff(c_2490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:39:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.69  
% 3.64/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.69  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.90/1.69  
% 3.90/1.69  %Foreground sorts:
% 3.90/1.69  
% 3.90/1.69  
% 3.90/1.69  %Background operators:
% 3.90/1.69  
% 3.90/1.69  
% 3.90/1.69  %Foreground operators:
% 3.90/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.90/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.90/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.90/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.90/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.90/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.90/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.90/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.90/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.90/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.69  
% 3.90/1.70  tff(f_58, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.90/1.70  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.90/1.70  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.90/1.70  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.90/1.70  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.90/1.70  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.90/1.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.90/1.70  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.90/1.70  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.90/1.70  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.90/1.70  tff(c_28, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.90/1.70  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.90/1.70  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.70  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.70  tff(c_202, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.90/1.70  tff(c_220, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_202])).
% 3.90/1.70  tff(c_224, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_220])).
% 3.90/1.70  tff(c_361, plain, (![A_62, B_63, C_64]: (k5_xboole_0(k5_xboole_0(A_62, B_63), C_64)=k5_xboole_0(A_62, k5_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/1.70  tff(c_750, plain, (![A_75, C_76]: (k5_xboole_0(A_75, k5_xboole_0(A_75, C_76))=k5_xboole_0(k1_xboole_0, C_76))), inference(superposition, [status(thm), theory('equality')], [c_224, c_361])).
% 3.90/1.70  tff(c_837, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_750])).
% 3.90/1.70  tff(c_869, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_837])).
% 3.90/1.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.90/1.70  tff(c_30, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.90/1.70  tff(c_16, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.90/1.70  tff(c_871, plain, (![A_77, B_78, C_79]: (k5_xboole_0(A_77, k5_xboole_0(k4_xboole_0(B_78, A_77), C_79))=k5_xboole_0(k2_xboole_0(A_77, B_78), C_79))), inference(superposition, [status(thm), theory('equality')], [c_16, c_361])).
% 3.90/1.70  tff(c_953, plain, (![A_77, B_78]: (k5_xboole_0(k2_xboole_0(A_77, B_78), k4_xboole_0(B_78, A_77))=k5_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_871])).
% 3.90/1.70  tff(c_2333, plain, (![A_106, B_107]: (k5_xboole_0(k2_xboole_0(A_106, B_107), k4_xboole_0(B_107, A_106))=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_953])).
% 3.90/1.70  tff(c_2384, plain, (k5_xboole_0(k1_tarski('#skF_1'), k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1')))=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2333])).
% 3.90/1.70  tff(c_403, plain, (![A_7, C_64]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_64))=k5_xboole_0(k1_xboole_0, C_64))), inference(superposition, [status(thm), theory('equality')], [c_224, c_361])).
% 3.90/1.70  tff(c_987, plain, (![A_7, C_64]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_64))=C_64)), inference(demodulation, [status(thm), theory('equality')], [c_869, c_403])).
% 3.90/1.70  tff(c_2417, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2384, c_987])).
% 3.90/1.70  tff(c_2433, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_224, c_2417])).
% 3.90/1.70  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.90/1.70  tff(c_1356, plain, (![A_88, B_89, C_90]: (k5_xboole_0(A_88, k5_xboole_0(k3_xboole_0(A_88, B_89), C_90))=k5_xboole_0(k4_xboole_0(A_88, B_89), C_90))), inference(superposition, [status(thm), theory('equality')], [c_4, c_361])).
% 3.90/1.70  tff(c_1427, plain, (![A_88, B_89]: (k5_xboole_0(k4_xboole_0(A_88, B_89), k3_xboole_0(A_88, B_89))=k5_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_1356])).
% 3.90/1.70  tff(c_1457, plain, (![A_88, B_89]: (k5_xboole_0(k4_xboole_0(A_88, B_89), k3_xboole_0(A_88, B_89))=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1427])).
% 3.90/1.70  tff(c_2445, plain, (k5_xboole_0(k1_xboole_0, k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1')))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2433, c_1457])).
% 3.90/1.70  tff(c_2455, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_869, c_2, c_2445])).
% 3.90/1.70  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.70  tff(c_2478, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2455, c_6])).
% 3.90/1.70  tff(c_26, plain, (![B_28, A_27]: (B_28=A_27 | ~r1_tarski(k1_tarski(A_27), k1_tarski(B_28)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.70  tff(c_2486, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_2478, c_26])).
% 3.90/1.70  tff(c_2490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2486])).
% 3.90/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.70  
% 3.90/1.70  Inference rules
% 3.90/1.70  ----------------------
% 3.90/1.70  #Ref     : 0
% 3.90/1.70  #Sup     : 607
% 3.90/1.70  #Fact    : 0
% 3.90/1.70  #Define  : 0
% 3.90/1.70  #Split   : 0
% 3.90/1.70  #Chain   : 0
% 3.90/1.70  #Close   : 0
% 3.90/1.70  
% 3.90/1.70  Ordering : KBO
% 3.90/1.70  
% 3.90/1.70  Simplification rules
% 3.90/1.70  ----------------------
% 3.90/1.70  #Subsume      : 5
% 3.90/1.70  #Demod        : 520
% 3.90/1.70  #Tautology    : 368
% 3.90/1.70  #SimpNegUnit  : 1
% 3.90/1.70  #BackRed      : 5
% 3.90/1.70  
% 3.90/1.70  #Partial instantiations: 0
% 3.90/1.70  #Strategies tried      : 1
% 3.90/1.70  
% 3.90/1.70  Timing (in seconds)
% 3.90/1.70  ----------------------
% 3.90/1.70  Preprocessing        : 0.33
% 3.90/1.70  Parsing              : 0.17
% 3.90/1.71  CNF conversion       : 0.02
% 3.90/1.71  Main loop            : 0.57
% 3.90/1.71  Inferencing          : 0.20
% 3.90/1.71  Reduction            : 0.24
% 3.90/1.71  Demodulation         : 0.20
% 3.90/1.71  BG Simplification    : 0.03
% 3.90/1.71  Subsumption          : 0.07
% 3.90/1.71  Abstraction          : 0.03
% 3.90/1.71  MUC search           : 0.00
% 3.90/1.71  Cooper               : 0.00
% 3.90/1.71  Total                : 0.92
% 3.90/1.71  Index Insertion      : 0.00
% 3.90/1.71  Index Deletion       : 0.00
% 3.90/1.71  Index Matching       : 0.00
% 3.90/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
