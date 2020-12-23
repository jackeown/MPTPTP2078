%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:55 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 115 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 ( 103 expanded)
%              Number of equality atoms :   47 (  90 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_109,plain,(
    ! [B_59,A_60] : k5_xboole_0(B_59,A_60) = k5_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_534,plain,(
    ! [A_83,B_84,C_85] : k5_xboole_0(k5_xboole_0(A_83,B_84),C_85) = k5_xboole_0(A_83,k5_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_637,plain,(
    ! [A_18,C_85] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_85)) = k5_xboole_0(k1_xboole_0,C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_534])).

tff(c_684,plain,(
    ! [A_86,C_87] : k5_xboole_0(A_86,k5_xboole_0(A_86,C_87)) = C_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_637])).

tff(c_736,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_684])).

tff(c_790,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k5_xboole_0(B_93,A_92)) = B_93 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_684])).

tff(c_820,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),B_2) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_790])).

tff(c_12,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_654,plain,(
    ! [A_18,C_85] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_85)) = C_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_637])).

tff(c_42,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_224,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(A_66,B_67) = B_67
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_231,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_224])).

tff(c_329,plain,(
    ! [A_78,B_79] : k5_xboole_0(k5_xboole_0(A_78,B_79),k2_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_362,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_329])).

tff(c_392,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_362])).

tff(c_683,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_392])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_761,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_8])).

tff(c_764,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_761])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_769,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_14])).

tff(c_772,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_769])).

tff(c_22,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k2_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_777,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_22])).

tff(c_2185,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_777])).

tff(c_44,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_232,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_224])).

tff(c_359,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_329])).

tff(c_547,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_359])).

tff(c_644,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_547])).

tff(c_38,plain,(
    ! [A_50,C_52,B_51,D_53] : k3_xboole_0(k2_zfmisc_1(A_50,C_52),k2_zfmisc_1(B_51,D_53)) = k2_zfmisc_1(k3_xboole_0(A_50,B_51),k3_xboole_0(C_52,D_53)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_45,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_657,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_45])).

tff(c_2188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2185,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:17:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/2.21  
% 4.71/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/2.22  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.71/2.22  
% 4.71/2.22  %Foreground sorts:
% 4.71/2.22  
% 4.71/2.22  
% 4.71/2.22  %Background operators:
% 4.71/2.22  
% 4.71/2.22  
% 4.71/2.22  %Foreground operators:
% 4.71/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.71/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.71/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.71/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.71/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.71/2.22  tff('#skF_2', type, '#skF_2': $i).
% 4.71/2.22  tff('#skF_3', type, '#skF_3': $i).
% 4.71/2.22  tff('#skF_1', type, '#skF_1': $i).
% 4.71/2.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.71/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/2.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.71/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/2.22  tff('#skF_4', type, '#skF_4': $i).
% 4.71/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.71/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.71/2.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.71/2.22  
% 4.71/2.24  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.71/2.24  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.71/2.24  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.71/2.24  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.71/2.24  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.71/2.24  tff(f_72, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 4.71/2.24  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.71/2.24  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.71/2.24  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.71/2.24  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.71/2.24  tff(f_65, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 4.71/2.24  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.71/2.24  tff(c_109, plain, (![B_59, A_60]: (k5_xboole_0(B_59, A_60)=k5_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.71/2.24  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.71/2.24  tff(c_125, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_109, c_16])).
% 4.71/2.24  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.71/2.24  tff(c_534, plain, (![A_83, B_84, C_85]: (k5_xboole_0(k5_xboole_0(A_83, B_84), C_85)=k5_xboole_0(A_83, k5_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.71/2.24  tff(c_637, plain, (![A_18, C_85]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_85))=k5_xboole_0(k1_xboole_0, C_85))), inference(superposition, [status(thm), theory('equality')], [c_20, c_534])).
% 4.71/2.24  tff(c_684, plain, (![A_86, C_87]: (k5_xboole_0(A_86, k5_xboole_0(A_86, C_87))=C_87)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_637])).
% 4.71/2.24  tff(c_736, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_684])).
% 4.71/2.24  tff(c_790, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k5_xboole_0(B_93, A_92))=B_93)), inference(superposition, [status(thm), theory('equality')], [c_2, c_684])).
% 4.71/2.24  tff(c_820, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), B_2)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_736, c_790])).
% 4.71/2.24  tff(c_12, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.71/2.24  tff(c_654, plain, (![A_18, C_85]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_85))=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_637])).
% 4.71/2.24  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.71/2.24  tff(c_224, plain, (![A_66, B_67]: (k2_xboole_0(A_66, B_67)=B_67 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.71/2.24  tff(c_231, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_42, c_224])).
% 4.71/2.24  tff(c_329, plain, (![A_78, B_79]: (k5_xboole_0(k5_xboole_0(A_78, B_79), k2_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.71/2.24  tff(c_362, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_231, c_329])).
% 4.71/2.24  tff(c_392, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_362])).
% 4.71/2.24  tff(c_683, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_392])).
% 4.71/2.24  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.71/2.24  tff(c_761, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_683, c_8])).
% 4.71/2.24  tff(c_764, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_761])).
% 4.71/2.24  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.71/2.24  tff(c_769, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_764, c_14])).
% 4.71/2.24  tff(c_772, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_769])).
% 4.71/2.24  tff(c_22, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k2_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.71/2.24  tff(c_777, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_772, c_22])).
% 4.71/2.24  tff(c_2185, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_820, c_777])).
% 4.71/2.24  tff(c_44, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.71/2.24  tff(c_232, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_44, c_224])).
% 4.71/2.24  tff(c_359, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_232, c_329])).
% 4.71/2.24  tff(c_547, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_534, c_359])).
% 4.71/2.24  tff(c_644, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_547])).
% 4.71/2.24  tff(c_38, plain, (![A_50, C_52, B_51, D_53]: (k3_xboole_0(k2_zfmisc_1(A_50, C_52), k2_zfmisc_1(B_51, D_53))=k2_zfmisc_1(k3_xboole_0(A_50, B_51), k3_xboole_0(C_52, D_53)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.71/2.24  tff(c_40, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.71/2.24  tff(c_45, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 4.71/2.24  tff(c_657, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_45])).
% 4.71/2.24  tff(c_2188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2185, c_657])).
% 4.71/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/2.24  
% 4.71/2.24  Inference rules
% 4.71/2.24  ----------------------
% 4.71/2.24  #Ref     : 0
% 4.71/2.24  #Sup     : 532
% 4.71/2.24  #Fact    : 0
% 4.71/2.24  #Define  : 0
% 4.71/2.24  #Split   : 0
% 4.71/2.24  #Chain   : 0
% 4.71/2.24  #Close   : 0
% 4.71/2.24  
% 4.71/2.24  Ordering : KBO
% 4.71/2.24  
% 4.71/2.24  Simplification rules
% 4.71/2.24  ----------------------
% 4.71/2.24  #Subsume      : 4
% 4.71/2.24  #Demod        : 430
% 4.71/2.24  #Tautology    : 389
% 4.71/2.24  #SimpNegUnit  : 0
% 4.71/2.24  #BackRed      : 5
% 4.71/2.24  
% 4.71/2.24  #Partial instantiations: 0
% 4.71/2.24  #Strategies tried      : 1
% 4.71/2.24  
% 4.71/2.24  Timing (in seconds)
% 4.71/2.24  ----------------------
% 4.71/2.24  Preprocessing        : 0.51
% 4.71/2.24  Parsing              : 0.27
% 4.71/2.24  CNF conversion       : 0.03
% 4.71/2.24  Main loop            : 0.88
% 4.71/2.25  Inferencing          : 0.29
% 4.71/2.25  Reduction            : 0.37
% 4.71/2.25  Demodulation         : 0.31
% 4.71/2.25  BG Simplification    : 0.04
% 4.71/2.25  Subsumption          : 0.12
% 4.71/2.25  Abstraction          : 0.05
% 4.71/2.25  MUC search           : 0.00
% 4.71/2.25  Cooper               : 0.00
% 4.71/2.25  Total                : 1.44
% 4.71/2.25  Index Insertion      : 0.00
% 4.71/2.25  Index Deletion       : 0.00
% 4.71/2.25  Index Matching       : 0.00
% 4.71/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
