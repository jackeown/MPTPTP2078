%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:53 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 111 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  99 expanded)
%              Number of equality atoms :   41 (  86 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [B_58,A_59] : k5_xboole_0(B_58,A_59) = k5_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [A_59] : k5_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_8])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_367,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_420,plain,(
    ! [A_11,C_77] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_77)) = k5_xboole_0(k1_xboole_0,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_367])).

tff(c_436,plain,(
    ! [A_78,C_79] : k5_xboole_0(A_78,k5_xboole_0(A_78,C_79)) = C_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_420])).

tff(c_586,plain,(
    ! [B_82,A_83] : k5_xboole_0(B_82,k5_xboole_0(A_83,B_82)) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_436])).

tff(c_479,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_436])).

tff(c_589,plain,(
    ! [A_83,B_82] : k5_xboole_0(k5_xboole_0(A_83,B_82),A_83) = B_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_479])).

tff(c_16,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_290,plain,(
    ! [B_71,A_72] : k3_tarski(k2_tarski(B_71,A_72)) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_253])).

tff(c_32,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_317,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_32])).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_236,plain,(
    ! [A_63,B_64] :
      ( k2_xboole_0(A_63,B_64) = B_64
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_243,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_236])).

tff(c_332,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_243])).

tff(c_498,plain,(
    ! [A_80,B_81] : k5_xboole_0(k5_xboole_0(A_80,B_81),k2_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_538,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_498])).

tff(c_1479,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_538])).

tff(c_433,plain,(
    ! [A_11,C_77] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_420])).

tff(c_625,plain,(
    ! [A_11,C_77] : k5_xboole_0(k5_xboole_0(A_11,C_77),C_77) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_586])).

tff(c_42,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_244,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_236])).

tff(c_550,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_498])).

tff(c_898,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_550])).

tff(c_34,plain,(
    ! [A_46,C_48,B_47,D_49] : k3_xboole_0(k2_zfmisc_1(A_46,C_48),k2_zfmisc_1(B_47,D_49)) = k2_zfmisc_1(k3_xboole_0(A_46,B_47),k3_xboole_0(C_48,D_49)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_899,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_43])).

tff(c_1482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.53  
% 3.30/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.53  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.30/1.53  
% 3.30/1.53  %Foreground sorts:
% 3.30/1.53  
% 3.30/1.53  
% 3.30/1.53  %Background operators:
% 3.30/1.53  
% 3.30/1.53  
% 3.30/1.53  %Foreground operators:
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.30/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.30/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.30/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.30/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.30/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.30/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.53  
% 3.44/1.55  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.44/1.55  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.44/1.55  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.44/1.55  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.44/1.55  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.44/1.55  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.44/1.55  tff(f_70, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 3.44/1.55  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.44/1.55  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.44/1.55  tff(f_61, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.44/1.55  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.55  tff(c_130, plain, (![B_58, A_59]: (k5_xboole_0(B_58, A_59)=k5_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.55  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.55  tff(c_146, plain, (![A_59]: (k5_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_130, c_8])).
% 3.44/1.55  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.55  tff(c_367, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.55  tff(c_420, plain, (![A_11, C_77]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_77))=k5_xboole_0(k1_xboole_0, C_77))), inference(superposition, [status(thm), theory('equality')], [c_12, c_367])).
% 3.44/1.55  tff(c_436, plain, (![A_78, C_79]: (k5_xboole_0(A_78, k5_xboole_0(A_78, C_79))=C_79)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_420])).
% 3.44/1.55  tff(c_586, plain, (![B_82, A_83]: (k5_xboole_0(B_82, k5_xboole_0(A_83, B_82))=A_83)), inference(superposition, [status(thm), theory('equality')], [c_2, c_436])).
% 3.44/1.55  tff(c_479, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_436])).
% 3.44/1.55  tff(c_589, plain, (![A_83, B_82]: (k5_xboole_0(k5_xboole_0(A_83, B_82), A_83)=B_82)), inference(superposition, [status(thm), theory('equality')], [c_586, c_479])).
% 3.44/1.55  tff(c_16, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.55  tff(c_253, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.44/1.55  tff(c_290, plain, (![B_71, A_72]: (k3_tarski(k2_tarski(B_71, A_72))=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_16, c_253])).
% 3.44/1.55  tff(c_32, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.44/1.55  tff(c_317, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_290, c_32])).
% 3.44/1.55  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.44/1.55  tff(c_236, plain, (![A_63, B_64]: (k2_xboole_0(A_63, B_64)=B_64 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.55  tff(c_243, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_236])).
% 3.44/1.55  tff(c_332, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_317, c_243])).
% 3.44/1.55  tff(c_498, plain, (![A_80, B_81]: (k5_xboole_0(k5_xboole_0(A_80, B_81), k2_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.55  tff(c_538, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_332, c_498])).
% 3.44/1.55  tff(c_1479, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_589, c_538])).
% 3.44/1.55  tff(c_433, plain, (![A_11, C_77]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_420])).
% 3.44/1.55  tff(c_625, plain, (![A_11, C_77]: (k5_xboole_0(k5_xboole_0(A_11, C_77), C_77)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_433, c_586])).
% 3.44/1.55  tff(c_42, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.44/1.55  tff(c_244, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_42, c_236])).
% 3.44/1.55  tff(c_550, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_244, c_498])).
% 3.44/1.55  tff(c_898, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_625, c_550])).
% 3.44/1.55  tff(c_34, plain, (![A_46, C_48, B_47, D_49]: (k3_xboole_0(k2_zfmisc_1(A_46, C_48), k2_zfmisc_1(B_47, D_49))=k2_zfmisc_1(k3_xboole_0(A_46, B_47), k3_xboole_0(C_48, D_49)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.44/1.55  tff(c_38, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.44/1.55  tff(c_43, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 3.44/1.55  tff(c_899, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_898, c_43])).
% 3.44/1.55  tff(c_1482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1479, c_899])).
% 3.44/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.55  
% 3.44/1.55  Inference rules
% 3.44/1.55  ----------------------
% 3.44/1.55  #Ref     : 0
% 3.44/1.55  #Sup     : 358
% 3.44/1.55  #Fact    : 0
% 3.44/1.55  #Define  : 0
% 3.44/1.55  #Split   : 0
% 3.44/1.55  #Chain   : 0
% 3.44/1.55  #Close   : 0
% 3.44/1.55  
% 3.44/1.55  Ordering : KBO
% 3.44/1.55  
% 3.44/1.55  Simplification rules
% 3.44/1.55  ----------------------
% 3.44/1.55  #Subsume      : 8
% 3.44/1.55  #Demod        : 190
% 3.44/1.55  #Tautology    : 229
% 3.44/1.55  #SimpNegUnit  : 0
% 3.44/1.55  #BackRed      : 2
% 3.44/1.55  
% 3.44/1.55  #Partial instantiations: 0
% 3.44/1.55  #Strategies tried      : 1
% 3.44/1.55  
% 3.44/1.55  Timing (in seconds)
% 3.44/1.55  ----------------------
% 3.44/1.55  Preprocessing        : 0.33
% 3.44/1.55  Parsing              : 0.18
% 3.44/1.55  CNF conversion       : 0.02
% 3.44/1.55  Main loop            : 0.45
% 3.44/1.55  Inferencing          : 0.15
% 3.44/1.55  Reduction            : 0.19
% 3.44/1.55  Demodulation         : 0.16
% 3.44/1.55  BG Simplification    : 0.03
% 3.44/1.55  Subsumption          : 0.06
% 3.44/1.55  Abstraction          : 0.03
% 3.44/1.55  MUC search           : 0.00
% 3.44/1.55  Cooper               : 0.00
% 3.44/1.55  Total                : 0.82
% 3.44/1.55  Index Insertion      : 0.00
% 3.44/1.55  Index Deletion       : 0.00
% 3.44/1.55  Index Matching       : 0.00
% 3.44/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
