%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:51 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 539 expanded)
%              Number of leaves         :   34 ( 196 expanded)
%              Depth                    :   16
%              Number of atoms          :   54 ( 587 expanded)
%              Number of equality atoms :   48 ( 431 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_73,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_46,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_312,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_315,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_166,c_312])).

tff(c_323,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_315])).

tff(c_379,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_388,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_379])).

tff(c_394,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_388])).

tff(c_325,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(resolution,[status(thm)],[c_18,c_312])).

tff(c_398,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_325])).

tff(c_411,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_12])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_427,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_1') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_16])).

tff(c_216,plain,(
    ! [B_67,A_68] : k5_xboole_0(B_67,A_68) = k5_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_232,plain,(
    ! [A_68] : k5_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_16])).

tff(c_423,plain,(
    ! [A_68] : k5_xboole_0('#skF_1',A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_232])).

tff(c_116,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_65] : k3_xboole_0(k1_xboole_0,A_65) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_12])).

tff(c_424,plain,(
    ! [A_65] : k3_xboole_0('#skF_1',A_65) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_411,c_132])).

tff(c_732,plain,(
    ! [A_92,B_93] : k5_xboole_0(k5_xboole_0(A_92,B_93),k3_xboole_0(A_92,B_93)) = k2_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_762,plain,(
    ! [A_65] : k5_xboole_0(k5_xboole_0('#skF_1',A_65),'#skF_1') = k2_xboole_0('#skF_1',A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_732])).

tff(c_921,plain,(
    ! [A_99] : k2_xboole_0('#skF_1',A_99) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_423,c_762])).

tff(c_419,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_394])).

tff(c_931,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_419])).

tff(c_422,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_323])).

tff(c_959,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_422])).

tff(c_26,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_989,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_26])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_649,plain,(
    ! [A_87] : k5_xboole_0('#skF_1',A_87) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_232])).

tff(c_685,plain,(
    ! [B_8] : k4_xboole_0('#skF_1',B_8) = k3_xboole_0('#skF_1',B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_649])).

tff(c_703,plain,(
    ! [B_8] : k4_xboole_0('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_685])).

tff(c_42,plain,(
    ! [B_54] : k4_xboole_0(k1_tarski(B_54),k1_tarski(B_54)) != k1_tarski(B_54) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1012,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_42])).

tff(c_1021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_703,c_1012])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.43  
% 2.78/1.43  %Foreground sorts:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Background operators:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Foreground operators:
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.43  
% 2.78/1.45  tff(f_73, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.78/1.45  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.78/1.45  tff(f_77, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.78/1.45  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.78/1.45  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.78/1.45  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.78/1.45  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.78/1.45  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.78/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.78/1.45  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.78/1.45  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.78/1.45  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.45  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.78/1.45  tff(c_46, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.45  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.45  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.78/1.45  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.45  tff(c_166, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_18])).
% 2.78/1.45  tff(c_312, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.45  tff(c_315, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_166, c_312])).
% 2.78/1.45  tff(c_323, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_315])).
% 2.78/1.45  tff(c_379, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.78/1.45  tff(c_388, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_323, c_379])).
% 2.78/1.45  tff(c_394, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_388])).
% 2.78/1.45  tff(c_325, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(resolution, [status(thm)], [c_18, c_312])).
% 2.78/1.45  tff(c_398, plain, (k3_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_394, c_325])).
% 2.78/1.45  tff(c_411, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_398, c_12])).
% 2.78/1.45  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.45  tff(c_427, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_1')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_16])).
% 2.78/1.45  tff(c_216, plain, (![B_67, A_68]: (k5_xboole_0(B_67, A_68)=k5_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.45  tff(c_232, plain, (![A_68]: (k5_xboole_0(k1_xboole_0, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_216, c_16])).
% 2.78/1.45  tff(c_423, plain, (![A_68]: (k5_xboole_0('#skF_1', A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_232])).
% 2.78/1.45  tff(c_116, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.45  tff(c_132, plain, (![A_65]: (k3_xboole_0(k1_xboole_0, A_65)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_12])).
% 2.78/1.45  tff(c_424, plain, (![A_65]: (k3_xboole_0('#skF_1', A_65)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_411, c_132])).
% 2.78/1.45  tff(c_732, plain, (![A_92, B_93]: (k5_xboole_0(k5_xboole_0(A_92, B_93), k3_xboole_0(A_92, B_93))=k2_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.45  tff(c_762, plain, (![A_65]: (k5_xboole_0(k5_xboole_0('#skF_1', A_65), '#skF_1')=k2_xboole_0('#skF_1', A_65))), inference(superposition, [status(thm), theory('equality')], [c_424, c_732])).
% 2.78/1.45  tff(c_921, plain, (![A_99]: (k2_xboole_0('#skF_1', A_99)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_427, c_423, c_762])).
% 2.78/1.45  tff(c_419, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_411, c_394])).
% 2.78/1.45  tff(c_931, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_921, c_419])).
% 2.78/1.45  tff(c_422, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_411, c_323])).
% 2.78/1.45  tff(c_959, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_931, c_422])).
% 2.78/1.45  tff(c_26, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.78/1.45  tff(c_989, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_959, c_26])).
% 2.78/1.45  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.45  tff(c_649, plain, (![A_87]: (k5_xboole_0('#skF_1', A_87)=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_232])).
% 2.78/1.45  tff(c_685, plain, (![B_8]: (k4_xboole_0('#skF_1', B_8)=k3_xboole_0('#skF_1', B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_649])).
% 2.78/1.45  tff(c_703, plain, (![B_8]: (k4_xboole_0('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_685])).
% 2.78/1.45  tff(c_42, plain, (![B_54]: (k4_xboole_0(k1_tarski(B_54), k1_tarski(B_54))!=k1_tarski(B_54))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.78/1.45  tff(c_1012, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_989, c_42])).
% 2.78/1.45  tff(c_1021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_989, c_703, c_1012])).
% 2.78/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  Inference rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Ref     : 0
% 2.78/1.45  #Sup     : 244
% 2.78/1.45  #Fact    : 0
% 2.78/1.45  #Define  : 0
% 2.78/1.45  #Split   : 0
% 2.78/1.45  #Chain   : 0
% 2.78/1.45  #Close   : 0
% 2.78/1.45  
% 2.78/1.45  Ordering : KBO
% 2.78/1.45  
% 2.78/1.45  Simplification rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Subsume      : 0
% 2.78/1.45  #Demod        : 115
% 2.78/1.45  #Tautology    : 187
% 2.78/1.45  #SimpNegUnit  : 0
% 2.78/1.45  #BackRed      : 17
% 2.78/1.45  
% 2.78/1.45  #Partial instantiations: 0
% 2.78/1.45  #Strategies tried      : 1
% 2.78/1.45  
% 2.78/1.45  Timing (in seconds)
% 2.78/1.45  ----------------------
% 2.93/1.45  Preprocessing        : 0.33
% 2.93/1.45  Parsing              : 0.18
% 2.93/1.45  CNF conversion       : 0.02
% 2.93/1.45  Main loop            : 0.30
% 2.93/1.45  Inferencing          : 0.10
% 2.93/1.45  Reduction            : 0.12
% 2.93/1.45  Demodulation         : 0.09
% 2.93/1.45  BG Simplification    : 0.02
% 2.93/1.45  Subsumption          : 0.04
% 2.93/1.45  Abstraction          : 0.02
% 2.93/1.45  MUC search           : 0.00
% 2.93/1.45  Cooper               : 0.00
% 2.93/1.45  Total                : 0.67
% 2.93/1.45  Index Insertion      : 0.00
% 2.93/1.45  Index Deletion       : 0.00
% 2.93/1.45  Index Matching       : 0.00
% 2.93/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
