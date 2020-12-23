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
% DateTime   : Thu Dec  3 09:51:34 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 119 expanded)
%              Number of leaves         :   37 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 124 expanded)
%              Number of equality atoms :   36 (  67 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_50,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_115,plain,(
    ! [D_65,B_66] : r2_hidden(D_65,k2_tarski(D_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_118,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_115])).

tff(c_129,plain,(
    ! [B_70,A_71] : k5_xboole_0(B_70,A_71) = k5_xboole_0(A_71,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_71] : k5_xboole_0(k1_xboole_0,A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_20])).

tff(c_18,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_264,plain,(
    ! [A_78,B_79] : r1_tarski(k4_xboole_0(A_78,B_79),k5_xboole_0(A_78,B_79)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_276,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_264])).

tff(c_284,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_276])).

tff(c_24,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_282,plain,(
    ! [A_15] : r1_tarski(k4_xboole_0(A_15,A_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_264])).

tff(c_332,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_336,plain,(
    ! [A_15] :
      ( k4_xboole_0(A_15,A_15) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(A_15,A_15)) ) ),
    inference(resolution,[status(thm)],[c_282,c_332])).

tff(c_346,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_336])).

tff(c_603,plain,(
    ! [A_101,B_102] :
      ( ~ r2_hidden(A_101,B_102)
      | k4_xboole_0(k1_tarski(A_101),B_102) != k1_tarski(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_614,plain,(
    ! [A_101] :
      ( ~ r2_hidden(A_101,k1_tarski(A_101))
      | k1_tarski(A_101) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_603])).

tff(c_617,plain,(
    ! [A_101] : k1_tarski(A_101) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_614])).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),k5_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1205,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_tarski(A_132,k2_xboole_0(B_133,C_134))
      | ~ r1_tarski(A_132,k5_xboole_0(B_133,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1574,plain,(
    ! [A_147,B_148] : r1_tarski(k4_xboole_0(A_147,B_148),k2_xboole_0(A_147,B_148)) ),
    inference(resolution,[status(thm)],[c_28,c_1205])).

tff(c_1597,plain,(
    r1_tarski(k4_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1574])).

tff(c_347,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_284,c_332])).

tff(c_1619,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1597,c_347])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_933,plain,(
    ! [A_125,B_126] : k5_xboole_0(k5_xboole_0(A_125,B_126),k2_xboole_0(A_125,B_126)) = k3_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1012,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_933])).

tff(c_1024,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_1012])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1694,plain,(
    ! [B_154,C_155] : r1_tarski(k5_xboole_0(B_154,C_155),k2_xboole_0(B_154,C_155)) ),
    inference(resolution,[status(thm)],[c_8,c_1205])).

tff(c_1750,plain,(
    r1_tarski(k5_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1694])).

tff(c_1764,plain,(
    r1_tarski(k3_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_2,c_1750])).

tff(c_1775,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1764,c_347])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1790,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1775,c_10])).

tff(c_1794,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1619,c_20,c_1790])).

tff(c_1796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_617,c_1794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.52  
% 3.26/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.26/1.52  
% 3.26/1.52  %Foreground sorts:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Background operators:
% 3.26/1.52  
% 3.26/1.52  
% 3.26/1.52  %Foreground operators:
% 3.26/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.26/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.26/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.52  
% 3.26/1.53  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.53  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.26/1.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.26/1.53  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.26/1.53  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.26/1.53  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 3.26/1.53  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.26/1.53  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.53  tff(f_83, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.26/1.53  tff(f_89, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.26/1.53  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 3.26/1.53  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.26/1.53  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.26/1.53  tff(c_50, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.53  tff(c_115, plain, (![D_65, B_66]: (r2_hidden(D_65, k2_tarski(D_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.26/1.53  tff(c_118, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_115])).
% 3.26/1.53  tff(c_129, plain, (![B_70, A_71]: (k5_xboole_0(B_70, A_71)=k5_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.53  tff(c_20, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.53  tff(c_145, plain, (![A_71]: (k5_xboole_0(k1_xboole_0, A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_129, c_20])).
% 3.26/1.53  tff(c_18, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.53  tff(c_264, plain, (![A_78, B_79]: (r1_tarski(k4_xboole_0(A_78, B_79), k5_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.53  tff(c_276, plain, (![A_10]: (r1_tarski(k1_xboole_0, k5_xboole_0(k1_xboole_0, A_10)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_264])).
% 3.26/1.53  tff(c_284, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_276])).
% 3.26/1.53  tff(c_24, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.53  tff(c_282, plain, (![A_15]: (r1_tarski(k4_xboole_0(A_15, A_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_264])).
% 3.26/1.53  tff(c_332, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.53  tff(c_336, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k4_xboole_0(A_15, A_15)))), inference(resolution, [status(thm)], [c_282, c_332])).
% 3.26/1.53  tff(c_346, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_336])).
% 3.26/1.53  tff(c_603, plain, (![A_101, B_102]: (~r2_hidden(A_101, B_102) | k4_xboole_0(k1_tarski(A_101), B_102)!=k1_tarski(A_101))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.26/1.53  tff(c_614, plain, (![A_101]: (~r2_hidden(A_101, k1_tarski(A_101)) | k1_tarski(A_101)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_346, c_603])).
% 3.26/1.53  tff(c_617, plain, (![A_101]: (k1_tarski(A_101)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_614])).
% 3.26/1.53  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.26/1.53  tff(c_28, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), k5_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.53  tff(c_1205, plain, (![A_132, B_133, C_134]: (r1_tarski(A_132, k2_xboole_0(B_133, C_134)) | ~r1_tarski(A_132, k5_xboole_0(B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.53  tff(c_1574, plain, (![A_147, B_148]: (r1_tarski(k4_xboole_0(A_147, B_148), k2_xboole_0(A_147, B_148)))), inference(resolution, [status(thm)], [c_28, c_1205])).
% 3.26/1.53  tff(c_1597, plain, (r1_tarski(k4_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_1574])).
% 3.26/1.53  tff(c_347, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_284, c_332])).
% 3.26/1.53  tff(c_1619, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1597, c_347])).
% 3.26/1.53  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.53  tff(c_933, plain, (![A_125, B_126]: (k5_xboole_0(k5_xboole_0(A_125, B_126), k2_xboole_0(A_125, B_126))=k3_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.26/1.53  tff(c_1012, plain, (k5_xboole_0(k5_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70, c_933])).
% 3.26/1.53  tff(c_1024, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_1012])).
% 3.26/1.53  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.53  tff(c_1694, plain, (![B_154, C_155]: (r1_tarski(k5_xboole_0(B_154, C_155), k2_xboole_0(B_154, C_155)))), inference(resolution, [status(thm)], [c_8, c_1205])).
% 3.26/1.53  tff(c_1750, plain, (r1_tarski(k5_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_1694])).
% 3.26/1.53  tff(c_1764, plain, (r1_tarski(k3_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_2, c_1750])).
% 3.26/1.53  tff(c_1775, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1764, c_347])).
% 3.26/1.53  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.53  tff(c_1790, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1775, c_10])).
% 3.26/1.53  tff(c_1794, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1619, c_20, c_1790])).
% 3.26/1.53  tff(c_1796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_617, c_1794])).
% 3.26/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.53  
% 3.26/1.53  Inference rules
% 3.26/1.53  ----------------------
% 3.26/1.53  #Ref     : 0
% 3.26/1.53  #Sup     : 431
% 3.26/1.53  #Fact    : 0
% 3.26/1.53  #Define  : 0
% 3.26/1.53  #Split   : 0
% 3.26/1.53  #Chain   : 0
% 3.26/1.53  #Close   : 0
% 3.26/1.53  
% 3.26/1.53  Ordering : KBO
% 3.26/1.53  
% 3.49/1.53  Simplification rules
% 3.49/1.53  ----------------------
% 3.49/1.53  #Subsume      : 5
% 3.49/1.53  #Demod        : 224
% 3.49/1.53  #Tautology    : 261
% 3.49/1.53  #SimpNegUnit  : 3
% 3.49/1.53  #BackRed      : 9
% 3.49/1.53  
% 3.49/1.53  #Partial instantiations: 0
% 3.49/1.53  #Strategies tried      : 1
% 3.49/1.53  
% 3.49/1.53  Timing (in seconds)
% 3.49/1.53  ----------------------
% 3.49/1.53  Preprocessing        : 0.33
% 3.49/1.53  Parsing              : 0.17
% 3.49/1.53  CNF conversion       : 0.02
% 3.49/1.53  Main loop            : 0.44
% 3.49/1.53  Inferencing          : 0.14
% 3.49/1.53  Reduction            : 0.18
% 3.49/1.53  Demodulation         : 0.14
% 3.49/1.53  BG Simplification    : 0.03
% 3.49/1.53  Subsumption          : 0.07
% 3.49/1.53  Abstraction          : 0.02
% 3.49/1.54  MUC search           : 0.00
% 3.49/1.54  Cooper               : 0.00
% 3.49/1.54  Total                : 0.80
% 3.49/1.54  Index Insertion      : 0.00
% 3.49/1.54  Index Deletion       : 0.00
% 3.49/1.54  Index Matching       : 0.00
% 3.49/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
