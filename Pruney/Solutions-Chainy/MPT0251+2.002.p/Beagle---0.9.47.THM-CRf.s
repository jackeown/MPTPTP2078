%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:46 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 137 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :   71 ( 138 expanded)
%              Number of equality atoms :   45 ( 103 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_97,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_107,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_99,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_157,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_398,plain,(
    ! [A_103,B_104] : k3_tarski(k2_tarski(A_103,B_104)) = k2_xboole_0(B_104,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_157])).

tff(c_52,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_442,plain,(
    ! [B_107,A_108] : k2_xboole_0(B_107,A_108) = k2_xboole_0(A_108,B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_52])).

tff(c_470,plain,(
    ! [A_108] : k2_xboole_0(k1_xboole_0,A_108) = A_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_32])).

tff(c_501,plain,(
    ! [A_109] : k2_xboole_0(k1_xboole_0,A_109) = A_109 ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_32])).

tff(c_36,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_514,plain,(
    ! [B_30] : k4_xboole_0(B_30,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_36])).

tff(c_547,plain,(
    ! [B_30] : k4_xboole_0(B_30,k1_xboole_0) = B_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_514])).

tff(c_40,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_148,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_155,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(resolution,[status(thm)],[c_40,c_148])).

tff(c_517,plain,(
    ! [A_109] : k3_xboole_0(k1_xboole_0,A_109) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_155])).

tff(c_821,plain,(
    ! [A_133,B_134] : k5_xboole_0(A_133,k3_xboole_0(A_133,B_134)) = k4_xboole_0(A_133,B_134) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_888,plain,(
    ! [A_141] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_821])).

tff(c_28,plain,(
    ! [B_23] : r1_tarski(B_23,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_156,plain,(
    ! [B_23] : k3_xboole_0(B_23,B_23) = B_23 ),
    inference(resolution,[status(thm)],[c_28,c_148])).

tff(c_842,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k4_xboole_0(B_23,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_821])).

tff(c_894,plain,(
    ! [A_141] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_842])).

tff(c_905,plain,(
    ! [A_141] : k4_xboole_0(k1_xboole_0,A_141) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_894])).

tff(c_909,plain,(
    ! [A_142,B_143] : k4_xboole_0(k2_xboole_0(A_142,B_143),B_143) = k4_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_929,plain,(
    ! [A_108] : k4_xboole_0(k1_xboole_0,A_108) = k4_xboole_0(A_108,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_909])).

tff(c_995,plain,(
    ! [A_108] : k4_xboole_0(A_108,A_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_929])).

tff(c_996,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_842])).

tff(c_44,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1398,plain,(
    ! [A_175,B_176,C_177] :
      ( r1_tarski(k2_tarski(A_175,B_176),C_177)
      | ~ r2_hidden(B_176,C_177)
      | ~ r2_hidden(A_175,C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3547,plain,(
    ! [A_338,C_339] :
      ( r1_tarski(k1_tarski(A_338),C_339)
      | ~ r2_hidden(A_338,C_339)
      | ~ r2_hidden(A_338,C_339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1398])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6121,plain,(
    ! [A_475,C_476] :
      ( k3_xboole_0(k1_tarski(A_475),C_476) = k1_tarski(A_475)
      | ~ r2_hidden(A_475,C_476) ) ),
    inference(resolution,[status(thm)],[c_3547,c_34])).

tff(c_30,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6158,plain,(
    ! [A_475,C_476] :
      ( k5_xboole_0(k1_tarski(A_475),k1_tarski(A_475)) = k4_xboole_0(k1_tarski(A_475),C_476)
      | ~ r2_hidden(A_475,C_476) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6121,c_30])).

tff(c_6971,plain,(
    ! [A_505,C_506] :
      ( k4_xboole_0(k1_tarski(A_505),C_506) = k1_xboole_0
      | ~ r2_hidden(A_505,C_506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_6158])).

tff(c_7014,plain,(
    ! [C_506,A_505] :
      ( k2_xboole_0(C_506,k1_tarski(A_505)) = k2_xboole_0(C_506,k1_xboole_0)
      | ~ r2_hidden(A_505,C_506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6971,c_36])).

tff(c_7190,plain,(
    ! [C_513,A_514] :
      ( k2_xboole_0(C_513,k1_tarski(A_514)) = C_513
      | ~ r2_hidden(A_514,C_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_7014])).

tff(c_404,plain,(
    ! [B_104,A_103] : k2_xboole_0(B_104,A_103) = k2_xboole_0(A_103,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_52])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_441,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_60])).

tff(c_7441,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7190,c_441])).

tff(c_7502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:21:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.39  
% 6.02/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 6.02/2.39  
% 6.02/2.39  %Foreground sorts:
% 6.02/2.39  
% 6.02/2.39  
% 6.02/2.39  %Background operators:
% 6.02/2.39  
% 6.02/2.39  
% 6.02/2.39  %Foreground operators:
% 6.02/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.02/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.02/2.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.02/2.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.02/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.02/2.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.02/2.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.02/2.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.02/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.02/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.02/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.02/2.39  tff('#skF_5', type, '#skF_5': $i).
% 6.02/2.39  tff('#skF_6', type, '#skF_6': $i).
% 6.02/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.02/2.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.02/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.02/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.02/2.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.02/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.02/2.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.02/2.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.02/2.39  
% 6.21/2.41  tff(f_118, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 6.21/2.41  tff(f_85, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.21/2.41  tff(f_97, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.21/2.41  tff(f_107, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.21/2.41  tff(f_91, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.21/2.41  tff(f_95, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.21/2.41  tff(f_89, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.21/2.41  tff(f_83, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.21/2.41  tff(f_81, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.21/2.41  tff(f_93, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.21/2.41  tff(f_99, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.21/2.41  tff(f_113, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.21/2.41  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.21/2.41  tff(c_32, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.21/2.41  tff(c_42, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.21/2.41  tff(c_157, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.21/2.41  tff(c_398, plain, (![A_103, B_104]: (k3_tarski(k2_tarski(A_103, B_104))=k2_xboole_0(B_104, A_103))), inference(superposition, [status(thm), theory('equality')], [c_42, c_157])).
% 6.21/2.41  tff(c_52, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.21/2.41  tff(c_442, plain, (![B_107, A_108]: (k2_xboole_0(B_107, A_108)=k2_xboole_0(A_108, B_107))), inference(superposition, [status(thm), theory('equality')], [c_398, c_52])).
% 6.21/2.41  tff(c_470, plain, (![A_108]: (k2_xboole_0(k1_xboole_0, A_108)=A_108)), inference(superposition, [status(thm), theory('equality')], [c_442, c_32])).
% 6.21/2.41  tff(c_501, plain, (![A_109]: (k2_xboole_0(k1_xboole_0, A_109)=A_109)), inference(superposition, [status(thm), theory('equality')], [c_442, c_32])).
% 6.21/2.41  tff(c_36, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.21/2.41  tff(c_514, plain, (![B_30]: (k4_xboole_0(B_30, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_30))), inference(superposition, [status(thm), theory('equality')], [c_501, c_36])).
% 6.21/2.41  tff(c_547, plain, (![B_30]: (k4_xboole_0(B_30, k1_xboole_0)=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_470, c_514])).
% 6.21/2.41  tff(c_40, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.21/2.41  tff(c_148, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.21/2.41  tff(c_155, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(resolution, [status(thm)], [c_40, c_148])).
% 6.21/2.41  tff(c_517, plain, (![A_109]: (k3_xboole_0(k1_xboole_0, A_109)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_501, c_155])).
% 6.21/2.41  tff(c_821, plain, (![A_133, B_134]: (k5_xboole_0(A_133, k3_xboole_0(A_133, B_134))=k4_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.41  tff(c_888, plain, (![A_141]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_141))), inference(superposition, [status(thm), theory('equality')], [c_517, c_821])).
% 6.21/2.41  tff(c_28, plain, (![B_23]: (r1_tarski(B_23, B_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.21/2.41  tff(c_156, plain, (![B_23]: (k3_xboole_0(B_23, B_23)=B_23)), inference(resolution, [status(thm)], [c_28, c_148])).
% 6.21/2.41  tff(c_842, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k4_xboole_0(B_23, B_23))), inference(superposition, [status(thm), theory('equality')], [c_156, c_821])).
% 6.21/2.41  tff(c_894, plain, (![A_141]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_141))), inference(superposition, [status(thm), theory('equality')], [c_888, c_842])).
% 6.21/2.41  tff(c_905, plain, (![A_141]: (k4_xboole_0(k1_xboole_0, A_141)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_547, c_894])).
% 6.21/2.41  tff(c_909, plain, (![A_142, B_143]: (k4_xboole_0(k2_xboole_0(A_142, B_143), B_143)=k4_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.21/2.41  tff(c_929, plain, (![A_108]: (k4_xboole_0(k1_xboole_0, A_108)=k4_xboole_0(A_108, A_108))), inference(superposition, [status(thm), theory('equality')], [c_470, c_909])).
% 6.21/2.41  tff(c_995, plain, (![A_108]: (k4_xboole_0(A_108, A_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_905, c_929])).
% 6.21/2.41  tff(c_996, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_995, c_842])).
% 6.21/2.41  tff(c_44, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.21/2.41  tff(c_1398, plain, (![A_175, B_176, C_177]: (r1_tarski(k2_tarski(A_175, B_176), C_177) | ~r2_hidden(B_176, C_177) | ~r2_hidden(A_175, C_177))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.21/2.41  tff(c_3547, plain, (![A_338, C_339]: (r1_tarski(k1_tarski(A_338), C_339) | ~r2_hidden(A_338, C_339) | ~r2_hidden(A_338, C_339))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1398])).
% 6.21/2.41  tff(c_34, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.21/2.41  tff(c_6121, plain, (![A_475, C_476]: (k3_xboole_0(k1_tarski(A_475), C_476)=k1_tarski(A_475) | ~r2_hidden(A_475, C_476))), inference(resolution, [status(thm)], [c_3547, c_34])).
% 6.21/2.41  tff(c_30, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.41  tff(c_6158, plain, (![A_475, C_476]: (k5_xboole_0(k1_tarski(A_475), k1_tarski(A_475))=k4_xboole_0(k1_tarski(A_475), C_476) | ~r2_hidden(A_475, C_476))), inference(superposition, [status(thm), theory('equality')], [c_6121, c_30])).
% 6.21/2.41  tff(c_6971, plain, (![A_505, C_506]: (k4_xboole_0(k1_tarski(A_505), C_506)=k1_xboole_0 | ~r2_hidden(A_505, C_506))), inference(demodulation, [status(thm), theory('equality')], [c_996, c_6158])).
% 6.21/2.41  tff(c_7014, plain, (![C_506, A_505]: (k2_xboole_0(C_506, k1_tarski(A_505))=k2_xboole_0(C_506, k1_xboole_0) | ~r2_hidden(A_505, C_506))), inference(superposition, [status(thm), theory('equality')], [c_6971, c_36])).
% 6.21/2.41  tff(c_7190, plain, (![C_513, A_514]: (k2_xboole_0(C_513, k1_tarski(A_514))=C_513 | ~r2_hidden(A_514, C_513))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_7014])).
% 6.21/2.41  tff(c_404, plain, (![B_104, A_103]: (k2_xboole_0(B_104, A_103)=k2_xboole_0(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_398, c_52])).
% 6.21/2.41  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.21/2.41  tff(c_441, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_404, c_60])).
% 6.21/2.41  tff(c_7441, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7190, c_441])).
% 6.21/2.41  tff(c_7502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_7441])).
% 6.21/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.41  
% 6.21/2.41  Inference rules
% 6.21/2.41  ----------------------
% 6.21/2.41  #Ref     : 0
% 6.21/2.41  #Sup     : 1918
% 6.21/2.41  #Fact    : 0
% 6.21/2.41  #Define  : 0
% 6.21/2.41  #Split   : 3
% 6.21/2.41  #Chain   : 0
% 6.21/2.41  #Close   : 0
% 6.21/2.41  
% 6.21/2.41  Ordering : KBO
% 6.21/2.41  
% 6.21/2.41  Simplification rules
% 6.21/2.41  ----------------------
% 6.21/2.41  #Subsume      : 842
% 6.21/2.41  #Demod        : 774
% 6.21/2.41  #Tautology    : 581
% 6.21/2.41  #SimpNegUnit  : 14
% 6.21/2.41  #BackRed      : 6
% 6.21/2.41  
% 6.21/2.41  #Partial instantiations: 0
% 6.21/2.41  #Strategies tried      : 1
% 6.21/2.41  
% 6.21/2.41  Timing (in seconds)
% 6.21/2.41  ----------------------
% 6.21/2.41  Preprocessing        : 0.32
% 6.21/2.41  Parsing              : 0.17
% 6.21/2.41  CNF conversion       : 0.02
% 6.21/2.41  Main loop            : 1.34
% 6.21/2.41  Inferencing          : 0.39
% 6.21/2.41  Reduction            : 0.53
% 6.21/2.41  Demodulation         : 0.40
% 6.21/2.41  BG Simplification    : 0.03
% 6.21/2.41  Subsumption          : 0.30
% 6.21/2.41  Abstraction          : 0.05
% 6.21/2.41  MUC search           : 0.00
% 6.21/2.41  Cooper               : 0.00
% 6.21/2.41  Total                : 1.69
% 6.21/2.41  Index Insertion      : 0.00
% 6.21/2.41  Index Deletion       : 0.00
% 6.21/2.41  Index Matching       : 0.00
% 6.21/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
