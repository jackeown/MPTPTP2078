%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:52 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 132 expanded)
%              Number of leaves         :   42 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :   69 ( 143 expanded)
%              Number of equality atoms :   42 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_72,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_94,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_72,plain,(
    ! [C_45] : r2_hidden(C_45,k1_tarski(C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_283,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2647,plain,(
    ! [A_231,B_232] : k3_xboole_0(k4_xboole_0(A_231,B_232),A_231) = k4_xboole_0(A_231,B_232) ),
    inference(resolution,[status(thm)],[c_36,c_283])).

tff(c_40,plain,(
    ! [A_27,B_28] : r1_xboole_0(k4_xboole_0(A_27,B_28),B_28) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_461,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,k3_xboole_0(A_112,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_709,plain,(
    ! [A_132,B_133] :
      ( ~ r1_xboole_0(A_132,B_133)
      | k3_xboole_0(A_132,B_133) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_461])).

tff(c_730,plain,(
    ! [A_27,B_28] : k3_xboole_0(k4_xboole_0(A_27,B_28),B_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_709])).

tff(c_2670,plain,(
    ! [A_231] : k4_xboole_0(A_231,A_231) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2647,c_730])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_356,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_379,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_356])).

tff(c_2760,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2670,c_379])).

tff(c_96,plain,(
    k2_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_179,plain,(
    ! [B_89,A_90] : k5_xboole_0(B_89,A_90) = k5_xboole_0(A_90,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_195,plain,(
    ! [A_90] : k5_xboole_0(k1_xboole_0,A_90) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_38])).

tff(c_2824,plain,(
    ! [A_239] : k5_xboole_0(A_239,A_239) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2670,c_379])).

tff(c_42,plain,(
    ! [A_29,B_30,C_31] : k5_xboole_0(k5_xboole_0(A_29,B_30),C_31) = k5_xboole_0(A_29,k5_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2829,plain,(
    ! [A_239,C_31] : k5_xboole_0(A_239,k5_xboole_0(A_239,C_31)) = k5_xboole_0(k1_xboole_0,C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_2824,c_42])).

tff(c_2902,plain,(
    ! [A_244,C_245] : k5_xboole_0(A_244,k5_xboole_0(A_244,C_245)) = C_245 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_2829])).

tff(c_4335,plain,(
    ! [A_316,B_317] : k5_xboole_0(A_316,k2_xboole_0(A_316,B_317)) = k4_xboole_0(B_317,A_316) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2902])).

tff(c_4390,plain,(
    k5_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k4_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4335])).

tff(c_4401,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_4390])).

tff(c_32,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2941,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2902])).

tff(c_4405,plain,(
    k3_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) = k5_xboole_0(k1_tarski('#skF_10'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4401,c_2941])).

tff(c_4453,plain,(
    k3_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4405])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4626,plain,(
    ! [D_320] :
      ( r2_hidden(D_320,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_320,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4453,c_8])).

tff(c_4691,plain,(
    r2_hidden('#skF_10',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_72,c_4626])).

tff(c_70,plain,(
    ! [C_45,A_41] :
      ( C_45 = A_41
      | ~ r2_hidden(C_45,k1_tarski(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4694,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4691,c_70])).

tff(c_4698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.95  
% 4.73/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.95  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7
% 4.73/1.95  
% 4.73/1.95  %Foreground sorts:
% 4.73/1.95  
% 4.73/1.95  
% 4.73/1.95  %Background operators:
% 4.73/1.95  
% 4.73/1.95  
% 4.73/1.95  %Foreground operators:
% 4.73/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.73/1.95  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.73/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.73/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.73/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.73/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.73/1.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.73/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.73/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.73/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.73/1.95  tff('#skF_10', type, '#skF_10': $i).
% 4.73/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.73/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.73/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.73/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.73/1.95  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.73/1.95  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.73/1.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.73/1.95  tff('#skF_9', type, '#skF_9': $i).
% 4.73/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.95  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.73/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.73/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.73/1.95  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.73/1.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.73/1.95  
% 4.73/1.96  tff(f_117, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 4.73/1.96  tff(f_100, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.73/1.96  tff(f_72, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.73/1.96  tff(f_70, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.73/1.96  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.73/1.96  tff(f_74, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.73/1.96  tff(f_62, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.73/1.96  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.73/1.96  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.73/1.96  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.73/1.96  tff(f_78, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.73/1.96  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.73/1.96  tff(f_76, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.73/1.96  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.73/1.96  tff(c_94, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.73/1.96  tff(c_72, plain, (![C_45]: (r2_hidden(C_45, k1_tarski(C_45)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.73/1.96  tff(c_38, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.73/1.96  tff(c_36, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.73/1.96  tff(c_283, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.73/1.96  tff(c_2647, plain, (![A_231, B_232]: (k3_xboole_0(k4_xboole_0(A_231, B_232), A_231)=k4_xboole_0(A_231, B_232))), inference(resolution, [status(thm)], [c_36, c_283])).
% 4.73/1.96  tff(c_40, plain, (![A_27, B_28]: (r1_xboole_0(k4_xboole_0(A_27, B_28), B_28))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.73/1.96  tff(c_30, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.73/1.96  tff(c_461, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, k3_xboole_0(A_112, B_113)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.73/1.96  tff(c_709, plain, (![A_132, B_133]: (~r1_xboole_0(A_132, B_133) | k3_xboole_0(A_132, B_133)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_461])).
% 4.73/1.96  tff(c_730, plain, (![A_27, B_28]: (k3_xboole_0(k4_xboole_0(A_27, B_28), B_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_709])).
% 4.73/1.96  tff(c_2670, plain, (![A_231]: (k4_xboole_0(A_231, A_231)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2647, c_730])).
% 4.73/1.96  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.73/1.96  tff(c_356, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.73/1.96  tff(c_379, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_24, c_356])).
% 4.73/1.96  tff(c_2760, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2670, c_379])).
% 4.73/1.96  tff(c_96, plain, (k2_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.73/1.96  tff(c_44, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.73/1.96  tff(c_179, plain, (![B_89, A_90]: (k5_xboole_0(B_89, A_90)=k5_xboole_0(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.73/1.96  tff(c_195, plain, (![A_90]: (k5_xboole_0(k1_xboole_0, A_90)=A_90)), inference(superposition, [status(thm), theory('equality')], [c_179, c_38])).
% 4.73/1.96  tff(c_2824, plain, (![A_239]: (k5_xboole_0(A_239, A_239)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2670, c_379])).
% 4.73/1.96  tff(c_42, plain, (![A_29, B_30, C_31]: (k5_xboole_0(k5_xboole_0(A_29, B_30), C_31)=k5_xboole_0(A_29, k5_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.73/1.96  tff(c_2829, plain, (![A_239, C_31]: (k5_xboole_0(A_239, k5_xboole_0(A_239, C_31))=k5_xboole_0(k1_xboole_0, C_31))), inference(superposition, [status(thm), theory('equality')], [c_2824, c_42])).
% 4.73/1.96  tff(c_2902, plain, (![A_244, C_245]: (k5_xboole_0(A_244, k5_xboole_0(A_244, C_245))=C_245)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_2829])).
% 4.73/1.96  tff(c_4335, plain, (![A_316, B_317]: (k5_xboole_0(A_316, k2_xboole_0(A_316, B_317))=k4_xboole_0(B_317, A_316))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2902])).
% 4.73/1.96  tff(c_4390, plain, (k5_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k4_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4335])).
% 4.73/1.96  tff(c_4401, plain, (k4_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_4390])).
% 4.73/1.96  tff(c_32, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.73/1.96  tff(c_2941, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2902])).
% 4.73/1.96  tff(c_4405, plain, (k3_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))=k5_xboole_0(k1_tarski('#skF_10'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4401, c_2941])).
% 4.73/1.96  tff(c_4453, plain, (k3_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4405])).
% 4.73/1.96  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.73/1.96  tff(c_4626, plain, (![D_320]: (r2_hidden(D_320, k1_tarski('#skF_9')) | ~r2_hidden(D_320, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_4453, c_8])).
% 4.73/1.96  tff(c_4691, plain, (r2_hidden('#skF_10', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_72, c_4626])).
% 4.73/1.96  tff(c_70, plain, (![C_45, A_41]: (C_45=A_41 | ~r2_hidden(C_45, k1_tarski(A_41)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.73/1.96  tff(c_4694, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_4691, c_70])).
% 4.73/1.96  tff(c_4698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_4694])).
% 4.73/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.96  
% 4.73/1.96  Inference rules
% 4.73/1.96  ----------------------
% 4.73/1.96  #Ref     : 0
% 4.73/1.96  #Sup     : 1078
% 4.73/1.96  #Fact    : 0
% 4.73/1.96  #Define  : 0
% 4.73/1.96  #Split   : 0
% 4.73/1.96  #Chain   : 0
% 4.73/1.96  #Close   : 0
% 4.73/1.96  
% 4.73/1.96  Ordering : KBO
% 4.73/1.96  
% 4.73/1.96  Simplification rules
% 4.73/1.96  ----------------------
% 4.73/1.96  #Subsume      : 130
% 4.73/1.96  #Demod        : 647
% 4.73/1.96  #Tautology    : 653
% 4.73/1.96  #SimpNegUnit  : 31
% 4.73/1.96  #BackRed      : 14
% 4.73/1.96  
% 4.73/1.96  #Partial instantiations: 0
% 4.73/1.96  #Strategies tried      : 1
% 4.73/1.96  
% 4.73/1.96  Timing (in seconds)
% 4.73/1.96  ----------------------
% 4.73/1.97  Preprocessing        : 0.36
% 4.73/1.97  Parsing              : 0.18
% 4.73/1.97  CNF conversion       : 0.03
% 4.73/1.97  Main loop            : 0.81
% 4.73/1.97  Inferencing          : 0.28
% 4.73/1.97  Reduction            : 0.30
% 4.73/1.97  Demodulation         : 0.24
% 4.73/1.97  BG Simplification    : 0.04
% 4.73/1.97  Subsumption          : 0.13
% 4.73/1.97  Abstraction          : 0.05
% 4.73/1.97  MUC search           : 0.00
% 4.73/1.97  Cooper               : 0.00
% 4.73/1.97  Total                : 1.20
% 4.73/1.97  Index Insertion      : 0.00
% 4.73/1.97  Index Deletion       : 0.00
% 4.73/1.97  Index Matching       : 0.00
% 4.73/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
