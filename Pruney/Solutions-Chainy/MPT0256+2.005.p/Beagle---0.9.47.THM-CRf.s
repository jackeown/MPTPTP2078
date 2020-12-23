%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:02 EST 2020

% Result     : Theorem 8.34s
% Output     : CNFRefutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 144 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 135 expanded)
%              Number of equality atoms :   40 ( 112 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_332,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k2_xboole_0(A_108,B_109)) = k3_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_365,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_332])).

tff(c_371,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_365])).

tff(c_462,plain,(
    ! [A_112,B_113,C_114] : k5_xboole_0(k5_xboole_0(A_112,B_113),C_114) = k5_xboole_0(A_112,k5_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_528,plain,(
    ! [A_10,C_114] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_114)) = k5_xboole_0(k1_xboole_0,C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_462])).

tff(c_541,plain,(
    ! [A_10,C_114] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_114)) = C_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_528])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_543,plain,(
    ! [A_115,C_116] : k5_xboole_0(A_115,k5_xboole_0(A_115,C_116)) = C_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_528])).

tff(c_611,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k5_xboole_0(B_118,A_117)) = B_118 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_543])).

tff(c_647,plain,(
    ! [A_10,C_114] : k5_xboole_0(k5_xboole_0(A_10,C_114),C_114) = A_10 ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_611])).

tff(c_64,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_11,B_12] : k5_xboole_0(k5_xboole_0(A_11,B_12),k2_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7388,plain,(
    ! [A_318,B_319,C_320] : k5_xboole_0(k5_xboole_0(A_318,B_319),k5_xboole_0(k2_xboole_0(A_318,B_319),C_320)) = k5_xboole_0(k3_xboole_0(A_318,B_319),C_320) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_462])).

tff(c_7793,plain,(
    ! [A_318,B_319] : k5_xboole_0(k3_xboole_0(A_318,B_319),k2_xboole_0(A_318,B_319)) = k5_xboole_0(k5_xboole_0(A_318,B_319),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_7388])).

tff(c_8953,plain,(
    ! [A_327,B_328] : k5_xboole_0(k3_xboole_0(A_327,B_328),k2_xboole_0(A_327,B_328)) = k5_xboole_0(A_327,B_328) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_2,c_7793])).

tff(c_9069,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k2_xboole_0('#skF_3',k1_tarski('#skF_4'))) = k5_xboole_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_8953])).

tff(c_592,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_543])).

tff(c_641,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),B_2) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_611])).

tff(c_10111,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_4')) = k2_xboole_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9069,c_641])).

tff(c_10139,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_10111])).

tff(c_54,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_139,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_151,plain,(
    ! [B_71,A_70] : r2_hidden(B_71,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_16])).

tff(c_52,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,k3_tarski(B_49))
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_202,plain,(
    ! [B_84,C_85,A_86] :
      ( r2_hidden(B_84,C_85)
      | ~ r1_tarski(k2_tarski(A_86,B_84),C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_218,plain,(
    ! [A_88,C_89] :
      ( r2_hidden(A_88,C_89)
      | ~ r1_tarski(k1_tarski(A_88),C_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_202])).

tff(c_245,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(A_93,k3_tarski(B_94))
      | ~ r2_hidden(k1_tarski(A_93),B_94) ) ),
    inference(resolution,[status(thm)],[c_52,c_218])).

tff(c_249,plain,(
    ! [A_93,A_70] : r2_hidden(A_93,k3_tarski(k2_tarski(A_70,k1_tarski(A_93)))) ),
    inference(resolution,[status(thm)],[c_151,c_245])).

tff(c_271,plain,(
    ! [A_93,A_70] : r2_hidden(A_93,k2_xboole_0(A_70,k1_tarski(A_93))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_249])).

tff(c_10178,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10139,c_271])).

tff(c_10191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_10178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.34/3.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/3.41  
% 8.34/3.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/3.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.34/3.41  
% 8.34/3.41  %Foreground sorts:
% 8.34/3.41  
% 8.34/3.41  
% 8.34/3.41  %Background operators:
% 8.34/3.41  
% 8.34/3.41  
% 8.34/3.41  %Foreground operators:
% 8.34/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.34/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.34/3.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.34/3.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.34/3.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.34/3.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.34/3.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.34/3.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.34/3.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.34/3.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.34/3.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.34/3.41  tff('#skF_3', type, '#skF_3': $i).
% 8.34/3.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.34/3.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.34/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.34/3.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.34/3.41  tff('#skF_4', type, '#skF_4': $i).
% 8.34/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.34/3.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.34/3.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.34/3.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.34/3.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 8.34/3.41  
% 8.34/3.43  tff(f_83, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 8.34/3.43  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.34/3.43  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.34/3.43  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.34/3.43  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.34/3.43  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.34/3.43  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.34/3.43  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.34/3.43  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.34/3.43  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 8.34/3.43  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 8.34/3.43  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.34/3.43  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.34/3.43  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.34/3.43  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.34/3.43  tff(c_10, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.34/3.43  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.34/3.43  tff(c_332, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k2_xboole_0(A_108, B_109))=k3_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.34/3.43  tff(c_365, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_332])).
% 8.34/3.43  tff(c_371, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_365])).
% 8.34/3.43  tff(c_462, plain, (![A_112, B_113, C_114]: (k5_xboole_0(k5_xboole_0(A_112, B_113), C_114)=k5_xboole_0(A_112, k5_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.34/3.43  tff(c_528, plain, (![A_10, C_114]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_114))=k5_xboole_0(k1_xboole_0, C_114))), inference(superposition, [status(thm), theory('equality')], [c_10, c_462])).
% 8.34/3.43  tff(c_541, plain, (![A_10, C_114]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_114))=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_371, c_528])).
% 8.34/3.43  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.34/3.43  tff(c_543, plain, (![A_115, C_116]: (k5_xboole_0(A_115, k5_xboole_0(A_115, C_116))=C_116)), inference(demodulation, [status(thm), theory('equality')], [c_371, c_528])).
% 8.34/3.43  tff(c_611, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k5_xboole_0(B_118, A_117))=B_118)), inference(superposition, [status(thm), theory('equality')], [c_2, c_543])).
% 8.34/3.43  tff(c_647, plain, (![A_10, C_114]: (k5_xboole_0(k5_xboole_0(A_10, C_114), C_114)=A_10)), inference(superposition, [status(thm), theory('equality')], [c_541, c_611])).
% 8.34/3.43  tff(c_64, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.34/3.43  tff(c_12, plain, (![A_11, B_12]: (k5_xboole_0(k5_xboole_0(A_11, B_12), k2_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.34/3.43  tff(c_7388, plain, (![A_318, B_319, C_320]: (k5_xboole_0(k5_xboole_0(A_318, B_319), k5_xboole_0(k2_xboole_0(A_318, B_319), C_320))=k5_xboole_0(k3_xboole_0(A_318, B_319), C_320))), inference(superposition, [status(thm), theory('equality')], [c_12, c_462])).
% 8.34/3.43  tff(c_7793, plain, (![A_318, B_319]: (k5_xboole_0(k3_xboole_0(A_318, B_319), k2_xboole_0(A_318, B_319))=k5_xboole_0(k5_xboole_0(A_318, B_319), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_7388])).
% 8.34/3.43  tff(c_8953, plain, (![A_327, B_328]: (k5_xboole_0(k3_xboole_0(A_327, B_328), k2_xboole_0(A_327, B_328))=k5_xboole_0(A_327, B_328))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_2, c_7793])).
% 8.34/3.43  tff(c_9069, plain, (k5_xboole_0(k1_tarski('#skF_4'), k2_xboole_0('#skF_3', k1_tarski('#skF_4')))=k5_xboole_0('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_8953])).
% 8.34/3.43  tff(c_592, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_543])).
% 8.34/3.43  tff(c_641, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), B_2)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_592, c_611])).
% 8.34/3.43  tff(c_10111, plain, (k5_xboole_0(k5_xboole_0('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_4'))=k2_xboole_0('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9069, c_641])).
% 8.34/3.43  tff(c_10139, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_10111])).
% 8.34/3.43  tff(c_54, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.34/3.43  tff(c_139, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.34/3.43  tff(c_16, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.34/3.43  tff(c_151, plain, (![B_71, A_70]: (r2_hidden(B_71, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_16])).
% 8.34/3.43  tff(c_52, plain, (![A_48, B_49]: (r1_tarski(A_48, k3_tarski(B_49)) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.34/3.43  tff(c_38, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.34/3.43  tff(c_202, plain, (![B_84, C_85, A_86]: (r2_hidden(B_84, C_85) | ~r1_tarski(k2_tarski(A_86, B_84), C_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.34/3.43  tff(c_218, plain, (![A_88, C_89]: (r2_hidden(A_88, C_89) | ~r1_tarski(k1_tarski(A_88), C_89))), inference(superposition, [status(thm), theory('equality')], [c_38, c_202])).
% 8.34/3.43  tff(c_245, plain, (![A_93, B_94]: (r2_hidden(A_93, k3_tarski(B_94)) | ~r2_hidden(k1_tarski(A_93), B_94))), inference(resolution, [status(thm)], [c_52, c_218])).
% 8.34/3.43  tff(c_249, plain, (![A_93, A_70]: (r2_hidden(A_93, k3_tarski(k2_tarski(A_70, k1_tarski(A_93)))))), inference(resolution, [status(thm)], [c_151, c_245])).
% 8.34/3.43  tff(c_271, plain, (![A_93, A_70]: (r2_hidden(A_93, k2_xboole_0(A_70, k1_tarski(A_93))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_249])).
% 8.34/3.43  tff(c_10178, plain, (r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10139, c_271])).
% 8.34/3.43  tff(c_10191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_10178])).
% 8.34/3.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/3.43  
% 8.34/3.43  Inference rules
% 8.34/3.43  ----------------------
% 8.34/3.43  #Ref     : 0
% 8.34/3.43  #Sup     : 2607
% 8.34/3.43  #Fact    : 0
% 8.34/3.43  #Define  : 0
% 8.34/3.43  #Split   : 0
% 8.34/3.43  #Chain   : 0
% 8.34/3.43  #Close   : 0
% 8.34/3.43  
% 8.34/3.43  Ordering : KBO
% 8.34/3.43  
% 8.34/3.43  Simplification rules
% 8.34/3.43  ----------------------
% 8.34/3.43  #Subsume      : 166
% 8.34/3.43  #Demod        : 2582
% 8.34/3.43  #Tautology    : 920
% 8.34/3.43  #SimpNegUnit  : 1
% 8.34/3.43  #BackRed      : 1
% 8.34/3.43  
% 8.34/3.43  #Partial instantiations: 0
% 8.34/3.43  #Strategies tried      : 1
% 8.34/3.43  
% 8.34/3.43  Timing (in seconds)
% 8.34/3.43  ----------------------
% 8.34/3.43  Preprocessing        : 0.32
% 8.34/3.43  Parsing              : 0.17
% 8.34/3.43  CNF conversion       : 0.02
% 8.34/3.43  Main loop            : 2.28
% 8.34/3.43  Inferencing          : 0.45
% 8.34/3.43  Reduction            : 1.42
% 8.34/3.43  Demodulation         : 1.31
% 8.34/3.43  BG Simplification    : 0.07
% 8.34/3.43  Subsumption          : 0.27
% 8.34/3.43  Abstraction          : 0.10
% 8.34/3.43  MUC search           : 0.00
% 8.34/3.43  Cooper               : 0.00
% 8.34/3.43  Total                : 2.64
% 8.34/3.43  Index Insertion      : 0.00
% 8.34/3.43  Index Deletion       : 0.00
% 8.34/3.43  Index Matching       : 0.00
% 8.34/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
