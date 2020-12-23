%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 129 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 163 expanded)
%              Number of equality atoms :   59 ( 122 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
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

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_40,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,(
    ! [B_52,A_53] : r2_hidden(B_52,k2_tarski(A_53,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_16])).

tff(c_115,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_112])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = A_62
      | ~ r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_163])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_172,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_253,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,k4_xboole_0(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_172])).

tff(c_282,plain,(
    ! [A_84] : k3_xboole_0(A_84,k4_xboole_0(A_84,k1_xboole_0)) = k4_xboole_0(A_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_253])).

tff(c_299,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,k1_xboole_0) = k3_xboole_0(A_1,A_1)
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_282])).

tff(c_324,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = k3_xboole_0(A_89,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_299])).

tff(c_339,plain,(
    ! [A_89] :
      ( k3_xboole_0(A_89,A_89) = A_89
      | k3_xboole_0(A_89,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_171])).

tff(c_374,plain,(
    ! [A_90] : k3_xboole_0(A_90,A_90) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_339])).

tff(c_123,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,B_58)
      | ~ r1_xboole_0(k1_tarski(A_57),B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,(
    ! [A_57,B_2] :
      ( ~ r2_hidden(A_57,B_2)
      | k3_xboole_0(k1_tarski(A_57),B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_123])).

tff(c_384,plain,(
    ! [A_57] :
      ( ~ r2_hidden(A_57,k1_tarski(A_57))
      | k1_tarski(A_57) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_133])).

tff(c_398,plain,(
    ! [A_57] : k1_tarski(A_57) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_384])).

tff(c_52,plain,(
    ! [A_31] : k1_setfam_1(k1_tarski(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_230,plain,(
    ! [A_76,B_77,C_78,D_79] : k2_xboole_0(k1_enumset1(A_76,B_77,C_78),k1_tarski(D_79)) = k2_enumset1(A_76,B_77,C_78,D_79) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_239,plain,(
    ! [A_20,B_21,D_79] : k2_xboole_0(k2_tarski(A_20,B_21),k1_tarski(D_79)) = k2_enumset1(A_20,A_20,B_21,D_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_230])).

tff(c_516,plain,(
    ! [A_100,B_101,D_102] : k2_xboole_0(k2_tarski(A_100,B_101),k1_tarski(D_102)) = k1_enumset1(A_100,B_101,D_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_239])).

tff(c_525,plain,(
    ! [A_19,D_102] : k2_xboole_0(k1_tarski(A_19),k1_tarski(D_102)) = k1_enumset1(A_19,A_19,D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_516])).

tff(c_528,plain,(
    ! [A_19,D_102] : k2_xboole_0(k1_tarski(A_19),k1_tarski(D_102)) = k2_tarski(A_19,D_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_525])).

tff(c_442,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(k1_setfam_1(A_93),k1_setfam_1(B_94)) = k1_setfam_1(k2_xboole_0(A_93,B_94))
      | k1_xboole_0 = B_94
      | k1_xboole_0 = A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_465,plain,(
    ! [A_93,A_31] :
      ( k1_setfam_1(k2_xboole_0(A_93,k1_tarski(A_31))) = k3_xboole_0(k1_setfam_1(A_93),A_31)
      | k1_tarski(A_31) = k1_xboole_0
      | k1_xboole_0 = A_93 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_442])).

tff(c_790,plain,(
    ! [A_139,A_140] :
      ( k1_setfam_1(k2_xboole_0(A_139,k1_tarski(A_140))) = k3_xboole_0(k1_setfam_1(A_139),A_140)
      | k1_xboole_0 = A_139 ) ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_465])).

tff(c_813,plain,(
    ! [A_19,D_102] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_19)),D_102) = k1_setfam_1(k2_tarski(A_19,D_102))
      | k1_tarski(A_19) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_790])).

tff(c_830,plain,(
    ! [A_19,D_102] :
      ( k1_setfam_1(k2_tarski(A_19,D_102)) = k3_xboole_0(A_19,D_102)
      | k1_tarski(A_19) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_813])).

tff(c_831,plain,(
    ! [A_19,D_102] : k1_setfam_1(k2_tarski(A_19,D_102)) = k3_xboole_0(A_19,D_102) ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_830])).

tff(c_54,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:23:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.48  
% 2.90/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.48  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.90/1.48  
% 2.90/1.48  %Foreground sorts:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Background operators:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Foreground operators:
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.90/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.90/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.90/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.90/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.90/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.90/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.90/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.90/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.90/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.90/1.48  
% 2.90/1.50  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.90/1.50  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.90/1.50  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.90/1.50  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.90/1.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.90/1.50  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.90/1.50  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.90/1.50  tff(f_65, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.90/1.50  tff(f_79, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.90/1.50  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.90/1.50  tff(f_54, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.90/1.50  tff(f_77, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.90/1.50  tff(f_82, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.90/1.50  tff(c_40, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.90/1.50  tff(c_94, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.50  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.90/1.50  tff(c_112, plain, (![B_52, A_53]: (r2_hidden(B_52, k2_tarski(A_53, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_16])).
% 2.90/1.50  tff(c_115, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_112])).
% 2.90/1.50  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.50  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.90/1.50  tff(c_163, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=A_62 | ~r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.50  tff(c_171, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_163])).
% 2.90/1.50  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.50  tff(c_172, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.50  tff(c_253, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k3_xboole_0(A_82, k4_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_172])).
% 2.90/1.50  tff(c_282, plain, (![A_84]: (k3_xboole_0(A_84, k4_xboole_0(A_84, k1_xboole_0))=k4_xboole_0(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_253])).
% 2.90/1.50  tff(c_299, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=k3_xboole_0(A_1, A_1) | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_282])).
% 2.90/1.50  tff(c_324, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=k3_xboole_0(A_89, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_299])).
% 2.90/1.50  tff(c_339, plain, (![A_89]: (k3_xboole_0(A_89, A_89)=A_89 | k3_xboole_0(A_89, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_171])).
% 2.90/1.50  tff(c_374, plain, (![A_90]: (k3_xboole_0(A_90, A_90)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_339])).
% 2.90/1.50  tff(c_123, plain, (![A_57, B_58]: (~r2_hidden(A_57, B_58) | ~r1_xboole_0(k1_tarski(A_57), B_58))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.90/1.50  tff(c_133, plain, (![A_57, B_2]: (~r2_hidden(A_57, B_2) | k3_xboole_0(k1_tarski(A_57), B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_123])).
% 2.90/1.50  tff(c_384, plain, (![A_57]: (~r2_hidden(A_57, k1_tarski(A_57)) | k1_tarski(A_57)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_374, c_133])).
% 2.90/1.50  tff(c_398, plain, (![A_57]: (k1_tarski(A_57)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_384])).
% 2.90/1.50  tff(c_52, plain, (![A_31]: (k1_setfam_1(k1_tarski(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.90/1.50  tff(c_42, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.50  tff(c_44, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.90/1.50  tff(c_230, plain, (![A_76, B_77, C_78, D_79]: (k2_xboole_0(k1_enumset1(A_76, B_77, C_78), k1_tarski(D_79))=k2_enumset1(A_76, B_77, C_78, D_79))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.90/1.50  tff(c_239, plain, (![A_20, B_21, D_79]: (k2_xboole_0(k2_tarski(A_20, B_21), k1_tarski(D_79))=k2_enumset1(A_20, A_20, B_21, D_79))), inference(superposition, [status(thm), theory('equality')], [c_42, c_230])).
% 2.90/1.50  tff(c_516, plain, (![A_100, B_101, D_102]: (k2_xboole_0(k2_tarski(A_100, B_101), k1_tarski(D_102))=k1_enumset1(A_100, B_101, D_102))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_239])).
% 2.90/1.50  tff(c_525, plain, (![A_19, D_102]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(D_102))=k1_enumset1(A_19, A_19, D_102))), inference(superposition, [status(thm), theory('equality')], [c_40, c_516])).
% 2.90/1.50  tff(c_528, plain, (![A_19, D_102]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(D_102))=k2_tarski(A_19, D_102))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_525])).
% 2.90/1.50  tff(c_442, plain, (![A_93, B_94]: (k3_xboole_0(k1_setfam_1(A_93), k1_setfam_1(B_94))=k1_setfam_1(k2_xboole_0(A_93, B_94)) | k1_xboole_0=B_94 | k1_xboole_0=A_93)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.90/1.50  tff(c_465, plain, (![A_93, A_31]: (k1_setfam_1(k2_xboole_0(A_93, k1_tarski(A_31)))=k3_xboole_0(k1_setfam_1(A_93), A_31) | k1_tarski(A_31)=k1_xboole_0 | k1_xboole_0=A_93)), inference(superposition, [status(thm), theory('equality')], [c_52, c_442])).
% 2.90/1.50  tff(c_790, plain, (![A_139, A_140]: (k1_setfam_1(k2_xboole_0(A_139, k1_tarski(A_140)))=k3_xboole_0(k1_setfam_1(A_139), A_140) | k1_xboole_0=A_139)), inference(negUnitSimplification, [status(thm)], [c_398, c_465])).
% 2.90/1.50  tff(c_813, plain, (![A_19, D_102]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_19)), D_102)=k1_setfam_1(k2_tarski(A_19, D_102)) | k1_tarski(A_19)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_528, c_790])).
% 2.90/1.50  tff(c_830, plain, (![A_19, D_102]: (k1_setfam_1(k2_tarski(A_19, D_102))=k3_xboole_0(A_19, D_102) | k1_tarski(A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_813])).
% 2.90/1.50  tff(c_831, plain, (![A_19, D_102]: (k1_setfam_1(k2_tarski(A_19, D_102))=k3_xboole_0(A_19, D_102))), inference(negUnitSimplification, [status(thm)], [c_398, c_830])).
% 2.90/1.50  tff(c_54, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.90/1.50  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_831, c_54])).
% 2.90/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.50  
% 2.90/1.50  Inference rules
% 2.90/1.50  ----------------------
% 2.90/1.50  #Ref     : 0
% 2.90/1.50  #Sup     : 176
% 2.90/1.50  #Fact    : 0
% 2.90/1.50  #Define  : 0
% 2.90/1.50  #Split   : 0
% 2.90/1.50  #Chain   : 0
% 2.90/1.50  #Close   : 0
% 2.90/1.50  
% 2.90/1.50  Ordering : KBO
% 2.90/1.50  
% 2.90/1.50  Simplification rules
% 2.90/1.50  ----------------------
% 2.90/1.50  #Subsume      : 10
% 2.90/1.50  #Demod        : 91
% 2.90/1.50  #Tautology    : 106
% 2.90/1.50  #SimpNegUnit  : 8
% 2.90/1.50  #BackRed      : 3
% 2.90/1.50  
% 2.90/1.50  #Partial instantiations: 0
% 2.90/1.50  #Strategies tried      : 1
% 2.90/1.50  
% 2.90/1.50  Timing (in seconds)
% 2.90/1.50  ----------------------
% 2.90/1.50  Preprocessing        : 0.34
% 2.90/1.50  Parsing              : 0.18
% 2.90/1.50  CNF conversion       : 0.03
% 2.90/1.50  Main loop            : 0.34
% 2.90/1.50  Inferencing          : 0.13
% 2.90/1.50  Reduction            : 0.11
% 2.90/1.50  Demodulation         : 0.08
% 2.90/1.50  BG Simplification    : 0.02
% 2.90/1.50  Subsumption          : 0.06
% 2.90/1.50  Abstraction          : 0.02
% 2.90/1.50  MUC search           : 0.00
% 2.90/1.50  Cooper               : 0.00
% 2.90/1.50  Total                : 0.71
% 2.90/1.50  Index Insertion      : 0.00
% 2.90/1.50  Index Deletion       : 0.00
% 2.90/1.50  Index Matching       : 0.00
% 2.90/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
