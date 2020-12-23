%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   72 (  94 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 115 expanded)
%              Number of equality atoms :   31 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_50,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_450,plain,(
    ! [B_103,A_104] :
      ( k1_tarski(B_103) = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,k1_tarski(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_479,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_450])).

tff(c_511,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_167,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_167])).

tff(c_765,plain,(
    ! [A_115,B_116,C_117] :
      ( k3_xboole_0(A_115,k2_xboole_0(B_116,C_117)) = k3_xboole_0(A_115,C_117)
      | ~ r1_xboole_0(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_126,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_46])).

tff(c_128,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_809,plain,
    ( k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0
    | ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_128])).

tff(c_852,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_2,c_809])).

tff(c_858,plain,(
    k3_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_852])).

tff(c_862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_2,c_858])).

tff(c_863,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_295,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2021,plain,(
    ! [A_167,B_168] : k5_xboole_0(A_167,k3_xboole_0(B_168,A_167)) = k4_xboole_0(A_167,B_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_295])).

tff(c_2059,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2021])).

tff(c_2074,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2059])).

tff(c_74,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    ! [B_60,A_61] : r1_tarski(k3_xboole_0(B_60,A_61),A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_16])).

tff(c_228,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_xboole_0(A_82,C_83)
      | ~ r1_tarski(A_82,k4_xboole_0(B_84,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    ! [B_60,B_84,C_83] : r1_xboole_0(k3_xboole_0(B_60,k4_xboole_0(B_84,C_83)),C_83) ),
    inference(resolution,[status(thm)],[c_89,c_228])).

tff(c_2101,plain,(
    ! [B_169] : r1_xboole_0(k3_xboole_0(B_169,'#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_247])).

tff(c_2115,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_863,c_2101])).

tff(c_22,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_278,plain,(
    ! [A_91,C_92,B_93] :
      ( ~ r2_hidden(A_91,C_92)
      | ~ r1_xboole_0(k2_tarski(A_91,B_93),C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_285,plain,(
    ! [A_19,C_92] :
      ( ~ r2_hidden(A_19,C_92)
      | ~ r1_xboole_0(k1_tarski(A_19),C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_278])).

tff(c_2132,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2115,c_285])).

tff(c_2139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.84  
% 4.13/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.13/1.84  
% 4.13/1.84  %Foreground sorts:
% 4.13/1.84  
% 4.13/1.84  
% 4.13/1.84  %Background operators:
% 4.13/1.84  
% 4.13/1.84  
% 4.13/1.84  %Foreground operators:
% 4.13/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.13/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.13/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.13/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.13/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.13/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.13/1.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.13/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.13/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.13/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.13/1.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.13/1.84  
% 4.22/1.86  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.22/1.86  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.22/1.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.22/1.86  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.22/1.86  tff(f_49, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.22/1.86  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.22/1.86  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.22/1.86  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.22/1.86  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.22/1.86  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.22/1.86  tff(f_76, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.22/1.86  tff(c_50, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.22/1.86  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.22/1.86  tff(c_450, plain, (![B_103, A_104]: (k1_tarski(B_103)=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, k1_tarski(B_103)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.22/1.86  tff(c_479, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_450])).
% 4.22/1.86  tff(c_511, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_479])).
% 4.22/1.86  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.86  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.86  tff(c_48, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.22/1.86  tff(c_167, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.86  tff(c_175, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_167])).
% 4.22/1.86  tff(c_765, plain, (![A_115, B_116, C_117]: (k3_xboole_0(A_115, k2_xboole_0(B_116, C_117))=k3_xboole_0(A_115, C_117) | ~r1_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.22/1.86  tff(c_123, plain, (![A_64, B_65]: (r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.86  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.22/1.86  tff(c_126, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_46])).
% 4.22/1.86  tff(c_128, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_126])).
% 4.22/1.86  tff(c_809, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0 | ~r1_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_765, c_128])).
% 4.22/1.86  tff(c_852, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_2, c_809])).
% 4.22/1.86  tff(c_858, plain, (k3_xboole_0('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_852])).
% 4.22/1.86  tff(c_862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_511, c_2, c_858])).
% 4.22/1.86  tff(c_863, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_479])).
% 4.22/1.86  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.22/1.86  tff(c_295, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.22/1.86  tff(c_2021, plain, (![A_167, B_168]: (k5_xboole_0(A_167, k3_xboole_0(B_168, A_167))=k4_xboole_0(A_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_2, c_295])).
% 4.22/1.86  tff(c_2059, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_2021])).
% 4.22/1.86  tff(c_2074, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2059])).
% 4.22/1.86  tff(c_74, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.86  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.22/1.86  tff(c_89, plain, (![B_60, A_61]: (r1_tarski(k3_xboole_0(B_60, A_61), A_61))), inference(superposition, [status(thm), theory('equality')], [c_74, c_16])).
% 4.22/1.86  tff(c_228, plain, (![A_82, C_83, B_84]: (r1_xboole_0(A_82, C_83) | ~r1_tarski(A_82, k4_xboole_0(B_84, C_83)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.86  tff(c_247, plain, (![B_60, B_84, C_83]: (r1_xboole_0(k3_xboole_0(B_60, k4_xboole_0(B_84, C_83)), C_83))), inference(resolution, [status(thm)], [c_89, c_228])).
% 4.22/1.86  tff(c_2101, plain, (![B_169]: (r1_xboole_0(k3_xboole_0(B_169, '#skF_2'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2074, c_247])).
% 4.22/1.86  tff(c_2115, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_863, c_2101])).
% 4.22/1.86  tff(c_22, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.22/1.86  tff(c_278, plain, (![A_91, C_92, B_93]: (~r2_hidden(A_91, C_92) | ~r1_xboole_0(k2_tarski(A_91, B_93), C_92))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.22/1.86  tff(c_285, plain, (![A_19, C_92]: (~r2_hidden(A_19, C_92) | ~r1_xboole_0(k1_tarski(A_19), C_92))), inference(superposition, [status(thm), theory('equality')], [c_22, c_278])).
% 4.22/1.86  tff(c_2132, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2115, c_285])).
% 4.22/1.86  tff(c_2139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2132])).
% 4.22/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.86  
% 4.22/1.86  Inference rules
% 4.22/1.86  ----------------------
% 4.22/1.86  #Ref     : 0
% 4.22/1.86  #Sup     : 525
% 4.22/1.86  #Fact    : 0
% 4.22/1.86  #Define  : 0
% 4.22/1.86  #Split   : 1
% 4.22/1.86  #Chain   : 0
% 4.22/1.86  #Close   : 0
% 4.22/1.86  
% 4.22/1.86  Ordering : KBO
% 4.22/1.86  
% 4.22/1.86  Simplification rules
% 4.22/1.86  ----------------------
% 4.22/1.86  #Subsume      : 1
% 4.22/1.86  #Demod        : 296
% 4.22/1.86  #Tautology    : 333
% 4.22/1.86  #SimpNegUnit  : 0
% 4.22/1.86  #BackRed      : 11
% 4.22/1.86  
% 4.22/1.86  #Partial instantiations: 0
% 4.22/1.86  #Strategies tried      : 1
% 4.22/1.86  
% 4.22/1.86  Timing (in seconds)
% 4.22/1.86  ----------------------
% 4.22/1.86  Preprocessing        : 0.38
% 4.22/1.86  Parsing              : 0.20
% 4.22/1.86  CNF conversion       : 0.02
% 4.22/1.86  Main loop            : 0.64
% 4.22/1.86  Inferencing          : 0.20
% 4.22/1.86  Reduction            : 0.25
% 4.22/1.86  Demodulation         : 0.20
% 4.22/1.86  BG Simplification    : 0.03
% 4.22/1.86  Subsumption          : 0.10
% 4.22/1.86  Abstraction          : 0.03
% 4.22/1.86  MUC search           : 0.00
% 4.22/1.86  Cooper               : 0.00
% 4.22/1.86  Total                : 1.05
% 4.22/1.86  Index Insertion      : 0.00
% 4.22/1.86  Index Deletion       : 0.00
% 4.22/1.86  Index Matching       : 0.00
% 4.22/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
