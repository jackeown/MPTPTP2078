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
% DateTime   : Thu Dec  3 09:50:26 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 120 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 169 expanded)
%              Number of equality atoms :   50 ( 132 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_54,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_14])).

tff(c_336,plain,(
    ! [B_91,A_92] :
      ( k1_tarski(B_91) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k1_tarski(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_343,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_91,c_336])).

tff(c_354,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_343])).

tff(c_361,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_56])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_207,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = k1_xboole_0
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_719,plain,(
    ! [A_109,B_110] :
      ( k3_xboole_0(k1_tarski(A_109),B_110) = k1_xboole_0
      | r2_hidden(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_40,c_207])).

tff(c_1215,plain,(
    ! [B_127] :
      ( k3_xboole_0('#skF_2',B_127) = k1_xboole_0
      | r2_hidden('#skF_1',B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_719])).

tff(c_38,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tarski(A_47),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_142,plain,(
    ! [A_72,B_73] :
      ( k2_xboole_0(A_72,B_73) = B_73
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(k1_tarski(A_47),B_48) = B_48
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_38,c_142])).

tff(c_370,plain,(
    ! [B_48] :
      ( k2_xboole_0('#skF_2',B_48) = B_48
      | ~ r2_hidden('#skF_1',B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_158])).

tff(c_1534,plain,(
    ! [B_139] :
      ( k2_xboole_0('#skF_2',B_139) = B_139
      | k3_xboole_0('#skF_2',B_139) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1215,c_370])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_545,plain,(
    ! [A_103,B_104] : k5_xboole_0(k5_xboole_0(A_103,B_104),k2_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_593,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,A_5),A_5) = k3_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_545])).

tff(c_602,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18,c_593])).

tff(c_741,plain,(
    ! [A_111,B_112,C_113] : k5_xboole_0(k5_xboole_0(A_111,B_112),C_113) = k5_xboole_0(A_111,k5_xboole_0(B_112,C_113)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_807,plain,(
    ! [A_16,C_113] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_113)) = k5_xboole_0(k1_xboole_0,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_741])).

tff(c_821,plain,(
    ! [A_114,C_115] : k5_xboole_0(A_114,k5_xboole_0(A_114,C_115)) = C_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_807])).

tff(c_870,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_821])).

tff(c_569,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_545])).

tff(c_600,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_569])).

tff(c_1225,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_600])).

tff(c_1540,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1534,c_1225])).

tff(c_1562,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_1540])).

tff(c_1564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_1562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.52  
% 3.21/1.52  %Foreground sorts:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Background operators:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Foreground operators:
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.21/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.52  
% 3.21/1.53  tff(f_91, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.21/1.53  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.21/1.53  tff(f_76, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.21/1.53  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.21/1.53  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.21/1.53  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.21/1.53  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.21/1.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.21/1.53  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.21/1.53  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.21/1.53  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.21/1.53  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.21/1.53  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.21/1.53  tff(c_54, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.53  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.53  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.53  tff(c_56, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.53  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.53  tff(c_91, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_14])).
% 3.21/1.53  tff(c_336, plain, (![B_91, A_92]: (k1_tarski(B_91)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k1_tarski(B_91)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.21/1.53  tff(c_343, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_91, c_336])).
% 3.21/1.53  tff(c_354, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_343])).
% 3.21/1.53  tff(c_361, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_56])).
% 3.21/1.53  tff(c_40, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.21/1.53  tff(c_207, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=k1_xboole_0 | ~r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.53  tff(c_719, plain, (![A_109, B_110]: (k3_xboole_0(k1_tarski(A_109), B_110)=k1_xboole_0 | r2_hidden(A_109, B_110))), inference(resolution, [status(thm)], [c_40, c_207])).
% 3.21/1.53  tff(c_1215, plain, (![B_127]: (k3_xboole_0('#skF_2', B_127)=k1_xboole_0 | r2_hidden('#skF_1', B_127))), inference(superposition, [status(thm), theory('equality')], [c_354, c_719])).
% 3.21/1.53  tff(c_38, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.53  tff(c_142, plain, (![A_72, B_73]: (k2_xboole_0(A_72, B_73)=B_73 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.53  tff(c_158, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), B_48)=B_48 | ~r2_hidden(A_47, B_48))), inference(resolution, [status(thm)], [c_38, c_142])).
% 3.21/1.53  tff(c_370, plain, (![B_48]: (k2_xboole_0('#skF_2', B_48)=B_48 | ~r2_hidden('#skF_1', B_48))), inference(superposition, [status(thm), theory('equality')], [c_354, c_158])).
% 3.21/1.53  tff(c_1534, plain, (![B_139]: (k2_xboole_0('#skF_2', B_139)=B_139 | k3_xboole_0('#skF_2', B_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1215, c_370])).
% 3.21/1.53  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.53  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.53  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.53  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.53  tff(c_545, plain, (![A_103, B_104]: (k5_xboole_0(k5_xboole_0(A_103, B_104), k2_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.53  tff(c_593, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, A_5), A_5)=k3_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_545])).
% 3.21/1.53  tff(c_602, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18, c_593])).
% 3.21/1.53  tff(c_741, plain, (![A_111, B_112, C_113]: (k5_xboole_0(k5_xboole_0(A_111, B_112), C_113)=k5_xboole_0(A_111, k5_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.53  tff(c_807, plain, (![A_16, C_113]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_113))=k5_xboole_0(k1_xboole_0, C_113))), inference(superposition, [status(thm), theory('equality')], [c_18, c_741])).
% 3.21/1.53  tff(c_821, plain, (![A_114, C_115]: (k5_xboole_0(A_114, k5_xboole_0(A_114, C_115))=C_115)), inference(demodulation, [status(thm), theory('equality')], [c_602, c_807])).
% 3.21/1.53  tff(c_870, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_821])).
% 3.21/1.53  tff(c_569, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_361, c_545])).
% 3.21/1.53  tff(c_600, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_569])).
% 3.21/1.53  tff(c_1225, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_870, c_600])).
% 3.21/1.53  tff(c_1540, plain, (k1_xboole_0='#skF_3' | k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1534, c_1225])).
% 3.21/1.53  tff(c_1562, plain, (k1_xboole_0='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_1540])).
% 3.21/1.53  tff(c_1564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_1562])).
% 3.21/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.53  
% 3.21/1.53  Inference rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Ref     : 0
% 3.21/1.53  #Sup     : 364
% 3.21/1.53  #Fact    : 0
% 3.21/1.53  #Define  : 0
% 3.21/1.53  #Split   : 0
% 3.21/1.53  #Chain   : 0
% 3.21/1.53  #Close   : 0
% 3.21/1.53  
% 3.21/1.53  Ordering : KBO
% 3.21/1.53  
% 3.21/1.53  Simplification rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Subsume      : 7
% 3.21/1.53  #Demod        : 212
% 3.21/1.53  #Tautology    : 241
% 3.21/1.53  #SimpNegUnit  : 7
% 3.21/1.53  #BackRed      : 3
% 3.21/1.53  
% 3.21/1.53  #Partial instantiations: 0
% 3.21/1.53  #Strategies tried      : 1
% 3.21/1.53  
% 3.21/1.53  Timing (in seconds)
% 3.21/1.53  ----------------------
% 3.21/1.53  Preprocessing        : 0.33
% 3.21/1.53  Parsing              : 0.18
% 3.21/1.53  CNF conversion       : 0.02
% 3.21/1.53  Main loop            : 0.41
% 3.21/1.53  Inferencing          : 0.14
% 3.21/1.53  Reduction            : 0.16
% 3.21/1.53  Demodulation         : 0.13
% 3.21/1.53  BG Simplification    : 0.02
% 3.21/1.53  Subsumption          : 0.06
% 3.21/1.53  Abstraction          : 0.02
% 3.21/1.53  MUC search           : 0.00
% 3.21/1.53  Cooper               : 0.00
% 3.21/1.53  Total                : 0.76
% 3.21/1.53  Index Insertion      : 0.00
% 3.21/1.53  Index Deletion       : 0.00
% 3.21/1.53  Index Matching       : 0.00
% 3.21/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
