%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:08 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   70 (  80 expanded)
%              Number of leaves         :   38 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 (  73 expanded)
%              Number of equality atoms :   49 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_80,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_986,plain,(
    ! [A_125,B_126,C_127,D_128] : k2_xboole_0(k1_enumset1(A_125,B_126,C_127),k1_tarski(D_128)) = k2_enumset1(A_125,B_126,C_127,D_128) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1025,plain,(
    ! [A_34,B_35,D_128] : k2_xboole_0(k2_tarski(A_34,B_35),k1_tarski(D_128)) = k2_enumset1(A_34,A_34,B_35,D_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_986])).

tff(c_1126,plain,(
    ! [A_136,B_137,D_138] : k2_xboole_0(k2_tarski(A_136,B_137),k1_tarski(D_138)) = k1_enumset1(A_136,B_137,D_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1025])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_320,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_335,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_339,plain,(
    ! [A_97] : k4_xboole_0(A_97,k1_xboole_0) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_335])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_345,plain,(
    ! [A_97] : k4_xboole_0(A_97,A_97) = k3_xboole_0(A_97,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_10])).

tff(c_353,plain,(
    ! [A_97] : k4_xboole_0(A_97,A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_345])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_332,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_484,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_332])).

tff(c_82,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_140,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_144,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_140])).

tff(c_329,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_320])).

tff(c_502,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_329])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_509,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_14])).

tff(c_513,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_509])).

tff(c_1132,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1126,c_513])).

tff(c_18,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1160,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_18])).

tff(c_40,plain,(
    ! [D_25,B_21,A_20] :
      ( D_25 = B_21
      | D_25 = A_20
      | ~ r2_hidden(D_25,k2_tarski(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1181,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1160,c_40])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_1181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:57:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.52  
% 3.11/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.53  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 3.11/1.53  
% 3.11/1.53  %Foreground sorts:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Background operators:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Foreground operators:
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.11/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.11/1.53  
% 3.22/1.54  tff(f_95, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.22/1.54  tff(f_75, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.22/1.54  tff(f_73, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.22/1.54  tff(f_69, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.22/1.54  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.22/1.54  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.22/1.54  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.54  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.22/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.22/1.54  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.54  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.22/1.54  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.22/1.54  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.22/1.54  tff(c_80, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.54  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.54  tff(c_66, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.54  tff(c_64, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.54  tff(c_986, plain, (![A_125, B_126, C_127, D_128]: (k2_xboole_0(k1_enumset1(A_125, B_126, C_127), k1_tarski(D_128))=k2_enumset1(A_125, B_126, C_127, D_128))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.54  tff(c_1025, plain, (![A_34, B_35, D_128]: (k2_xboole_0(k2_tarski(A_34, B_35), k1_tarski(D_128))=k2_enumset1(A_34, A_34, B_35, D_128))), inference(superposition, [status(thm), theory('equality')], [c_64, c_986])).
% 3.22/1.54  tff(c_1126, plain, (![A_136, B_137, D_138]: (k2_xboole_0(k2_tarski(A_136, B_137), k1_tarski(D_138))=k1_enumset1(A_136, B_137, D_138))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1025])).
% 3.22/1.54  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.54  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.54  tff(c_320, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.54  tff(c_335, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_320])).
% 3.22/1.54  tff(c_339, plain, (![A_97]: (k4_xboole_0(A_97, k1_xboole_0)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_335])).
% 3.22/1.54  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.54  tff(c_345, plain, (![A_97]: (k4_xboole_0(A_97, A_97)=k3_xboole_0(A_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_339, c_10])).
% 3.22/1.54  tff(c_353, plain, (![A_97]: (k4_xboole_0(A_97, A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_345])).
% 3.22/1.54  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.54  tff(c_332, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_320])).
% 3.22/1.54  tff(c_484, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_353, c_332])).
% 3.22/1.54  tff(c_82, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.54  tff(c_140, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=A_82 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.54  tff(c_144, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_82, c_140])).
% 3.22/1.54  tff(c_329, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_320])).
% 3.22/1.54  tff(c_502, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_484, c_329])).
% 3.22/1.54  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.54  tff(c_509, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_502, c_14])).
% 3.22/1.54  tff(c_513, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_509])).
% 3.22/1.54  tff(c_1132, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1126, c_513])).
% 3.22/1.54  tff(c_18, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.54  tff(c_1160, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1132, c_18])).
% 3.22/1.54  tff(c_40, plain, (![D_25, B_21, A_20]: (D_25=B_21 | D_25=A_20 | ~r2_hidden(D_25, k2_tarski(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.54  tff(c_1181, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1160, c_40])).
% 3.22/1.54  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_1181])).
% 3.22/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.54  
% 3.22/1.54  Inference rules
% 3.22/1.54  ----------------------
% 3.22/1.54  #Ref     : 0
% 3.22/1.54  #Sup     : 283
% 3.22/1.54  #Fact    : 0
% 3.22/1.54  #Define  : 0
% 3.22/1.54  #Split   : 0
% 3.22/1.54  #Chain   : 0
% 3.22/1.54  #Close   : 0
% 3.22/1.54  
% 3.22/1.54  Ordering : KBO
% 3.22/1.54  
% 3.22/1.54  Simplification rules
% 3.22/1.54  ----------------------
% 3.22/1.54  #Subsume      : 53
% 3.22/1.54  #Demod        : 116
% 3.22/1.54  #Tautology    : 181
% 3.22/1.54  #SimpNegUnit  : 1
% 3.22/1.54  #BackRed      : 0
% 3.22/1.54  
% 3.22/1.54  #Partial instantiations: 0
% 3.22/1.54  #Strategies tried      : 1
% 3.22/1.54  
% 3.22/1.54  Timing (in seconds)
% 3.22/1.54  ----------------------
% 3.22/1.54  Preprocessing        : 0.36
% 3.22/1.54  Parsing              : 0.19
% 3.22/1.54  CNF conversion       : 0.03
% 3.22/1.54  Main loop            : 0.36
% 3.22/1.54  Inferencing          : 0.11
% 3.22/1.54  Reduction            : 0.15
% 3.22/1.54  Demodulation         : 0.12
% 3.22/1.54  BG Simplification    : 0.02
% 3.22/1.54  Subsumption          : 0.06
% 3.22/1.54  Abstraction          : 0.02
% 3.22/1.54  MUC search           : 0.00
% 3.22/1.54  Cooper               : 0.00
% 3.22/1.54  Total                : 0.75
% 3.22/1.54  Index Insertion      : 0.00
% 3.22/1.54  Index Deletion       : 0.00
% 3.22/1.54  Index Matching       : 0.00
% 3.22/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
