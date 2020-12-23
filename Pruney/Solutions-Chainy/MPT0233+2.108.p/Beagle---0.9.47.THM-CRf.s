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
% DateTime   : Thu Dec  3 09:49:35 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   79 (  95 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 116 expanded)
%              Number of equality atoms :   49 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_80,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_78,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_122,plain,(
    ! [B_74,C_75] : r1_tarski(k1_xboole_0,k2_tarski(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_124,plain,(
    ! [A_29] : r1_tarski(k1_xboole_0,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_122])).

tff(c_171,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_194,plain,(
    ! [A_29] : k3_xboole_0(k1_xboole_0,k1_tarski(A_29)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_171])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_265,plain,(
    ! [A_98,B_99] : k4_xboole_0(A_98,k4_xboole_0(A_98,B_99)) = k3_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_280,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_265])).

tff(c_74,plain,(
    ! [B_64] : k4_xboole_0(k1_tarski(B_64),k1_tarski(B_64)) != k1_tarski(B_64) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_295,plain,(
    ! [B_64] : k3_xboole_0(k1_tarski(B_64),k1_xboole_0) != k1_tarski(B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_74])).

tff(c_296,plain,(
    ! [B_64] : k1_tarski(B_64) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_2,c_295])).

tff(c_70,plain,(
    ! [B_61,C_62] : r1_tarski(k1_tarski(B_61),k2_tarski(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_82,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_196,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_171])).

tff(c_400,plain,(
    ! [A_109,B_110,C_111] :
      ( r1_tarski(A_109,B_110)
      | ~ r1_tarski(A_109,k3_xboole_0(B_110,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_723,plain,(
    ! [A_129,B_130,A_131] :
      ( r1_tarski(A_129,B_130)
      | ~ r1_tarski(A_129,k3_xboole_0(A_131,B_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_400])).

tff(c_821,plain,(
    ! [A_141] :
      ( r1_tarski(A_141,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_141,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_723])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2486,plain,(
    ! [A_233] :
      ( k3_xboole_0(A_233,k2_tarski('#skF_7','#skF_8')) = A_233
      | ~ r1_tarski(A_233,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_821,c_16])).

tff(c_2516,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_2486])).

tff(c_22,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_241,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,k3_xboole_0(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_395,plain,(
    ! [A_107,B_108] :
      ( ~ r1_xboole_0(A_107,B_108)
      | k3_xboole_0(A_107,B_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_241])).

tff(c_399,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_395])).

tff(c_420,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_280])).

tff(c_60,plain,(
    ! [B_58,C_59] :
      ( k4_xboole_0(k2_tarski(B_58,B_58),C_59) = k1_tarski(B_58)
      | r2_hidden(B_58,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_998,plain,(
    ! [B_154,C_155] :
      ( k4_xboole_0(k1_tarski(B_154),C_155) = k1_tarski(B_154)
      | r2_hidden(B_154,C_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1020,plain,(
    ! [B_154,C_155] :
      ( k4_xboole_0(k1_tarski(B_154),k1_tarski(B_154)) = k3_xboole_0(k1_tarski(B_154),C_155)
      | r2_hidden(B_154,C_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_20])).

tff(c_1061,plain,(
    ! [B_154,C_155] :
      ( k3_xboole_0(k1_tarski(B_154),C_155) = k1_xboole_0
      | r2_hidden(B_154,C_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_1020])).

tff(c_2871,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2516,c_1061])).

tff(c_2904,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_2871])).

tff(c_24,plain,(
    ! [D_28,B_24,A_23] :
      ( D_28 = B_24
      | D_28 = A_23
      | ~ r2_hidden(D_28,k2_tarski(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2910,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2904,c_24])).

tff(c_2914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_2910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.87  
% 4.36/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 4.36/1.87  
% 4.36/1.87  %Foreground sorts:
% 4.36/1.87  
% 4.36/1.87  
% 4.36/1.87  %Background operators:
% 4.36/1.87  
% 4.36/1.87  
% 4.36/1.87  %Foreground operators:
% 4.36/1.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.36/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.36/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.36/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.36/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.36/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.36/1.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.36/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.36/1.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.36/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.36/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.36/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.36/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.36/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.36/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.36/1.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.87  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.36/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.36/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.36/1.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.36/1.87  
% 4.36/1.89  tff(f_129, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.36/1.89  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.36/1.89  tff(f_114, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.36/1.89  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.36/1.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.36/1.89  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.36/1.89  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.36/1.89  tff(f_119, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.36/1.89  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.36/1.89  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.36/1.89  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.36/1.89  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.36/1.89  tff(f_99, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 4.36/1.89  tff(f_76, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.36/1.89  tff(c_80, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.36/1.89  tff(c_78, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.36/1.89  tff(c_42, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.36/1.89  tff(c_122, plain, (![B_74, C_75]: (r1_tarski(k1_xboole_0, k2_tarski(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.36/1.89  tff(c_124, plain, (![A_29]: (r1_tarski(k1_xboole_0, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_122])).
% 4.36/1.89  tff(c_171, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.36/1.89  tff(c_194, plain, (![A_29]: (k3_xboole_0(k1_xboole_0, k1_tarski(A_29))=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_171])).
% 4.36/1.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.36/1.89  tff(c_18, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.36/1.89  tff(c_265, plain, (![A_98, B_99]: (k4_xboole_0(A_98, k4_xboole_0(A_98, B_99))=k3_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.36/1.89  tff(c_280, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_265])).
% 4.36/1.89  tff(c_74, plain, (![B_64]: (k4_xboole_0(k1_tarski(B_64), k1_tarski(B_64))!=k1_tarski(B_64))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.36/1.89  tff(c_295, plain, (![B_64]: (k3_xboole_0(k1_tarski(B_64), k1_xboole_0)!=k1_tarski(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_74])).
% 4.36/1.89  tff(c_296, plain, (![B_64]: (k1_tarski(B_64)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_2, c_295])).
% 4.36/1.89  tff(c_70, plain, (![B_61, C_62]: (r1_tarski(k1_tarski(B_61), k2_tarski(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.36/1.89  tff(c_82, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.36/1.89  tff(c_196, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_171])).
% 4.36/1.89  tff(c_400, plain, (![A_109, B_110, C_111]: (r1_tarski(A_109, B_110) | ~r1_tarski(A_109, k3_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.36/1.89  tff(c_723, plain, (![A_129, B_130, A_131]: (r1_tarski(A_129, B_130) | ~r1_tarski(A_129, k3_xboole_0(A_131, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_400])).
% 4.36/1.89  tff(c_821, plain, (![A_141]: (r1_tarski(A_141, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_141, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_196, c_723])).
% 4.36/1.89  tff(c_16, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.36/1.89  tff(c_2486, plain, (![A_233]: (k3_xboole_0(A_233, k2_tarski('#skF_7', '#skF_8'))=A_233 | ~r1_tarski(A_233, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_821, c_16])).
% 4.36/1.89  tff(c_2516, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_70, c_2486])).
% 4.36/1.89  tff(c_22, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.89  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.36/1.89  tff(c_241, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, k3_xboole_0(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.89  tff(c_395, plain, (![A_107, B_108]: (~r1_xboole_0(A_107, B_108) | k3_xboole_0(A_107, B_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_241])).
% 4.36/1.89  tff(c_399, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_395])).
% 4.36/1.89  tff(c_420, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_399, c_280])).
% 4.36/1.89  tff(c_60, plain, (![B_58, C_59]: (k4_xboole_0(k2_tarski(B_58, B_58), C_59)=k1_tarski(B_58) | r2_hidden(B_58, C_59))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.36/1.89  tff(c_998, plain, (![B_154, C_155]: (k4_xboole_0(k1_tarski(B_154), C_155)=k1_tarski(B_154) | r2_hidden(B_154, C_155))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60])).
% 4.36/1.89  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.36/1.89  tff(c_1020, plain, (![B_154, C_155]: (k4_xboole_0(k1_tarski(B_154), k1_tarski(B_154))=k3_xboole_0(k1_tarski(B_154), C_155) | r2_hidden(B_154, C_155))), inference(superposition, [status(thm), theory('equality')], [c_998, c_20])).
% 4.36/1.89  tff(c_1061, plain, (![B_154, C_155]: (k3_xboole_0(k1_tarski(B_154), C_155)=k1_xboole_0 | r2_hidden(B_154, C_155))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_1020])).
% 4.36/1.89  tff(c_2871, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2516, c_1061])).
% 4.36/1.89  tff(c_2904, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_296, c_2871])).
% 4.36/1.89  tff(c_24, plain, (![D_28, B_24, A_23]: (D_28=B_24 | D_28=A_23 | ~r2_hidden(D_28, k2_tarski(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.36/1.89  tff(c_2910, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_2904, c_24])).
% 4.36/1.89  tff(c_2914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_2910])).
% 4.36/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.89  
% 4.36/1.89  Inference rules
% 4.36/1.89  ----------------------
% 4.36/1.89  #Ref     : 0
% 4.36/1.89  #Sup     : 680
% 4.36/1.89  #Fact    : 0
% 4.36/1.89  #Define  : 0
% 4.36/1.89  #Split   : 3
% 4.36/1.89  #Chain   : 0
% 4.36/1.89  #Close   : 0
% 4.36/1.89  
% 4.36/1.89  Ordering : KBO
% 4.36/1.89  
% 4.36/1.89  Simplification rules
% 4.36/1.89  ----------------------
% 4.36/1.89  #Subsume      : 115
% 4.36/1.89  #Demod        : 430
% 4.36/1.89  #Tautology    : 332
% 4.36/1.89  #SimpNegUnit  : 59
% 4.36/1.89  #BackRed      : 31
% 4.36/1.89  
% 4.36/1.89  #Partial instantiations: 0
% 4.36/1.89  #Strategies tried      : 1
% 4.36/1.89  
% 4.36/1.89  Timing (in seconds)
% 4.36/1.89  ----------------------
% 4.36/1.89  Preprocessing        : 0.37
% 4.36/1.89  Parsing              : 0.19
% 4.36/1.89  CNF conversion       : 0.03
% 4.36/1.89  Main loop            : 0.70
% 4.36/1.89  Inferencing          : 0.23
% 4.36/1.89  Reduction            : 0.27
% 4.36/1.89  Demodulation         : 0.20
% 4.36/1.89  BG Simplification    : 0.03
% 4.36/1.89  Subsumption          : 0.12
% 4.36/1.89  Abstraction          : 0.03
% 4.36/1.89  MUC search           : 0.00
% 4.36/1.89  Cooper               : 0.00
% 4.36/1.89  Total                : 1.09
% 4.36/1.89  Index Insertion      : 0.00
% 4.36/1.89  Index Deletion       : 0.00
% 4.36/1.89  Index Matching       : 0.00
% 4.36/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
