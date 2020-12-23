%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:19 EST 2020

% Result     : Theorem 26.66s
% Output     : CNFRefutation 26.69s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 120 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 223 expanded)
%              Number of equality atoms :   43 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_177,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(A_72,B_73)
      | ~ r2_hidden(A_72,k4_xboole_0(B_73,k1_tarski(C_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5731,plain,(
    ! [B_10806,C_10807,B_10808] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_10806,k1_tarski(C_10807)),B_10808),B_10806)
      | r1_tarski(k4_xboole_0(B_10806,k1_tarski(C_10807)),B_10808) ) ),
    inference(resolution,[status(thm)],[c_6,c_177])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5853,plain,(
    ! [B_10899,C_10900] : r1_tarski(k4_xboole_0(B_10899,k1_tarski(C_10900)),B_10899) ),
    inference(resolution,[status(thm)],[c_5731,c_4])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( k1_tarski(B_21) = A_20
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6138,plain,(
    ! [B_11359,C_11360] :
      ( k4_xboole_0(k1_tarski(B_11359),k1_tarski(C_11360)) = k1_tarski(B_11359)
      | k4_xboole_0(k1_tarski(B_11359),k1_tarski(C_11360)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5853,c_38])).

tff(c_44,plain,(
    ! [B_23] : k4_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) != k1_tarski(B_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6316,plain,(
    ! [C_11360] : k4_xboole_0(k1_tarski(C_11360),k1_tarski(C_11360)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6138,c_44])).

tff(c_6320,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6316,c_44])).

tff(c_32,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_435,plain,(
    ! [A_108,C_109] :
      ( r2_hidden('#skF_4'(A_108,k1_setfam_1(A_108),C_109),A_108)
      | r2_hidden(C_109,k1_setfam_1(A_108))
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [D_13,B_9,A_8] :
      ( D_13 = B_9
      | D_13 = A_8
      | ~ r2_hidden(D_13,k2_tarski(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_469,plain,(
    ! [A_8,B_9,C_109] :
      ( '#skF_4'(k2_tarski(A_8,B_9),k1_setfam_1(k2_tarski(A_8,B_9)),C_109) = B_9
      | '#skF_4'(k2_tarski(A_8,B_9),k1_setfam_1(k2_tarski(A_8,B_9)),C_109) = A_8
      | r2_hidden(C_109,k1_setfam_1(k2_tarski(A_8,B_9)))
      | k2_tarski(A_8,B_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_435,c_14])).

tff(c_117718,plain,(
    ! [C_109,B_9] :
      ( r2_hidden(C_109,k1_setfam_1(k2_tarski(B_9,B_9)))
      | k2_tarski(B_9,B_9) = k1_xboole_0
      | '#skF_4'(k2_tarski(B_9,B_9),k1_setfam_1(k2_tarski(B_9,B_9)),C_109) = B_9 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_469])).

tff(c_117722,plain,(
    ! [C_109,B_9] :
      ( r2_hidden(C_109,k1_setfam_1(k1_tarski(B_9)))
      | k1_tarski(B_9) = k1_xboole_0
      | '#skF_4'(k1_tarski(B_9),k1_setfam_1(k1_tarski(B_9)),C_109) = B_9 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_32,c_32,c_117718])).

tff(c_118385,plain,(
    ! [C_116765,B_116766] :
      ( r2_hidden(C_116765,k1_setfam_1(k1_tarski(B_116766)))
      | '#skF_4'(k1_tarski(B_116766),k1_setfam_1(k1_tarski(B_116766)),C_116765) = B_116766 ) ),
    inference(negUnitSimplification,[status(thm)],[c_6320,c_117722])).

tff(c_68,plain,(
    ! [C_39,A_27] :
      ( ~ r2_hidden(C_39,'#skF_4'(A_27,k1_setfam_1(A_27),C_39))
      | r2_hidden(C_39,k1_setfam_1(A_27))
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_118404,plain,(
    ! [C_116765,B_116766] :
      ( ~ r2_hidden(C_116765,B_116766)
      | r2_hidden(C_116765,k1_setfam_1(k1_tarski(B_116766)))
      | k1_tarski(B_116766) = k1_xboole_0
      | r2_hidden(C_116765,k1_setfam_1(k1_tarski(B_116766))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118385,c_68])).

tff(c_118722,plain,(
    ! [C_116765,B_116766] :
      ( ~ r2_hidden(C_116765,B_116766)
      | r2_hidden(C_116765,k1_setfam_1(k1_tarski(B_116766)))
      | r2_hidden(C_116765,k1_setfam_1(k1_tarski(B_116766))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6320,c_118404])).

tff(c_119633,plain,(
    ! [C_117493,B_117494] :
      ( ~ r2_hidden(C_117493,B_117494)
      | r2_hidden(C_117493,k1_setfam_1(k1_tarski(B_117494))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_118722])).

tff(c_133402,plain,(
    ! [A_126435,B_126436] :
      ( r1_tarski(A_126435,k1_setfam_1(k1_tarski(B_126436)))
      | ~ r2_hidden('#skF_1'(A_126435,k1_setfam_1(k1_tarski(B_126436))),B_126436) ) ),
    inference(resolution,[status(thm)],[c_119633,c_4])).

tff(c_133677,plain,(
    ! [A_1] : r1_tarski(A_1,k1_setfam_1(k1_tarski(A_1))) ),
    inference(resolution,[status(thm)],[c_6,c_133402])).

tff(c_95,plain,(
    ! [D_49,B_50] : r2_hidden(D_49,k2_tarski(D_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_95])).

tff(c_336,plain,(
    ! [C_100,D_101,A_102] :
      ( r2_hidden(C_100,D_101)
      | ~ r2_hidden(D_101,A_102)
      | ~ r2_hidden(C_100,k1_setfam_1(A_102))
      | k1_xboole_0 = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_350,plain,(
    ! [C_100,A_14] :
      ( r2_hidden(C_100,A_14)
      | ~ r2_hidden(C_100,k1_setfam_1(k1_tarski(A_14)))
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_98,c_336])).

tff(c_6472,plain,(
    ! [C_11633,A_11634] :
      ( r2_hidden(C_11633,A_11634)
      | ~ r2_hidden(C_11633,k1_setfam_1(k1_tarski(A_11634))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6320,c_350])).

tff(c_6976,plain,(
    ! [A_12095,B_12096] :
      ( r2_hidden('#skF_1'(k1_setfam_1(k1_tarski(A_12095)),B_12096),A_12095)
      | r1_tarski(k1_setfam_1(k1_tarski(A_12095)),B_12096) ) ),
    inference(resolution,[status(thm)],[c_6,c_6472])).

tff(c_7092,plain,(
    ! [A_12187] : r1_tarski(k1_setfam_1(k1_tarski(A_12187)),A_12187) ),
    inference(resolution,[status(thm)],[c_6976,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7160,plain,(
    ! [A_12187] :
      ( k1_setfam_1(k1_tarski(A_12187)) = A_12187
      | ~ r1_tarski(A_12187,k1_setfam_1(k1_tarski(A_12187))) ) ),
    inference(resolution,[status(thm)],[c_7092,c_8])).

tff(c_133679,plain,(
    ! [A_12187] : k1_setfam_1(k1_tarski(A_12187)) = A_12187 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133677,c_7160])).

tff(c_76,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_134184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133679,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n021.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 17:20:19 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.66/17.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.69/17.03  
% 26.69/17.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.69/17.03  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5
% 26.69/17.03  
% 26.69/17.03  %Foreground sorts:
% 26.69/17.03  
% 26.69/17.03  
% 26.69/17.03  %Background operators:
% 26.69/17.03  
% 26.69/17.03  
% 26.69/17.03  %Foreground operators:
% 26.69/17.03  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 26.69/17.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.69/17.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.69/17.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 26.69/17.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.69/17.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.69/17.03  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 26.69/17.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.69/17.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 26.69/17.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.69/17.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 26.69/17.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.69/17.03  tff('#skF_8', type, '#skF_8': $i).
% 26.69/17.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.69/17.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 26.69/17.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.69/17.03  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 26.69/17.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 26.69/17.03  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 26.69/17.03  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 26.69/17.03  
% 26.69/17.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 26.69/17.05  tff(f_71, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 26.69/17.05  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 26.69/17.05  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 26.69/17.05  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 26.69/17.05  tff(f_90, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 26.69/17.05  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 26.69/17.05  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 26.69/17.05  tff(f_93, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 26.69/17.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.69/17.05  tff(c_177, plain, (![A_72, B_73, C_74]: (r2_hidden(A_72, B_73) | ~r2_hidden(A_72, k4_xboole_0(B_73, k1_tarski(C_74))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 26.69/17.05  tff(c_5731, plain, (![B_10806, C_10807, B_10808]: (r2_hidden('#skF_1'(k4_xboole_0(B_10806, k1_tarski(C_10807)), B_10808), B_10806) | r1_tarski(k4_xboole_0(B_10806, k1_tarski(C_10807)), B_10808))), inference(resolution, [status(thm)], [c_6, c_177])).
% 26.69/17.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.69/17.05  tff(c_5853, plain, (![B_10899, C_10900]: (r1_tarski(k4_xboole_0(B_10899, k1_tarski(C_10900)), B_10899))), inference(resolution, [status(thm)], [c_5731, c_4])).
% 26.69/17.05  tff(c_38, plain, (![B_21, A_20]: (k1_tarski(B_21)=A_20 | k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 26.69/17.05  tff(c_6138, plain, (![B_11359, C_11360]: (k4_xboole_0(k1_tarski(B_11359), k1_tarski(C_11360))=k1_tarski(B_11359) | k4_xboole_0(k1_tarski(B_11359), k1_tarski(C_11360))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5853, c_38])).
% 26.69/17.05  tff(c_44, plain, (![B_23]: (k4_xboole_0(k1_tarski(B_23), k1_tarski(B_23))!=k1_tarski(B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 26.69/17.05  tff(c_6316, plain, (![C_11360]: (k4_xboole_0(k1_tarski(C_11360), k1_tarski(C_11360))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6138, c_44])).
% 26.69/17.05  tff(c_6320, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6316, c_44])).
% 26.69/17.05  tff(c_32, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.69/17.05  tff(c_435, plain, (![A_108, C_109]: (r2_hidden('#skF_4'(A_108, k1_setfam_1(A_108), C_109), A_108) | r2_hidden(C_109, k1_setfam_1(A_108)) | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_90])).
% 26.69/17.05  tff(c_14, plain, (![D_13, B_9, A_8]: (D_13=B_9 | D_13=A_8 | ~r2_hidden(D_13, k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 26.69/17.05  tff(c_469, plain, (![A_8, B_9, C_109]: ('#skF_4'(k2_tarski(A_8, B_9), k1_setfam_1(k2_tarski(A_8, B_9)), C_109)=B_9 | '#skF_4'(k2_tarski(A_8, B_9), k1_setfam_1(k2_tarski(A_8, B_9)), C_109)=A_8 | r2_hidden(C_109, k1_setfam_1(k2_tarski(A_8, B_9))) | k2_tarski(A_8, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_435, c_14])).
% 26.69/17.05  tff(c_117718, plain, (![C_109, B_9]: (r2_hidden(C_109, k1_setfam_1(k2_tarski(B_9, B_9))) | k2_tarski(B_9, B_9)=k1_xboole_0 | '#skF_4'(k2_tarski(B_9, B_9), k1_setfam_1(k2_tarski(B_9, B_9)), C_109)=B_9)), inference(factorization, [status(thm), theory('equality')], [c_469])).
% 26.69/17.05  tff(c_117722, plain, (![C_109, B_9]: (r2_hidden(C_109, k1_setfam_1(k1_tarski(B_9))) | k1_tarski(B_9)=k1_xboole_0 | '#skF_4'(k1_tarski(B_9), k1_setfam_1(k1_tarski(B_9)), C_109)=B_9)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_32, c_32, c_117718])).
% 26.69/17.05  tff(c_118385, plain, (![C_116765, B_116766]: (r2_hidden(C_116765, k1_setfam_1(k1_tarski(B_116766))) | '#skF_4'(k1_tarski(B_116766), k1_setfam_1(k1_tarski(B_116766)), C_116765)=B_116766)), inference(negUnitSimplification, [status(thm)], [c_6320, c_117722])).
% 26.69/17.05  tff(c_68, plain, (![C_39, A_27]: (~r2_hidden(C_39, '#skF_4'(A_27, k1_setfam_1(A_27), C_39)) | r2_hidden(C_39, k1_setfam_1(A_27)) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_90])).
% 26.69/17.05  tff(c_118404, plain, (![C_116765, B_116766]: (~r2_hidden(C_116765, B_116766) | r2_hidden(C_116765, k1_setfam_1(k1_tarski(B_116766))) | k1_tarski(B_116766)=k1_xboole_0 | r2_hidden(C_116765, k1_setfam_1(k1_tarski(B_116766))))), inference(superposition, [status(thm), theory('equality')], [c_118385, c_68])).
% 26.69/17.05  tff(c_118722, plain, (![C_116765, B_116766]: (~r2_hidden(C_116765, B_116766) | r2_hidden(C_116765, k1_setfam_1(k1_tarski(B_116766))) | r2_hidden(C_116765, k1_setfam_1(k1_tarski(B_116766))))), inference(negUnitSimplification, [status(thm)], [c_6320, c_118404])).
% 26.69/17.05  tff(c_119633, plain, (![C_117493, B_117494]: (~r2_hidden(C_117493, B_117494) | r2_hidden(C_117493, k1_setfam_1(k1_tarski(B_117494))))), inference(factorization, [status(thm), theory('equality')], [c_118722])).
% 26.69/17.05  tff(c_133402, plain, (![A_126435, B_126436]: (r1_tarski(A_126435, k1_setfam_1(k1_tarski(B_126436))) | ~r2_hidden('#skF_1'(A_126435, k1_setfam_1(k1_tarski(B_126436))), B_126436))), inference(resolution, [status(thm)], [c_119633, c_4])).
% 26.69/17.05  tff(c_133677, plain, (![A_1]: (r1_tarski(A_1, k1_setfam_1(k1_tarski(A_1))))), inference(resolution, [status(thm)], [c_6, c_133402])).
% 26.69/17.05  tff(c_95, plain, (![D_49, B_50]: (r2_hidden(D_49, k2_tarski(D_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 26.69/17.05  tff(c_98, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_95])).
% 26.69/17.05  tff(c_336, plain, (![C_100, D_101, A_102]: (r2_hidden(C_100, D_101) | ~r2_hidden(D_101, A_102) | ~r2_hidden(C_100, k1_setfam_1(A_102)) | k1_xboole_0=A_102)), inference(cnfTransformation, [status(thm)], [f_90])).
% 26.69/17.05  tff(c_350, plain, (![C_100, A_14]: (r2_hidden(C_100, A_14) | ~r2_hidden(C_100, k1_setfam_1(k1_tarski(A_14))) | k1_tarski(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_98, c_336])).
% 26.69/17.05  tff(c_6472, plain, (![C_11633, A_11634]: (r2_hidden(C_11633, A_11634) | ~r2_hidden(C_11633, k1_setfam_1(k1_tarski(A_11634))))), inference(negUnitSimplification, [status(thm)], [c_6320, c_350])).
% 26.69/17.05  tff(c_6976, plain, (![A_12095, B_12096]: (r2_hidden('#skF_1'(k1_setfam_1(k1_tarski(A_12095)), B_12096), A_12095) | r1_tarski(k1_setfam_1(k1_tarski(A_12095)), B_12096))), inference(resolution, [status(thm)], [c_6, c_6472])).
% 26.69/17.05  tff(c_7092, plain, (![A_12187]: (r1_tarski(k1_setfam_1(k1_tarski(A_12187)), A_12187))), inference(resolution, [status(thm)], [c_6976, c_4])).
% 26.69/17.05  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 26.69/17.05  tff(c_7160, plain, (![A_12187]: (k1_setfam_1(k1_tarski(A_12187))=A_12187 | ~r1_tarski(A_12187, k1_setfam_1(k1_tarski(A_12187))))), inference(resolution, [status(thm)], [c_7092, c_8])).
% 26.69/17.05  tff(c_133679, plain, (![A_12187]: (k1_setfam_1(k1_tarski(A_12187))=A_12187)), inference(demodulation, [status(thm), theory('equality')], [c_133677, c_7160])).
% 26.69/17.05  tff(c_76, plain, (k1_setfam_1(k1_tarski('#skF_8'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_93])).
% 26.69/17.05  tff(c_134184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133679, c_76])).
% 26.69/17.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.69/17.05  
% 26.69/17.05  Inference rules
% 26.69/17.05  ----------------------
% 26.69/17.05  #Ref     : 0
% 26.69/17.05  #Sup     : 26046
% 26.69/17.05  #Fact    : 86
% 26.69/17.05  #Define  : 0
% 26.69/17.05  #Split   : 16
% 26.69/17.05  #Chain   : 0
% 26.69/17.05  #Close   : 0
% 26.69/17.05  
% 26.69/17.05  Ordering : KBO
% 26.69/17.05  
% 26.69/17.05  Simplification rules
% 26.69/17.05  ----------------------
% 26.69/17.05  #Subsume      : 11040
% 26.69/17.05  #Demod        : 4214
% 26.69/17.05  #Tautology    : 2691
% 26.69/17.05  #SimpNegUnit  : 1752
% 26.69/17.05  #BackRed      : 130
% 26.69/17.05  
% 26.69/17.05  #Partial instantiations: 62220
% 26.69/17.05  #Strategies tried      : 1
% 26.69/17.05  
% 26.69/17.05  Timing (in seconds)
% 26.69/17.05  ----------------------
% 26.69/17.05  Preprocessing        : 0.33
% 26.69/17.05  Parsing              : 0.16
% 26.69/17.05  CNF conversion       : 0.03
% 26.69/17.05  Main loop            : 16.05
% 26.69/17.05  Inferencing          : 3.51
% 26.69/17.05  Reduction            : 3.55
% 26.69/17.05  Demodulation         : 2.26
% 26.69/17.05  BG Simplification    : 0.36
% 26.69/17.05  Subsumption          : 7.66
% 26.69/17.05  Abstraction          : 0.62
% 26.69/17.05  MUC search           : 0.00
% 26.69/17.05  Cooper               : 0.00
% 26.69/17.05  Total                : 16.41
% 26.69/17.05  Index Insertion      : 0.00
% 26.69/17.05  Index Deletion       : 0.00
% 26.69/17.05  Index Matching       : 0.00
% 26.69/17.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
