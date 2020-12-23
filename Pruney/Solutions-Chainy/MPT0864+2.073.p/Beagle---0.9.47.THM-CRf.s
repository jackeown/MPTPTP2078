%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:18 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 153 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 204 expanded)
%              Number of equality atoms :   65 ( 172 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_383,plain,(
    ! [A_85,B_86] : k4_xboole_0(A_85,k2_xboole_0(A_85,B_86)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_390,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_383])).

tff(c_20,plain,(
    ! [B_22] : k4_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) != k1_tarski(B_22) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_453,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_20])).

tff(c_34,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_508,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(k1_tarski(A_105),k1_tarski(B_106)) = k1_tarski(A_105)
      | B_106 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [B_24,A_23] :
      ( ~ r2_hidden(B_24,A_23)
      | k4_xboole_0(A_23,k1_tarski(B_24)) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_551,plain,(
    ! [B_110,A_111] :
      ( ~ r2_hidden(B_110,k1_tarski(A_111))
      | B_110 = A_111 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_24])).

tff(c_558,plain,(
    ! [A_111] :
      ( '#skF_1'(k1_tarski(A_111)) = A_111
      | k1_tarski(A_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_551])).

tff(c_563,plain,(
    ! [A_111] : '#skF_1'(k1_tarski(A_111)) = A_111 ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_558])).

tff(c_455,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,k1_tarski(B_98)) = A_97
      | r2_hidden(B_98,A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_462,plain,(
    ! [B_98] :
      ( k1_tarski(B_98) = k1_xboole_0
      | r2_hidden(B_98,k1_tarski(B_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_390])).

tff(c_471,plain,(
    ! [B_98] : r2_hidden(B_98,k1_tarski(B_98)) ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_462])).

tff(c_578,plain,(
    ! [D_113,A_114,C_115] :
      ( ~ r2_hidden(D_113,A_114)
      | k4_tarski(C_115,D_113) != '#skF_1'(A_114)
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_580,plain,(
    ! [C_115,B_98] :
      ( k4_tarski(C_115,B_98) != '#skF_1'(k1_tarski(B_98))
      | k1_tarski(B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_471,c_578])).

tff(c_584,plain,(
    ! [C_115,B_98] :
      ( k4_tarski(C_115,B_98) != B_98
      | k1_tarski(B_98) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_580])).

tff(c_585,plain,(
    ! [C_115,B_98] : k4_tarski(C_115,B_98) != B_98 ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_584])).

tff(c_136,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(A_49,B_50)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_206,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_20])).

tff(c_268,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(k1_tarski(A_72),k1_tarski(B_73)) = k1_tarski(A_72)
      | B_73 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_302,plain,(
    ! [B_74,A_75] :
      ( ~ r2_hidden(B_74,k1_tarski(A_75))
      | B_74 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_24])).

tff(c_309,plain,(
    ! [A_75] :
      ( '#skF_1'(k1_tarski(A_75)) = A_75
      | k1_tarski(A_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_302])).

tff(c_314,plain,(
    ! [A_75] : '#skF_1'(k1_tarski(A_75)) = A_75 ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_309])).

tff(c_228,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,k1_tarski(B_65)) = A_64
      | r2_hidden(B_65,A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_235,plain,(
    ! [B_65] :
      ( k1_tarski(B_65) = k1_xboole_0
      | r2_hidden(B_65,k1_tarski(B_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_143])).

tff(c_244,plain,(
    ! [B_65] : r2_hidden(B_65,k1_tarski(B_65)) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_235])).

tff(c_342,plain,(
    ! [C_82,A_83,D_84] :
      ( ~ r2_hidden(C_82,A_83)
      | k4_tarski(C_82,D_84) != '#skF_1'(A_83)
      | k1_xboole_0 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_344,plain,(
    ! [B_65,D_84] :
      ( k4_tarski(B_65,D_84) != '#skF_1'(k1_tarski(B_65))
      | k1_tarski(B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_244,c_342])).

tff(c_348,plain,(
    ! [B_65,D_84] :
      ( k4_tarski(B_65,D_84) != B_65
      | k1_tarski(B_65) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_344])).

tff(c_349,plain,(
    ! [B_65,D_84] : k4_tarski(B_65,D_84) != B_65 ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_348])).

tff(c_42,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_86,plain,(
    ! [A_46,B_47] : k1_mcart_1(k4_tarski(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_74,plain,(
    ! [A_44,B_45] : k2_mcart_1(k4_tarski(A_44,B_45)) = B_45 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_107,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_83,c_40])).

tff(c_108,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_111,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_42])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_111])).

tff(c_353,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_357,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_42])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.23/1.30  
% 2.23/1.30  %Foreground sorts:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Background operators:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Foreground operators:
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.23/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.23/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.30  
% 2.53/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.53/1.31  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.53/1.31  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.53/1.31  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.53/1.31  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.53/1.31  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.53/1.31  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.53/1.31  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.31  tff(c_383, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k2_xboole_0(A_85, B_86))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.31  tff(c_390, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_383])).
% 2.53/1.31  tff(c_20, plain, (![B_22]: (k4_xboole_0(k1_tarski(B_22), k1_tarski(B_22))!=k1_tarski(B_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.53/1.31  tff(c_453, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_390, c_20])).
% 2.53/1.31  tff(c_34, plain, (![A_29]: (r2_hidden('#skF_1'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.31  tff(c_508, plain, (![A_105, B_106]: (k4_xboole_0(k1_tarski(A_105), k1_tarski(B_106))=k1_tarski(A_105) | B_106=A_105)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.53/1.31  tff(c_24, plain, (![B_24, A_23]: (~r2_hidden(B_24, A_23) | k4_xboole_0(A_23, k1_tarski(B_24))!=A_23)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.31  tff(c_551, plain, (![B_110, A_111]: (~r2_hidden(B_110, k1_tarski(A_111)) | B_110=A_111)), inference(superposition, [status(thm), theory('equality')], [c_508, c_24])).
% 2.53/1.31  tff(c_558, plain, (![A_111]: ('#skF_1'(k1_tarski(A_111))=A_111 | k1_tarski(A_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_551])).
% 2.53/1.31  tff(c_563, plain, (![A_111]: ('#skF_1'(k1_tarski(A_111))=A_111)), inference(negUnitSimplification, [status(thm)], [c_453, c_558])).
% 2.53/1.31  tff(c_455, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k1_tarski(B_98))=A_97 | r2_hidden(B_98, A_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.31  tff(c_462, plain, (![B_98]: (k1_tarski(B_98)=k1_xboole_0 | r2_hidden(B_98, k1_tarski(B_98)))), inference(superposition, [status(thm), theory('equality')], [c_455, c_390])).
% 2.53/1.31  tff(c_471, plain, (![B_98]: (r2_hidden(B_98, k1_tarski(B_98)))), inference(negUnitSimplification, [status(thm)], [c_453, c_462])).
% 2.53/1.31  tff(c_578, plain, (![D_113, A_114, C_115]: (~r2_hidden(D_113, A_114) | k4_tarski(C_115, D_113)!='#skF_1'(A_114) | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.31  tff(c_580, plain, (![C_115, B_98]: (k4_tarski(C_115, B_98)!='#skF_1'(k1_tarski(B_98)) | k1_tarski(B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_471, c_578])).
% 2.53/1.31  tff(c_584, plain, (![C_115, B_98]: (k4_tarski(C_115, B_98)!=B_98 | k1_tarski(B_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_563, c_580])).
% 2.53/1.31  tff(c_585, plain, (![C_115, B_98]: (k4_tarski(C_115, B_98)!=B_98)), inference(negUnitSimplification, [status(thm)], [c_453, c_584])).
% 2.53/1.31  tff(c_136, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(A_49, B_50))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.31  tff(c_143, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 2.53/1.31  tff(c_206, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_20])).
% 2.53/1.31  tff(c_268, plain, (![A_72, B_73]: (k4_xboole_0(k1_tarski(A_72), k1_tarski(B_73))=k1_tarski(A_72) | B_73=A_72)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.53/1.31  tff(c_302, plain, (![B_74, A_75]: (~r2_hidden(B_74, k1_tarski(A_75)) | B_74=A_75)), inference(superposition, [status(thm), theory('equality')], [c_268, c_24])).
% 2.53/1.31  tff(c_309, plain, (![A_75]: ('#skF_1'(k1_tarski(A_75))=A_75 | k1_tarski(A_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_302])).
% 2.53/1.31  tff(c_314, plain, (![A_75]: ('#skF_1'(k1_tarski(A_75))=A_75)), inference(negUnitSimplification, [status(thm)], [c_206, c_309])).
% 2.53/1.31  tff(c_228, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k1_tarski(B_65))=A_64 | r2_hidden(B_65, A_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.31  tff(c_235, plain, (![B_65]: (k1_tarski(B_65)=k1_xboole_0 | r2_hidden(B_65, k1_tarski(B_65)))), inference(superposition, [status(thm), theory('equality')], [c_228, c_143])).
% 2.53/1.31  tff(c_244, plain, (![B_65]: (r2_hidden(B_65, k1_tarski(B_65)))), inference(negUnitSimplification, [status(thm)], [c_206, c_235])).
% 2.53/1.31  tff(c_342, plain, (![C_82, A_83, D_84]: (~r2_hidden(C_82, A_83) | k4_tarski(C_82, D_84)!='#skF_1'(A_83) | k1_xboole_0=A_83)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.31  tff(c_344, plain, (![B_65, D_84]: (k4_tarski(B_65, D_84)!='#skF_1'(k1_tarski(B_65)) | k1_tarski(B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_244, c_342])).
% 2.53/1.31  tff(c_348, plain, (![B_65, D_84]: (k4_tarski(B_65, D_84)!=B_65 | k1_tarski(B_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_314, c_344])).
% 2.53/1.31  tff(c_349, plain, (![B_65, D_84]: (k4_tarski(B_65, D_84)!=B_65)), inference(negUnitSimplification, [status(thm)], [c_206, c_348])).
% 2.53/1.31  tff(c_42, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.31  tff(c_86, plain, (![A_46, B_47]: (k1_mcart_1(k4_tarski(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.31  tff(c_95, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_42, c_86])).
% 2.53/1.31  tff(c_74, plain, (![A_44, B_45]: (k2_mcart_1(k4_tarski(A_44, B_45))=B_45)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.31  tff(c_83, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_42, c_74])).
% 2.53/1.31  tff(c_40, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.31  tff(c_107, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_83, c_40])).
% 2.53/1.31  tff(c_108, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_107])).
% 2.53/1.31  tff(c_111, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_42])).
% 2.53/1.31  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_349, c_111])).
% 2.53/1.31  tff(c_353, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_107])).
% 2.53/1.31  tff(c_357, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_42])).
% 2.53/1.31  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_585, c_357])).
% 2.53/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.31  
% 2.53/1.31  Inference rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Ref     : 0
% 2.53/1.31  #Sup     : 129
% 2.53/1.31  #Fact    : 0
% 2.53/1.31  #Define  : 0
% 2.53/1.31  #Split   : 1
% 2.53/1.31  #Chain   : 0
% 2.53/1.31  #Close   : 0
% 2.53/1.31  
% 2.53/1.31  Ordering : KBO
% 2.53/1.31  
% 2.53/1.31  Simplification rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Subsume      : 2
% 2.53/1.31  #Demod        : 29
% 2.53/1.31  #Tautology    : 104
% 2.53/1.31  #SimpNegUnit  : 17
% 2.53/1.31  #BackRed      : 8
% 2.53/1.31  
% 2.53/1.31  #Partial instantiations: 0
% 2.53/1.31  #Strategies tried      : 1
% 2.53/1.31  
% 2.53/1.31  Timing (in seconds)
% 2.53/1.31  ----------------------
% 2.53/1.31  Preprocessing        : 0.31
% 2.53/1.31  Parsing              : 0.16
% 2.53/1.31  CNF conversion       : 0.02
% 2.53/1.32  Main loop            : 0.23
% 2.53/1.32  Inferencing          : 0.09
% 2.53/1.32  Reduction            : 0.07
% 2.53/1.32  Demodulation         : 0.05
% 2.53/1.32  BG Simplification    : 0.01
% 2.53/1.32  Subsumption          : 0.03
% 2.53/1.32  Abstraction          : 0.02
% 2.53/1.32  MUC search           : 0.00
% 2.53/1.32  Cooper               : 0.00
% 2.53/1.32  Total                : 0.58
% 2.53/1.32  Index Insertion      : 0.00
% 2.53/1.32  Index Deletion       : 0.00
% 2.53/1.32  Index Matching       : 0.00
% 2.53/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
