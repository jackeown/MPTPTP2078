%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:13 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 132 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 172 expanded)
%              Number of equality atoms :   62 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_357,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_366,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_357])).

tff(c_369,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_366])).

tff(c_34,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_370,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_34])).

tff(c_44,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_3'(A_45),A_45)
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_300,plain,(
    ! [C_93,A_94] :
      ( C_93 = A_94
      | ~ r2_hidden(C_93,k1_tarski(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_308,plain,(
    ! [A_94] :
      ( '#skF_3'(k1_tarski(A_94)) = A_94
      | k1_tarski(A_94) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_300])).

tff(c_378,plain,(
    ! [A_94] : '#skF_3'(k1_tarski(A_94)) = A_94 ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_308])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_434,plain,(
    ! [D_115,A_116,C_117] :
      ( ~ r2_hidden(D_115,A_116)
      | k4_tarski(C_117,D_115) != '#skF_3'(A_116)
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_438,plain,(
    ! [C_117,C_10] :
      ( k4_tarski(C_117,C_10) != '#skF_3'(k1_tarski(C_10))
      | k1_tarski(C_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_434])).

tff(c_441,plain,(
    ! [C_117,C_10] :
      ( k4_tarski(C_117,C_10) != C_10
      | k1_tarski(C_10) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_438])).

tff(c_442,plain,(
    ! [C_117,C_10] : k4_tarski(C_117,C_10) != C_10 ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_441])).

tff(c_183,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_192,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_183])).

tff(c_195,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_192])).

tff(c_196,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_34])).

tff(c_145,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_3'(A_67),A_67)
      | k1_xboole_0 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_150,plain,(
    ! [A_6] :
      ( '#skF_3'(k1_tarski(A_6)) = A_6
      | k1_tarski(A_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_145,c_8])).

tff(c_205,plain,(
    ! [A_6] : '#skF_3'(k1_tarski(A_6)) = A_6 ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_150])).

tff(c_264,plain,(
    ! [C_89,A_90,D_91] :
      ( ~ r2_hidden(C_89,A_90)
      | k4_tarski(C_89,D_91) != '#skF_3'(A_90)
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_268,plain,(
    ! [C_10,D_91] :
      ( k4_tarski(C_10,D_91) != '#skF_3'(k1_tarski(C_10))
      | k1_tarski(C_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_264])).

tff(c_271,plain,(
    ! [C_10,D_91] :
      ( k4_tarski(C_10,D_91) != C_10
      | k1_tarski(C_10) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_268])).

tff(c_272,plain,(
    ! [C_10,D_91] : k4_tarski(C_10,D_91) != C_10 ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_271])).

tff(c_52,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    ! [A_63,B_64] : k1_mcart_1(k4_tarski(A_63,B_64)) = A_63 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_108,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_83,plain,(
    ! [A_61,B_62] : k2_mcart_1(k4_tarski(A_61,B_62)) = B_62 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_50,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_115,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_92,c_50])).

tff(c_116,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_118,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_52])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_118])).

tff(c_275,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_278,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_52])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.22/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.22/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.22/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.22/1.31  
% 2.22/1.33  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.22/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.22/1.33  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.22/1.33  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.22/1.33  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.22/1.33  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.22/1.33  tff(f_89, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.22/1.33  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.22/1.33  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.33  tff(c_357, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.33  tff(c_366, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_357])).
% 2.22/1.33  tff(c_369, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_366])).
% 2.22/1.33  tff(c_34, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.33  tff(c_370, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_34])).
% 2.22/1.33  tff(c_44, plain, (![A_45]: (r2_hidden('#skF_3'(A_45), A_45) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.33  tff(c_300, plain, (![C_93, A_94]: (C_93=A_94 | ~r2_hidden(C_93, k1_tarski(A_94)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.33  tff(c_308, plain, (![A_94]: ('#skF_3'(k1_tarski(A_94))=A_94 | k1_tarski(A_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_300])).
% 2.22/1.33  tff(c_378, plain, (![A_94]: ('#skF_3'(k1_tarski(A_94))=A_94)), inference(negUnitSimplification, [status(thm)], [c_370, c_308])).
% 2.22/1.33  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.33  tff(c_434, plain, (![D_115, A_116, C_117]: (~r2_hidden(D_115, A_116) | k4_tarski(C_117, D_115)!='#skF_3'(A_116) | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.33  tff(c_438, plain, (![C_117, C_10]: (k4_tarski(C_117, C_10)!='#skF_3'(k1_tarski(C_10)) | k1_tarski(C_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_434])).
% 2.22/1.33  tff(c_441, plain, (![C_117, C_10]: (k4_tarski(C_117, C_10)!=C_10 | k1_tarski(C_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_378, c_438])).
% 2.22/1.33  tff(c_442, plain, (![C_117, C_10]: (k4_tarski(C_117, C_10)!=C_10)), inference(negUnitSimplification, [status(thm)], [c_370, c_441])).
% 2.22/1.33  tff(c_183, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.33  tff(c_192, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_183])).
% 2.22/1.33  tff(c_195, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_192])).
% 2.22/1.33  tff(c_196, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_34])).
% 2.22/1.33  tff(c_145, plain, (![A_67]: (r2_hidden('#skF_3'(A_67), A_67) | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.33  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.33  tff(c_150, plain, (![A_6]: ('#skF_3'(k1_tarski(A_6))=A_6 | k1_tarski(A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_145, c_8])).
% 2.22/1.33  tff(c_205, plain, (![A_6]: ('#skF_3'(k1_tarski(A_6))=A_6)), inference(negUnitSimplification, [status(thm)], [c_196, c_150])).
% 2.22/1.33  tff(c_264, plain, (![C_89, A_90, D_91]: (~r2_hidden(C_89, A_90) | k4_tarski(C_89, D_91)!='#skF_3'(A_90) | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.33  tff(c_268, plain, (![C_10, D_91]: (k4_tarski(C_10, D_91)!='#skF_3'(k1_tarski(C_10)) | k1_tarski(C_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_264])).
% 2.22/1.33  tff(c_271, plain, (![C_10, D_91]: (k4_tarski(C_10, D_91)!=C_10 | k1_tarski(C_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_205, c_268])).
% 2.22/1.33  tff(c_272, plain, (![C_10, D_91]: (k4_tarski(C_10, D_91)!=C_10)), inference(negUnitSimplification, [status(thm)], [c_196, c_271])).
% 2.22/1.33  tff(c_52, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.33  tff(c_99, plain, (![A_63, B_64]: (k1_mcart_1(k4_tarski(A_63, B_64))=A_63)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.33  tff(c_108, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_52, c_99])).
% 2.22/1.33  tff(c_83, plain, (![A_61, B_62]: (k2_mcart_1(k4_tarski(A_61, B_62))=B_62)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.33  tff(c_92, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_52, c_83])).
% 2.22/1.33  tff(c_50, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.33  tff(c_115, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_92, c_50])).
% 2.22/1.33  tff(c_116, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_115])).
% 2.22/1.33  tff(c_118, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_52])).
% 2.22/1.33  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_118])).
% 2.22/1.33  tff(c_275, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 2.22/1.33  tff(c_278, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_52])).
% 2.22/1.33  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_278])).
% 2.22/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.33  
% 2.22/1.33  Inference rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Ref     : 0
% 2.22/1.33  #Sup     : 93
% 2.22/1.33  #Fact    : 0
% 2.22/1.33  #Define  : 0
% 2.22/1.33  #Split   : 1
% 2.22/1.33  #Chain   : 0
% 2.22/1.33  #Close   : 0
% 2.22/1.33  
% 2.22/1.33  Ordering : KBO
% 2.22/1.33  
% 2.22/1.33  Simplification rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Subsume      : 2
% 2.22/1.33  #Demod        : 23
% 2.22/1.33  #Tautology    : 75
% 2.22/1.33  #SimpNegUnit  : 14
% 2.22/1.33  #BackRed      : 9
% 2.22/1.33  
% 2.22/1.33  #Partial instantiations: 0
% 2.22/1.33  #Strategies tried      : 1
% 2.22/1.33  
% 2.22/1.33  Timing (in seconds)
% 2.22/1.33  ----------------------
% 2.22/1.33  Preprocessing        : 0.34
% 2.22/1.33  Parsing              : 0.17
% 2.22/1.33  CNF conversion       : 0.02
% 2.22/1.33  Main loop            : 0.21
% 2.22/1.33  Inferencing          : 0.08
% 2.22/1.33  Reduction            : 0.07
% 2.22/1.33  Demodulation         : 0.05
% 2.22/1.33  BG Simplification    : 0.02
% 2.22/1.33  Subsumption          : 0.03
% 2.22/1.33  Abstraction          : 0.03
% 2.22/1.33  MUC search           : 0.00
% 2.22/1.33  Cooper               : 0.00
% 2.22/1.33  Total                : 0.59
% 2.22/1.33  Index Insertion      : 0.00
% 2.22/1.33  Index Deletion       : 0.00
% 2.22/1.33  Index Matching       : 0.00
% 2.22/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
