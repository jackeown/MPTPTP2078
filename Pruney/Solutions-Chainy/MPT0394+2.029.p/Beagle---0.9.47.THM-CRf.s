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
% DateTime   : Thu Dec  3 09:57:24 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 124 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   71 ( 175 expanded)
%              Number of equality atoms :   50 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_86,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_70,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [D_18,A_13] : r2_hidden(D_18,k2_tarski(A_13,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_22])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = A_51
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_145,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_339,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,k4_xboole_0(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_367,plain,(
    ! [A_96] : k3_xboole_0(A_96,k4_xboole_0(A_96,k1_xboole_0)) = k4_xboole_0(A_96,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_339])).

tff(c_380,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,k1_xboole_0) = k3_xboole_0(A_1,A_1)
      | k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_367])).

tff(c_387,plain,(
    ! [A_100] : k4_xboole_0(A_100,k1_xboole_0) = k3_xboole_0(A_100,A_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_380])).

tff(c_418,plain,(
    ! [A_100] :
      ( k3_xboole_0(A_100,A_100) = A_100
      | k3_xboole_0(A_100,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_145])).

tff(c_457,plain,(
    ! [A_101] : k3_xboole_0(A_101,A_101) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_418])).

tff(c_268,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,B_75)
      | ~ r2_hidden(C_76,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_299,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | k3_xboole_0(A_83,B_82) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_268])).

tff(c_313,plain,(
    ! [A_36,A_83] :
      ( ~ r2_hidden(A_36,A_83)
      | k3_xboole_0(A_83,k1_tarski(A_36)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_76,c_299])).

tff(c_475,plain,(
    ! [A_36] :
      ( ~ r2_hidden(A_36,k1_tarski(A_36))
      | k1_tarski(A_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_313])).

tff(c_501,plain,(
    ! [A_36] : k1_tarski(A_36) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_475])).

tff(c_50,plain,(
    ! [A_31] : k1_setfam_1(k1_tarski(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_315,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(k1_setfam_1(A_84),k1_setfam_1(B_85)) = k1_setfam_1(k2_xboole_0(A_84,B_85))
      | k1_xboole_0 = B_85
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_327,plain,(
    ! [A_84,A_31] :
      ( k1_setfam_1(k2_xboole_0(A_84,k1_tarski(A_31))) = k3_xboole_0(k1_setfam_1(A_84),A_31)
      | k1_tarski(A_31) = k1_xboole_0
      | k1_xboole_0 = A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_315])).

tff(c_4677,plain,(
    ! [A_6627,A_6628] :
      ( k1_setfam_1(k2_xboole_0(A_6627,k1_tarski(A_6628))) = k3_xboole_0(k1_setfam_1(A_6627),A_6628)
      | k1_xboole_0 = A_6627 ) ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_327])).

tff(c_4754,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_19)),B_20) = k1_setfam_1(k2_tarski(A_19,B_20))
      | k1_tarski(A_19) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4677])).

tff(c_4765,plain,(
    ! [A_19,B_20] :
      ( k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20)
      | k1_tarski(A_19) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4754])).

tff(c_4766,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_4765])).

tff(c_52,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4766,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.81  
% 4.40/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.81  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.40/1.81  
% 4.40/1.81  %Foreground sorts:
% 4.40/1.81  
% 4.40/1.81  
% 4.40/1.81  %Background operators:
% 4.40/1.81  
% 4.40/1.81  
% 4.40/1.81  %Foreground operators:
% 4.40/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.40/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.40/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.40/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.40/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.40/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.40/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.40/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.40/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.40/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.40/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.40/1.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.40/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.40/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.40/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.40/1.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.40/1.81  
% 4.59/1.82  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.59/1.82  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.59/1.82  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.59/1.82  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.59/1.82  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.59/1.82  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.59/1.82  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.59/1.82  tff(f_86, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.59/1.82  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.59/1.82  tff(f_84, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 4.59/1.82  tff(f_89, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.59/1.82  tff(c_70, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.59/1.82  tff(c_22, plain, (![D_18, A_13]: (r2_hidden(D_18, k2_tarski(A_13, D_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.59/1.82  tff(c_76, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_22])).
% 4.59/1.82  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.59/1.82  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.59/1.82  tff(c_137, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=A_51 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.59/1.82  tff(c_145, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_137])).
% 4.59/1.82  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.59/1.82  tff(c_146, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.59/1.82  tff(c_339, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k3_xboole_0(A_94, k4_xboole_0(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 4.59/1.82  tff(c_367, plain, (![A_96]: (k3_xboole_0(A_96, k4_xboole_0(A_96, k1_xboole_0))=k4_xboole_0(A_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_339])).
% 4.59/1.82  tff(c_380, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=k3_xboole_0(A_1, A_1) | k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_367])).
% 4.59/1.82  tff(c_387, plain, (![A_100]: (k4_xboole_0(A_100, k1_xboole_0)=k3_xboole_0(A_100, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_380])).
% 4.59/1.82  tff(c_418, plain, (![A_100]: (k3_xboole_0(A_100, A_100)=A_100 | k3_xboole_0(A_100, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_387, c_145])).
% 4.59/1.82  tff(c_457, plain, (![A_101]: (k3_xboole_0(A_101, A_101)=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_418])).
% 4.59/1.82  tff(c_268, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, B_75) | ~r2_hidden(C_76, A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.59/1.82  tff(c_299, plain, (![C_81, B_82, A_83]: (~r2_hidden(C_81, B_82) | ~r2_hidden(C_81, A_83) | k3_xboole_0(A_83, B_82)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_268])).
% 4.59/1.82  tff(c_313, plain, (![A_36, A_83]: (~r2_hidden(A_36, A_83) | k3_xboole_0(A_83, k1_tarski(A_36))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_299])).
% 4.59/1.82  tff(c_475, plain, (![A_36]: (~r2_hidden(A_36, k1_tarski(A_36)) | k1_tarski(A_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_457, c_313])).
% 4.59/1.82  tff(c_501, plain, (![A_36]: (k1_tarski(A_36)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_475])).
% 4.59/1.82  tff(c_50, plain, (![A_31]: (k1_setfam_1(k1_tarski(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.59/1.82  tff(c_38, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.59/1.82  tff(c_315, plain, (![A_84, B_85]: (k3_xboole_0(k1_setfam_1(A_84), k1_setfam_1(B_85))=k1_setfam_1(k2_xboole_0(A_84, B_85)) | k1_xboole_0=B_85 | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.59/1.82  tff(c_327, plain, (![A_84, A_31]: (k1_setfam_1(k2_xboole_0(A_84, k1_tarski(A_31)))=k3_xboole_0(k1_setfam_1(A_84), A_31) | k1_tarski(A_31)=k1_xboole_0 | k1_xboole_0=A_84)), inference(superposition, [status(thm), theory('equality')], [c_50, c_315])).
% 4.59/1.82  tff(c_4677, plain, (![A_6627, A_6628]: (k1_setfam_1(k2_xboole_0(A_6627, k1_tarski(A_6628)))=k3_xboole_0(k1_setfam_1(A_6627), A_6628) | k1_xboole_0=A_6627)), inference(negUnitSimplification, [status(thm)], [c_501, c_327])).
% 4.59/1.82  tff(c_4754, plain, (![A_19, B_20]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_19)), B_20)=k1_setfam_1(k2_tarski(A_19, B_20)) | k1_tarski(A_19)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_4677])).
% 4.59/1.82  tff(c_4765, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20) | k1_tarski(A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4754])).
% 4.59/1.82  tff(c_4766, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(negUnitSimplification, [status(thm)], [c_501, c_4765])).
% 4.59/1.82  tff(c_52, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.59/1.82  tff(c_4869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4766, c_52])).
% 4.59/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.82  
% 4.59/1.82  Inference rules
% 4.59/1.82  ----------------------
% 4.59/1.82  #Ref     : 0
% 4.59/1.82  #Sup     : 676
% 4.59/1.82  #Fact    : 7
% 4.59/1.82  #Define  : 0
% 4.59/1.82  #Split   : 1
% 4.59/1.82  #Chain   : 0
% 4.59/1.82  #Close   : 0
% 4.59/1.82  
% 4.59/1.82  Ordering : KBO
% 4.59/1.82  
% 4.59/1.82  Simplification rules
% 4.59/1.82  ----------------------
% 4.59/1.82  #Subsume      : 109
% 4.59/1.82  #Demod        : 162
% 4.59/1.82  #Tautology    : 255
% 4.59/1.82  #SimpNegUnit  : 25
% 4.59/1.82  #BackRed      : 3
% 4.59/1.82  
% 4.59/1.82  #Partial instantiations: 3780
% 4.59/1.82  #Strategies tried      : 1
% 4.59/1.82  
% 4.59/1.82  Timing (in seconds)
% 4.59/1.82  ----------------------
% 4.59/1.82  Preprocessing        : 0.31
% 4.59/1.82  Parsing              : 0.17
% 4.59/1.82  CNF conversion       : 0.02
% 4.59/1.82  Main loop            : 0.75
% 4.59/1.82  Inferencing          : 0.38
% 4.59/1.82  Reduction            : 0.18
% 4.59/1.82  Demodulation         : 0.12
% 4.59/1.82  BG Simplification    : 0.05
% 4.59/1.82  Subsumption          : 0.11
% 4.59/1.82  Abstraction          : 0.04
% 4.59/1.82  MUC search           : 0.00
% 4.59/1.82  Cooper               : 0.00
% 4.59/1.82  Total                : 1.10
% 4.59/1.82  Index Insertion      : 0.00
% 4.59/1.82  Index Deletion       : 0.00
% 4.59/1.82  Index Matching       : 0.00
% 4.59/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
