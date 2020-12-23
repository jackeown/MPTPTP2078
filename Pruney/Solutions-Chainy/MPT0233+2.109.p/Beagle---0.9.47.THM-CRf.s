%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:35 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   66 (  72 expanded)
%              Number of leaves         :   35 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 (  81 expanded)
%              Number of equality atoms :   45 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_70,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_246,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_270,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_246])).

tff(c_276,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_270])).

tff(c_64,plain,(
    ! [B_54] : k4_xboole_0(k1_tarski(B_54),k1_tarski(B_54)) != k1_tarski(B_54) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_277,plain,(
    ! [B_54] : k1_tarski(B_54) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_64])).

tff(c_60,plain,(
    ! [B_51,C_52] : r1_tarski(k1_tarski(B_51),k2_tarski(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_156,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_156])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [A_83,B_84,C_85] :
      ( r1_tarski(A_83,B_84)
      | ~ r1_tarski(A_83,k3_xboole_0(B_84,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_367,plain,(
    ! [A_97,B_98,A_99] :
      ( r1_tarski(A_97,B_98)
      | ~ r1_tarski(A_97,k3_xboole_0(A_99,B_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_493,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_113,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_367])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_782,plain,(
    ! [A_141] :
      ( k3_xboole_0(A_141,k2_tarski('#skF_5','#skF_6')) = A_141
      | ~ r1_tarski(A_141,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_493,c_10])).

tff(c_816,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_782])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_832,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_816,c_6])).

tff(c_841,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_832])).

tff(c_32,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    ! [B_48,C_49] :
      ( k4_xboole_0(k2_tarski(B_48,B_48),C_49) = k1_tarski(B_48)
      | r2_hidden(B_48,C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_73,plain,(
    ! [B_48,C_49] :
      ( k4_xboole_0(k1_tarski(B_48),C_49) = k1_tarski(B_48)
      | r2_hidden(B_48,C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50])).

tff(c_846,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_73])).

tff(c_852,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_846])).

tff(c_14,plain,(
    ! [D_18,B_14,A_13] :
      ( D_18 = B_14
      | D_18 = A_13
      | ~ r2_hidden(D_18,k2_tarski(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_857,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_852,c_14])).

tff(c_861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_68,c_857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.67/1.39  
% 2.67/1.39  %Foreground sorts:
% 2.67/1.39  
% 2.67/1.39  
% 2.67/1.39  %Background operators:
% 2.67/1.39  
% 2.67/1.39  
% 2.67/1.39  %Foreground operators:
% 2.67/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.67/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.67/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.39  
% 2.90/1.40  tff(f_103, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.90/1.40  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.90/1.40  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.90/1.40  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.90/1.40  tff(f_93, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.90/1.40  tff(f_88, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.90/1.40  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.90/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.90/1.40  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.90/1.40  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.90/1.40  tff(f_73, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.90/1.40  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.90/1.40  tff(c_70, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.90/1.40  tff(c_68, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.90/1.40  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.40  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.90/1.40  tff(c_246, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.40  tff(c_270, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_246])).
% 2.90/1.40  tff(c_276, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_270])).
% 2.90/1.40  tff(c_64, plain, (![B_54]: (k4_xboole_0(k1_tarski(B_54), k1_tarski(B_54))!=k1_tarski(B_54))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.90/1.40  tff(c_277, plain, (![B_54]: (k1_tarski(B_54)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_276, c_64])).
% 2.90/1.40  tff(c_60, plain, (![B_51, C_52]: (r1_tarski(k1_tarski(B_51), k2_tarski(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.90/1.40  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.90/1.40  tff(c_156, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.40  tff(c_179, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_156])).
% 2.90/1.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.90/1.40  tff(c_227, plain, (![A_83, B_84, C_85]: (r1_tarski(A_83, B_84) | ~r1_tarski(A_83, k3_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.40  tff(c_367, plain, (![A_97, B_98, A_99]: (r1_tarski(A_97, B_98) | ~r1_tarski(A_97, k3_xboole_0(A_99, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_227])).
% 2.90/1.40  tff(c_493, plain, (![A_113]: (r1_tarski(A_113, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_113, k2_tarski('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_179, c_367])).
% 2.90/1.40  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.40  tff(c_782, plain, (![A_141]: (k3_xboole_0(A_141, k2_tarski('#skF_5', '#skF_6'))=A_141 | ~r1_tarski(A_141, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_493, c_10])).
% 2.90/1.40  tff(c_816, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_60, c_782])).
% 2.90/1.40  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.40  tff(c_832, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_816, c_6])).
% 2.90/1.40  tff(c_841, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_832])).
% 2.90/1.40  tff(c_32, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.90/1.40  tff(c_50, plain, (![B_48, C_49]: (k4_xboole_0(k2_tarski(B_48, B_48), C_49)=k1_tarski(B_48) | r2_hidden(B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.90/1.40  tff(c_73, plain, (![B_48, C_49]: (k4_xboole_0(k1_tarski(B_48), C_49)=k1_tarski(B_48) | r2_hidden(B_48, C_49))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50])).
% 2.90/1.40  tff(c_846, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_841, c_73])).
% 2.90/1.40  tff(c_852, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_277, c_846])).
% 2.90/1.40  tff(c_14, plain, (![D_18, B_14, A_13]: (D_18=B_14 | D_18=A_13 | ~r2_hidden(D_18, k2_tarski(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.90/1.40  tff(c_857, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_852, c_14])).
% 2.90/1.40  tff(c_861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_68, c_857])).
% 2.90/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  Inference rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Ref     : 0
% 2.90/1.40  #Sup     : 195
% 2.90/1.40  #Fact    : 0
% 2.90/1.40  #Define  : 0
% 2.90/1.40  #Split   : 0
% 2.90/1.40  #Chain   : 0
% 2.90/1.40  #Close   : 0
% 2.90/1.40  
% 2.90/1.40  Ordering : KBO
% 2.90/1.40  
% 2.90/1.40  Simplification rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Subsume      : 15
% 2.90/1.40  #Demod        : 42
% 2.90/1.40  #Tautology    : 121
% 2.90/1.40  #SimpNegUnit  : 13
% 2.90/1.40  #BackRed      : 1
% 2.90/1.40  
% 2.90/1.40  #Partial instantiations: 0
% 2.90/1.40  #Strategies tried      : 1
% 2.90/1.40  
% 2.90/1.40  Timing (in seconds)
% 2.90/1.40  ----------------------
% 2.90/1.41  Preprocessing        : 0.33
% 2.90/1.41  Parsing              : 0.17
% 2.90/1.41  CNF conversion       : 0.03
% 2.90/1.41  Main loop            : 0.33
% 2.90/1.41  Inferencing          : 0.12
% 2.90/1.41  Reduction            : 0.11
% 2.90/1.41  Demodulation         : 0.08
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.06
% 2.90/1.41  Abstraction          : 0.02
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.69
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
