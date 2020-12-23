%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:46 EST 2020

% Result     : Theorem 8.22s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 103 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 130 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

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

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_45,B_46] :
      ( ~ r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_123,plain,(
    ! [A_47,B_48] : k3_xboole_0(k4_xboole_0(A_47,B_48),B_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_118])).

tff(c_147,plain,(
    ! [A_1,A_47] : k3_xboole_0(A_1,k4_xboole_0(A_47,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1363,plain,(
    ! [A_107,B_108] : k4_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k3_xboole_0(A_107,k4_xboole_0(A_107,B_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_1449,plain,(
    ! [A_3] : k3_xboole_0(A_3,k4_xboole_0(A_3,A_3)) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1363])).

tff(c_1461,plain,(
    ! [A_109] : k4_xboole_0(A_109,A_109) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1449])).

tff(c_1502,plain,(
    ! [A_109] : k4_xboole_0(A_109,k1_xboole_0) = k3_xboole_0(A_109,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_14])).

tff(c_1524,plain,(
    ! [A_109] : k4_xboole_0(A_109,k1_xboole_0) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1502])).

tff(c_122,plain,(
    ! [A_16,B_17] : k3_xboole_0(k4_xboole_0(A_16,B_17),B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_118])).

tff(c_217,plain,(
    ! [A_58,B_59] : r1_xboole_0(k3_xboole_0(A_58,B_59),k4_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_16])).

tff(c_246,plain,(
    ! [B_61,A_62] : r1_xboole_0(k3_xboole_0(B_61,A_62),k4_xboole_0(A_62,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_315,plain,(
    ! [B_69,A_70] : r1_xboole_0(k1_xboole_0,k4_xboole_0(B_69,k4_xboole_0(A_70,B_69))) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_246])).

tff(c_325,plain,(
    ! [B_15] : r1_xboole_0(k1_xboole_0,k3_xboole_0(B_15,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_315])).

tff(c_339,plain,(
    ! [B_74] : r1_xboole_0(k1_xboole_0,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_325])).

tff(c_98,plain,(
    ! [A_38,B_39] :
      ( ~ r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_348,plain,(
    ! [B_75] : k3_xboole_0(k1_xboole_0,B_75) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_339,c_98])).

tff(c_408,plain,(
    ! [B_76] : k3_xboole_0(B_76,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_425,plain,(
    ! [B_76] : k5_xboole_0(B_76,k1_xboole_0) = k4_xboole_0(B_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_12])).

tff(c_1546,plain,(
    ! [B_76] : k5_xboole_0(B_76,k1_xboole_0) = B_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_425])).

tff(c_328,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_xboole_0(k2_tarski(A_71,C_72),B_73)
      | r2_hidden(C_72,B_73)
      | r2_hidden(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4186,plain,(
    ! [A_149,C_150,B_151] :
      ( k3_xboole_0(k2_tarski(A_149,C_150),B_151) = k1_xboole_0
      | r2_hidden(C_150,B_151)
      | r2_hidden(A_149,B_151) ) ),
    inference(resolution,[status(thm)],[c_328,c_98])).

tff(c_172,plain,(
    ! [A_52,B_53] : k5_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172])).

tff(c_4317,plain,(
    ! [B_151,A_149,C_150] :
      ( k4_xboole_0(B_151,k2_tarski(A_149,C_150)) = k5_xboole_0(B_151,k1_xboole_0)
      | r2_hidden(C_150,B_151)
      | r2_hidden(A_149,B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4186,c_187])).

tff(c_19183,plain,(
    ! [B_278,A_279,C_280] :
      ( k4_xboole_0(B_278,k2_tarski(A_279,C_280)) = B_278
      | r2_hidden(C_280,B_278)
      | r2_hidden(A_279,B_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1546,c_4317])).

tff(c_26,plain,(
    k4_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_19356,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_19183,c_26])).

tff(c_19411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_19356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:29:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.22/3.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/3.57  
% 8.22/3.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/3.57  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 8.22/3.57  
% 8.22/3.57  %Foreground sorts:
% 8.22/3.57  
% 8.22/3.57  
% 8.22/3.57  %Background operators:
% 8.22/3.57  
% 8.22/3.57  
% 8.22/3.57  %Foreground operators:
% 8.22/3.57  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.22/3.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.22/3.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.22/3.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.22/3.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.22/3.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.22/3.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.22/3.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.22/3.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.22/3.57  tff('#skF_5', type, '#skF_5': $i).
% 8.22/3.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.22/3.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.22/3.57  tff('#skF_3', type, '#skF_3': $i).
% 8.22/3.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.22/3.57  tff('#skF_4', type, '#skF_4': $i).
% 8.22/3.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.22/3.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.22/3.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.22/3.57  
% 8.22/3.59  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 8.22/3.59  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.22/3.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.22/3.59  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.22/3.59  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.22/3.59  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.22/3.59  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.22/3.59  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.22/3.59  tff(f_73, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 8.22/3.59  tff(c_30, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.22/3.59  tff(c_28, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.22/3.59  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/3.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/3.59  tff(c_16, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/3.59  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.22/3.59  tff(c_84, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.22/3.59  tff(c_118, plain, (![A_45, B_46]: (~r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_84])).
% 8.22/3.59  tff(c_123, plain, (![A_47, B_48]: (k3_xboole_0(k4_xboole_0(A_47, B_48), B_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_118])).
% 8.22/3.59  tff(c_147, plain, (![A_1, A_47]: (k3_xboole_0(A_1, k4_xboole_0(A_47, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_123])).
% 8.22/3.59  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.22/3.59  tff(c_99, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.22/3.59  tff(c_1363, plain, (![A_107, B_108]: (k4_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k3_xboole_0(A_107, k4_xboole_0(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 8.22/3.59  tff(c_1449, plain, (![A_3]: (k3_xboole_0(A_3, k4_xboole_0(A_3, A_3))=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1363])).
% 8.22/3.59  tff(c_1461, plain, (![A_109]: (k4_xboole_0(A_109, A_109)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1449])).
% 8.22/3.59  tff(c_1502, plain, (![A_109]: (k4_xboole_0(A_109, k1_xboole_0)=k3_xboole_0(A_109, A_109))), inference(superposition, [status(thm), theory('equality')], [c_1461, c_14])).
% 8.22/3.59  tff(c_1524, plain, (![A_109]: (k4_xboole_0(A_109, k1_xboole_0)=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1502])).
% 8.22/3.59  tff(c_122, plain, (![A_16, B_17]: (k3_xboole_0(k4_xboole_0(A_16, B_17), B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_118])).
% 8.22/3.59  tff(c_217, plain, (![A_58, B_59]: (r1_xboole_0(k3_xboole_0(A_58, B_59), k4_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_16])).
% 8.22/3.59  tff(c_246, plain, (![B_61, A_62]: (r1_xboole_0(k3_xboole_0(B_61, A_62), k4_xboole_0(A_62, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_217])).
% 8.22/3.59  tff(c_315, plain, (![B_69, A_70]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(B_69, k4_xboole_0(A_70, B_69))))), inference(superposition, [status(thm), theory('equality')], [c_122, c_246])).
% 8.22/3.59  tff(c_325, plain, (![B_15]: (r1_xboole_0(k1_xboole_0, k3_xboole_0(B_15, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_315])).
% 8.22/3.59  tff(c_339, plain, (![B_74]: (r1_xboole_0(k1_xboole_0, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_325])).
% 8.22/3.59  tff(c_98, plain, (![A_38, B_39]: (~r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_84])).
% 8.22/3.59  tff(c_348, plain, (![B_75]: (k3_xboole_0(k1_xboole_0, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_339, c_98])).
% 8.22/3.59  tff(c_408, plain, (![B_76]: (k3_xboole_0(B_76, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_348, c_2])).
% 8.22/3.59  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.22/3.59  tff(c_425, plain, (![B_76]: (k5_xboole_0(B_76, k1_xboole_0)=k4_xboole_0(B_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_408, c_12])).
% 8.22/3.59  tff(c_1546, plain, (![B_76]: (k5_xboole_0(B_76, k1_xboole_0)=B_76)), inference(demodulation, [status(thm), theory('equality')], [c_1524, c_425])).
% 8.22/3.59  tff(c_328, plain, (![A_71, C_72, B_73]: (r1_xboole_0(k2_tarski(A_71, C_72), B_73) | r2_hidden(C_72, B_73) | r2_hidden(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/3.59  tff(c_4186, plain, (![A_149, C_150, B_151]: (k3_xboole_0(k2_tarski(A_149, C_150), B_151)=k1_xboole_0 | r2_hidden(C_150, B_151) | r2_hidden(A_149, B_151))), inference(resolution, [status(thm)], [c_328, c_98])).
% 8.22/3.59  tff(c_172, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.22/3.59  tff(c_187, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_172])).
% 8.22/3.59  tff(c_4317, plain, (![B_151, A_149, C_150]: (k4_xboole_0(B_151, k2_tarski(A_149, C_150))=k5_xboole_0(B_151, k1_xboole_0) | r2_hidden(C_150, B_151) | r2_hidden(A_149, B_151))), inference(superposition, [status(thm), theory('equality')], [c_4186, c_187])).
% 8.22/3.59  tff(c_19183, plain, (![B_278, A_279, C_280]: (k4_xboole_0(B_278, k2_tarski(A_279, C_280))=B_278 | r2_hidden(C_280, B_278) | r2_hidden(A_279, B_278))), inference(demodulation, [status(thm), theory('equality')], [c_1546, c_4317])).
% 8.22/3.59  tff(c_26, plain, (k4_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.22/3.59  tff(c_19356, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_19183, c_26])).
% 8.22/3.59  tff(c_19411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_19356])).
% 8.22/3.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/3.59  
% 8.22/3.59  Inference rules
% 8.22/3.59  ----------------------
% 8.22/3.59  #Ref     : 0
% 8.22/3.59  #Sup     : 4673
% 8.22/3.59  #Fact    : 2
% 8.22/3.59  #Define  : 0
% 8.22/3.59  #Split   : 0
% 8.22/3.59  #Chain   : 0
% 8.22/3.59  #Close   : 0
% 8.22/3.59  
% 8.22/3.59  Ordering : KBO
% 8.22/3.59  
% 8.22/3.59  Simplification rules
% 8.22/3.59  ----------------------
% 8.22/3.59  #Subsume      : 474
% 8.22/3.59  #Demod        : 9793
% 8.22/3.59  #Tautology    : 3424
% 8.22/3.59  #SimpNegUnit  : 50
% 8.22/3.59  #BackRed      : 3
% 8.22/3.59  
% 8.22/3.59  #Partial instantiations: 0
% 8.22/3.59  #Strategies tried      : 1
% 8.22/3.59  
% 8.22/3.59  Timing (in seconds)
% 8.22/3.59  ----------------------
% 8.22/3.59  Preprocessing        : 0.28
% 8.22/3.59  Parsing              : 0.15
% 8.22/3.59  CNF conversion       : 0.02
% 8.22/3.59  Main loop            : 2.50
% 8.22/3.59  Inferencing          : 0.52
% 8.22/3.59  Reduction            : 1.56
% 8.22/3.59  Demodulation         : 1.40
% 8.22/3.59  BG Simplification    : 0.05
% 8.22/3.59  Subsumption          : 0.27
% 8.22/3.59  Abstraction          : 0.11
% 8.22/3.59  MUC search           : 0.00
% 8.22/3.59  Cooper               : 0.00
% 8.22/3.59  Total                : 2.81
% 8.22/3.59  Index Insertion      : 0.00
% 8.22/3.59  Index Deletion       : 0.00
% 8.22/3.59  Index Matching       : 0.00
% 8.22/3.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
