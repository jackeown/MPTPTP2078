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
% DateTime   : Thu Dec  3 09:48:58 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   69 (  92 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 105 expanded)
%              Number of equality atoms :   51 (  78 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_60,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_176,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_198,plain,(
    ! [A_62] : k3_xboole_0(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_207,plain,(
    ! [A_62] : k3_xboole_0(A_62,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_4])).

tff(c_413,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_433,plain,(
    ! [A_62] : k5_xboole_0(A_62,k1_xboole_0) = k4_xboole_0(A_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_413])).

tff(c_450,plain,(
    ! [A_62] : k5_xboole_0(A_62,k1_xboole_0) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_433])).

tff(c_343,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_361,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_343])).

tff(c_365,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_361])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_187,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_176])).

tff(c_439,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_413])).

tff(c_452,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_439])).

tff(c_62,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_186,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_176])).

tff(c_430,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_413])).

tff(c_517,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_430])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_524,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_22])).

tff(c_528,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_524])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_649,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_2])).

tff(c_48,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k1_tarski(A_24),k2_tarski(B_25,C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_990,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_5') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_48])).

tff(c_30,plain,(
    ! [E_23,B_18,C_19] : r2_hidden(E_23,k1_enumset1(E_23,B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1007,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_30])).

tff(c_52,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_942,plain,(
    ! [E_102,C_103,B_104,A_105] :
      ( E_102 = C_103
      | E_102 = B_104
      | E_102 = A_105
      | ~ r2_hidden(E_102,k1_enumset1(A_105,B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1381,plain,(
    ! [E_134,B_135,A_136] :
      ( E_134 = B_135
      | E_134 = A_136
      | E_134 = A_136
      | ~ r2_hidden(E_134,k2_tarski(A_136,B_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_942])).

tff(c_1384,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1007,c_1381])).

tff(c_1397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_58,c_1384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/2.05  
% 3.73/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/2.05  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.73/2.05  
% 3.73/2.05  %Foreground sorts:
% 3.73/2.05  
% 3.73/2.05  
% 3.73/2.05  %Background operators:
% 3.73/2.05  
% 3.73/2.05  
% 3.73/2.05  %Foreground operators:
% 3.73/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.73/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/2.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.73/2.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/2.05  tff('#skF_5', type, '#skF_5': $i).
% 3.73/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.73/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/2.05  tff('#skF_3', type, '#skF_3': $i).
% 3.73/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/2.05  tff('#skF_4', type, '#skF_4': $i).
% 3.73/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.73/2.05  
% 3.98/2.07  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.98/2.07  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.98/2.07  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.98/2.07  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.98/2.07  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.98/2.07  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.98/2.07  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.98/2.07  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.98/2.07  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.98/2.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.98/2.07  tff(f_66, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.98/2.07  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.98/2.07  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.98/2.07  tff(c_60, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.98/2.07  tff(c_58, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.98/2.07  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/2.07  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/2.07  tff(c_176, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/2.07  tff(c_198, plain, (![A_62]: (k3_xboole_0(k1_xboole_0, A_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_176])).
% 3.98/2.07  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.98/2.07  tff(c_207, plain, (![A_62]: (k3_xboole_0(A_62, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_198, c_4])).
% 3.98/2.07  tff(c_413, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.98/2.07  tff(c_433, plain, (![A_62]: (k5_xboole_0(A_62, k1_xboole_0)=k4_xboole_0(A_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_207, c_413])).
% 3.98/2.07  tff(c_450, plain, (![A_62]: (k5_xboole_0(A_62, k1_xboole_0)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_433])).
% 3.98/2.07  tff(c_343, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/2.07  tff(c_361, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_343])).
% 3.98/2.07  tff(c_365, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_207, c_361])).
% 3.98/2.07  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.98/2.07  tff(c_187, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_176])).
% 3.98/2.07  tff(c_439, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_187, c_413])).
% 3.98/2.07  tff(c_452, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_365, c_439])).
% 3.98/2.07  tff(c_62, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.98/2.07  tff(c_186, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_62, c_176])).
% 3.98/2.07  tff(c_430, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_413])).
% 3.98/2.07  tff(c_517, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_452, c_430])).
% 3.98/2.07  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.98/2.07  tff(c_524, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_517, c_22])).
% 3.98/2.07  tff(c_528, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_524])).
% 3.98/2.07  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/2.07  tff(c_649, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_528, c_2])).
% 3.98/2.07  tff(c_48, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(B_25, C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/2.07  tff(c_990, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_5')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_649, c_48])).
% 3.98/2.07  tff(c_30, plain, (![E_23, B_18, C_19]: (r2_hidden(E_23, k1_enumset1(E_23, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/2.07  tff(c_1007, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_990, c_30])).
% 3.98/2.07  tff(c_52, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/2.07  tff(c_942, plain, (![E_102, C_103, B_104, A_105]: (E_102=C_103 | E_102=B_104 | E_102=A_105 | ~r2_hidden(E_102, k1_enumset1(A_105, B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/2.07  tff(c_1381, plain, (![E_134, B_135, A_136]: (E_134=B_135 | E_134=A_136 | E_134=A_136 | ~r2_hidden(E_134, k2_tarski(A_136, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_942])).
% 3.98/2.07  tff(c_1384, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1007, c_1381])).
% 3.98/2.07  tff(c_1397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_58, c_1384])).
% 3.98/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/2.07  
% 3.98/2.07  Inference rules
% 3.98/2.07  ----------------------
% 3.98/2.07  #Ref     : 0
% 3.98/2.07  #Sup     : 320
% 3.98/2.07  #Fact    : 0
% 3.98/2.07  #Define  : 0
% 3.98/2.07  #Split   : 1
% 3.98/2.07  #Chain   : 0
% 3.98/2.07  #Close   : 0
% 3.98/2.07  
% 3.98/2.07  Ordering : KBO
% 3.98/2.07  
% 3.98/2.07  Simplification rules
% 3.98/2.07  ----------------------
% 3.98/2.07  #Subsume      : 23
% 3.98/2.07  #Demod        : 169
% 3.98/2.07  #Tautology    : 248
% 3.98/2.07  #SimpNegUnit  : 4
% 3.98/2.07  #BackRed      : 2
% 3.98/2.07  
% 3.98/2.07  #Partial instantiations: 0
% 3.98/2.07  #Strategies tried      : 1
% 3.98/2.07  
% 3.98/2.07  Timing (in seconds)
% 3.98/2.07  ----------------------
% 3.98/2.08  Preprocessing        : 0.52
% 3.98/2.08  Parsing              : 0.26
% 3.98/2.08  CNF conversion       : 0.04
% 3.98/2.08  Main loop            : 0.66
% 3.98/2.08  Inferencing          : 0.23
% 3.98/2.08  Reduction            : 0.25
% 3.98/2.08  Demodulation         : 0.20
% 3.98/2.08  BG Simplification    : 0.03
% 3.98/2.08  Subsumption          : 0.11
% 3.98/2.08  Abstraction          : 0.03
% 3.98/2.08  MUC search           : 0.00
% 3.98/2.08  Cooper               : 0.00
% 3.98/2.08  Total                : 1.23
% 3.98/2.08  Index Insertion      : 0.00
% 3.98/2.08  Index Deletion       : 0.00
% 3.98/2.08  Index Matching       : 0.00
% 3.98/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
