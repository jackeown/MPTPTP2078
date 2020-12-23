%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:00 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   73 (  89 expanded)
%              Number of leaves         :   38 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 (  88 expanded)
%              Number of equality atoms :   52 (  68 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_82,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_74,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1604,plain,(
    ! [A_144,B_145,C_146,D_147] : k2_xboole_0(k1_enumset1(A_144,B_145,C_146),k1_tarski(D_147)) = k2_enumset1(A_144,B_145,C_146,D_147) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1637,plain,(
    ! [A_42,B_43,D_147] : k2_xboole_0(k2_tarski(A_42,B_43),k1_tarski(D_147)) = k2_enumset1(A_42,A_42,B_43,D_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1604])).

tff(c_3019,plain,(
    ! [A_186,B_187,D_188] : k2_xboole_0(k2_tarski(A_186,B_187),k1_tarski(D_188)) = k1_enumset1(A_186,B_187,D_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1637])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_186,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [A_83,B_84] : k3_xboole_0(k4_xboole_0(A_83,B_84),B_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_186])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_204,plain,(
    ! [B_84,A_83] : k3_xboole_0(B_84,k4_xboole_0(A_83,B_84)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_2])).

tff(c_674,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_683,plain,(
    ! [B_84,A_83] : k4_xboole_0(B_84,k4_xboole_0(A_83,B_84)) = k5_xboole_0(B_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_674])).

tff(c_701,plain,(
    ! [B_84,A_83] : k4_xboole_0(B_84,k4_xboole_0(A_83,B_84)) = B_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_683])).

tff(c_802,plain,(
    ! [A_107,B_108] : k4_xboole_0(A_107,k4_xboole_0(A_107,B_108)) = k3_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_836,plain,(
    ! [B_84,A_83] : k3_xboole_0(B_84,k4_xboole_0(A_83,B_84)) = k4_xboole_0(B_84,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_802])).

tff(c_850,plain,(
    ! [B_84] : k4_xboole_0(B_84,B_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_836])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_698,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_674])).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_180,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_180])).

tff(c_689,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_674])).

tff(c_720,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_689])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_724,plain,(
    k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5'))) = k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_20])).

tff(c_2305,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_850,c_724])).

tff(c_3025,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3019,c_2305])).

tff(c_24,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3056,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3025,c_24])).

tff(c_46,plain,(
    ! [D_30,B_26,A_25] :
      ( D_30 = B_26
      | D_30 = A_25
      | ~ r2_hidden(D_30,k2_tarski(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3074,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3056,c_46])).

tff(c_3078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_3074])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.73  
% 3.95/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.74  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 3.95/1.74  
% 3.95/1.74  %Foreground sorts:
% 3.95/1.74  
% 3.95/1.74  
% 3.95/1.74  %Background operators:
% 3.95/1.74  
% 3.95/1.74  
% 3.95/1.74  %Foreground operators:
% 3.95/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.95/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.95/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.95/1.74  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.95/1.74  tff('#skF_7', type, '#skF_7': $i).
% 3.95/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.95/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.95/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.95/1.74  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.95/1.74  tff('#skF_6', type, '#skF_6': $i).
% 3.95/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.95/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.95/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.95/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.95/1.74  
% 4.22/1.76  tff(f_97, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 4.22/1.76  tff(f_83, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.22/1.76  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.22/1.76  tff(f_77, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.22/1.76  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.22/1.76  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.22/1.76  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.22/1.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.22/1.76  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.22/1.76  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.22/1.76  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.22/1.76  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.22/1.76  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.22/1.76  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.22/1.76  tff(f_71, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.22/1.76  tff(c_82, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.22/1.76  tff(c_80, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.22/1.76  tff(c_74, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.22/1.76  tff(c_72, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.22/1.76  tff(c_1604, plain, (![A_144, B_145, C_146, D_147]: (k2_xboole_0(k1_enumset1(A_144, B_145, C_146), k1_tarski(D_147))=k2_enumset1(A_144, B_145, C_146, D_147))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.22/1.76  tff(c_1637, plain, (![A_42, B_43, D_147]: (k2_xboole_0(k2_tarski(A_42, B_43), k1_tarski(D_147))=k2_enumset1(A_42, A_42, B_43, D_147))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1604])).
% 4.22/1.76  tff(c_3019, plain, (![A_186, B_187, D_188]: (k2_xboole_0(k2_tarski(A_186, B_187), k1_tarski(D_188))=k1_enumset1(A_186, B_187, D_188))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1637])).
% 4.22/1.76  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.22/1.76  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.22/1.76  tff(c_186, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.76  tff(c_199, plain, (![A_83, B_84]: (k3_xboole_0(k4_xboole_0(A_83, B_84), B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_186])).
% 4.22/1.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.76  tff(c_204, plain, (![B_84, A_83]: (k3_xboole_0(B_84, k4_xboole_0(A_83, B_84))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_2])).
% 4.22/1.76  tff(c_674, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.22/1.76  tff(c_683, plain, (![B_84, A_83]: (k4_xboole_0(B_84, k4_xboole_0(A_83, B_84))=k5_xboole_0(B_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_204, c_674])).
% 4.22/1.76  tff(c_701, plain, (![B_84, A_83]: (k4_xboole_0(B_84, k4_xboole_0(A_83, B_84))=B_84)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_683])).
% 4.22/1.76  tff(c_802, plain, (![A_107, B_108]: (k4_xboole_0(A_107, k4_xboole_0(A_107, B_108))=k3_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.22/1.76  tff(c_836, plain, (![B_84, A_83]: (k3_xboole_0(B_84, k4_xboole_0(A_83, B_84))=k4_xboole_0(B_84, B_84))), inference(superposition, [status(thm), theory('equality')], [c_701, c_802])).
% 4.22/1.76  tff(c_850, plain, (![B_84]: (k4_xboole_0(B_84, B_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_836])).
% 4.22/1.76  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.22/1.76  tff(c_698, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_674])).
% 4.22/1.76  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.22/1.76  tff(c_180, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.76  tff(c_184, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_84, c_180])).
% 4.22/1.76  tff(c_689, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_674])).
% 4.22/1.76  tff(c_720, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_689])).
% 4.22/1.76  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.22/1.76  tff(c_724, plain, (k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5')))=k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_720, c_20])).
% 4.22/1.76  tff(c_2305, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_850, c_724])).
% 4.22/1.76  tff(c_3025, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3019, c_2305])).
% 4.22/1.76  tff(c_24, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.22/1.76  tff(c_3056, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3025, c_24])).
% 4.22/1.76  tff(c_46, plain, (![D_30, B_26, A_25]: (D_30=B_26 | D_30=A_25 | ~r2_hidden(D_30, k2_tarski(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.22/1.76  tff(c_3074, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_3056, c_46])).
% 4.22/1.76  tff(c_3078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_3074])).
% 4.22/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.76  
% 4.22/1.76  Inference rules
% 4.22/1.76  ----------------------
% 4.22/1.76  #Ref     : 0
% 4.22/1.76  #Sup     : 753
% 4.22/1.76  #Fact    : 0
% 4.22/1.76  #Define  : 0
% 4.22/1.76  #Split   : 0
% 4.22/1.76  #Chain   : 0
% 4.22/1.76  #Close   : 0
% 4.22/1.76  
% 4.22/1.76  Ordering : KBO
% 4.22/1.76  
% 4.22/1.76  Simplification rules
% 4.22/1.76  ----------------------
% 4.22/1.76  #Subsume      : 54
% 4.22/1.76  #Demod        : 686
% 4.22/1.76  #Tautology    : 572
% 4.22/1.76  #SimpNegUnit  : 1
% 4.22/1.76  #BackRed      : 2
% 4.22/1.76  
% 4.22/1.76  #Partial instantiations: 0
% 4.22/1.76  #Strategies tried      : 1
% 4.22/1.76  
% 4.22/1.76  Timing (in seconds)
% 4.22/1.76  ----------------------
% 4.22/1.76  Preprocessing        : 0.34
% 4.22/1.76  Parsing              : 0.16
% 4.22/1.76  CNF conversion       : 0.03
% 4.22/1.76  Main loop            : 0.63
% 4.22/1.76  Inferencing          : 0.19
% 4.22/1.76  Reduction            : 0.29
% 4.22/1.76  Demodulation         : 0.24
% 4.22/1.76  BG Simplification    : 0.03
% 4.22/1.76  Subsumption          : 0.10
% 4.22/1.76  Abstraction          : 0.03
% 4.22/1.76  MUC search           : 0.00
% 4.22/1.76  Cooper               : 0.00
% 4.22/1.76  Total                : 1.01
% 4.22/1.76  Index Insertion      : 0.00
% 4.22/1.77  Index Deletion       : 0.00
% 4.22/1.77  Index Matching       : 0.00
% 4.22/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
