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
% DateTime   : Thu Dec  3 09:48:55 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 178 expanded)
%              Number of leaves         :   34 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 ( 197 expanded)
%              Number of equality atoms :   53 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_328,plain,(
    ! [A_92,B_93,C_94,D_95] : k2_xboole_0(k1_enumset1(A_92,B_93,C_94),k1_tarski(D_95)) = k2_enumset1(A_92,B_93,C_94,D_95) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_346,plain,(
    ! [A_24,B_25,D_95] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_95)) = k2_enumset1(A_24,A_24,B_25,D_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_328])).

tff(c_351,plain,(
    ! [A_96,B_97,D_98] : k2_xboole_0(k2_tarski(A_96,B_97),k1_tarski(D_98)) = k1_enumset1(A_96,B_97,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_346])).

tff(c_369,plain,(
    ! [A_23,D_98] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_98)) = k1_enumset1(A_23,A_23,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_351])).

tff(c_373,plain,(
    ! [A_23,D_98] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_98)) = k2_tarski(A_23,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_369])).

tff(c_374,plain,(
    ! [A_99,D_100] : k2_xboole_0(k1_tarski(A_99),k1_tarski(D_100)) = k2_tarski(A_99,D_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_369])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_4,B_5] : k3_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k5_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_154])).

tff(c_173,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_169])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_144,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_144])).

tff(c_163,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_154])).

tff(c_178,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_163])).

tff(c_191,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_206,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k2_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_191])).

tff(c_217,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_206])).

tff(c_383,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_217])).

tff(c_350,plain,(
    ! [A_24,B_25,D_95] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_95)) = k1_enumset1(A_24,B_25,D_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_346])).

tff(c_412,plain,(
    ! [D_95] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_95)) = k1_enumset1('#skF_4','#skF_3',D_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_350])).

tff(c_463,plain,(
    ! [D_107] : k1_enumset1('#skF_4','#skF_3',D_107) = k2_tarski('#skF_4',D_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_412])).

tff(c_18,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_478,plain,(
    ! [D_107] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_18])).

tff(c_425,plain,(
    ! [E_101,C_102,B_103,A_104] :
      ( E_101 = C_102
      | E_101 = B_103
      | E_101 = A_104
      | ~ r2_hidden(E_101,k1_enumset1(A_104,B_103,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_746,plain,(
    ! [E_132,B_133,A_134] :
      ( E_132 = B_133
      | E_132 = A_134
      | E_132 = A_134
      | ~ r2_hidden(E_132,k2_tarski(A_134,B_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_425])).

tff(c_749,plain,(
    ! [D_107] :
      ( D_107 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_478,c_746])).

tff(c_770,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_749])).

tff(c_764,plain,(
    ! [D_107] : D_107 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_749])).

tff(c_949,plain,(
    ! [D_2541] : D_2541 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_764])).

tff(c_1117,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:07:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.54  
% 3.36/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.54  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.36/1.54  
% 3.36/1.54  %Foreground sorts:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Background operators:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Foreground operators:
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.36/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.36/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.36/1.54  
% 3.36/1.55  tff(f_75, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 3.36/1.55  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.36/1.55  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.36/1.55  tff(f_62, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.36/1.55  tff(f_56, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.36/1.55  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.36/1.55  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.36/1.55  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.36/1.55  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.36/1.55  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.36/1.55  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.36/1.55  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.36/1.55  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.36/1.55  tff(c_42, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.55  tff(c_40, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.55  tff(c_44, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.55  tff(c_328, plain, (![A_92, B_93, C_94, D_95]: (k2_xboole_0(k1_enumset1(A_92, B_93, C_94), k1_tarski(D_95))=k2_enumset1(A_92, B_93, C_94, D_95))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.55  tff(c_346, plain, (![A_24, B_25, D_95]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_95))=k2_enumset1(A_24, A_24, B_25, D_95))), inference(superposition, [status(thm), theory('equality')], [c_42, c_328])).
% 3.36/1.55  tff(c_351, plain, (![A_96, B_97, D_98]: (k2_xboole_0(k2_tarski(A_96, B_97), k1_tarski(D_98))=k1_enumset1(A_96, B_97, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_346])).
% 3.36/1.55  tff(c_369, plain, (![A_23, D_98]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_98))=k1_enumset1(A_23, A_23, D_98))), inference(superposition, [status(thm), theory('equality')], [c_40, c_351])).
% 3.36/1.55  tff(c_373, plain, (![A_23, D_98]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_98))=k2_tarski(A_23, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_369])).
% 3.36/1.55  tff(c_374, plain, (![A_99, D_100]: (k2_xboole_0(k1_tarski(A_99), k1_tarski(D_100))=k2_tarski(A_99, D_100))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_369])).
% 3.36/1.55  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.55  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.55  tff(c_6, plain, (![A_4, B_5]: (k3_xboole_0(A_4, k2_xboole_0(A_4, B_5))=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.55  tff(c_154, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.55  tff(c_169, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k5_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_154])).
% 3.36/1.55  tff(c_173, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_169])).
% 3.36/1.55  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.36/1.55  tff(c_144, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.55  tff(c_148, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_56, c_144])).
% 3.36/1.55  tff(c_163, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_154])).
% 3.36/1.55  tff(c_178, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_173, c_163])).
% 3.36/1.55  tff(c_191, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.55  tff(c_206, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k2_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_191])).
% 3.36/1.55  tff(c_217, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_206])).
% 3.36/1.55  tff(c_383, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_374, c_217])).
% 3.36/1.55  tff(c_350, plain, (![A_24, B_25, D_95]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_95))=k1_enumset1(A_24, B_25, D_95))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_346])).
% 3.36/1.55  tff(c_412, plain, (![D_95]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_95))=k1_enumset1('#skF_4', '#skF_3', D_95))), inference(superposition, [status(thm), theory('equality')], [c_383, c_350])).
% 3.36/1.55  tff(c_463, plain, (![D_107]: (k1_enumset1('#skF_4', '#skF_3', D_107)=k2_tarski('#skF_4', D_107))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_412])).
% 3.36/1.55  tff(c_18, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.36/1.55  tff(c_478, plain, (![D_107]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_107)))), inference(superposition, [status(thm), theory('equality')], [c_463, c_18])).
% 3.36/1.55  tff(c_425, plain, (![E_101, C_102, B_103, A_104]: (E_101=C_102 | E_101=B_103 | E_101=A_104 | ~r2_hidden(E_101, k1_enumset1(A_104, B_103, C_102)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.36/1.55  tff(c_746, plain, (![E_132, B_133, A_134]: (E_132=B_133 | E_132=A_134 | E_132=A_134 | ~r2_hidden(E_132, k2_tarski(A_134, B_133)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_425])).
% 3.36/1.55  tff(c_749, plain, (![D_107]: (D_107='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_478, c_746])).
% 3.36/1.55  tff(c_770, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_749])).
% 3.36/1.55  tff(c_764, plain, (![D_107]: (D_107='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_749])).
% 3.36/1.55  tff(c_949, plain, (![D_2541]: (D_2541='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_770, c_764])).
% 3.36/1.55  tff(c_1117, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_949, c_54])).
% 3.36/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  Inference rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Ref     : 0
% 3.45/1.55  #Sup     : 328
% 3.45/1.55  #Fact    : 0
% 3.45/1.55  #Define  : 0
% 3.45/1.55  #Split   : 0
% 3.45/1.55  #Chain   : 0
% 3.45/1.55  #Close   : 0
% 3.45/1.55  
% 3.45/1.55  Ordering : KBO
% 3.45/1.55  
% 3.45/1.55  Simplification rules
% 3.45/1.55  ----------------------
% 3.45/1.55  #Subsume      : 65
% 3.45/1.55  #Demod        : 108
% 3.45/1.55  #Tautology    : 145
% 3.45/1.55  #SimpNegUnit  : 7
% 3.45/1.55  #BackRed      : 1
% 3.45/1.55  
% 3.45/1.55  #Partial instantiations: 46
% 3.45/1.55  #Strategies tried      : 1
% 3.45/1.55  
% 3.45/1.55  Timing (in seconds)
% 3.45/1.55  ----------------------
% 3.45/1.56  Preprocessing        : 0.34
% 3.45/1.56  Parsing              : 0.17
% 3.45/1.56  CNF conversion       : 0.03
% 3.45/1.56  Main loop            : 0.45
% 3.45/1.56  Inferencing          : 0.21
% 3.45/1.56  Reduction            : 0.13
% 3.45/1.56  Demodulation         : 0.10
% 3.45/1.56  BG Simplification    : 0.02
% 3.45/1.56  Subsumption          : 0.06
% 3.45/1.56  Abstraction          : 0.02
% 3.45/1.56  MUC search           : 0.00
% 3.45/1.56  Cooper               : 0.00
% 3.45/1.56  Total                : 0.83
% 3.45/1.56  Index Insertion      : 0.00
% 3.45/1.56  Index Deletion       : 0.00
% 3.45/1.56  Index Matching       : 0.00
% 3.45/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
