%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:20 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 139 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :   80 ( 150 expanded)
%              Number of equality atoms :   54 ( 113 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_75,axiom,(
    ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(c_60,plain,(
    k1_setfam_1(k1_tarski('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_292,plain,(
    ! [A_93,B_94,C_95] : k5_xboole_0(k5_xboole_0(A_93,B_94),C_95) = k5_xboole_0(A_93,k5_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_570,plain,(
    ! [A_103,C_104] : k5_xboole_0(A_103,k5_xboole_0(A_103,C_104)) = k5_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_292])).

tff(c_642,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_570])).

tff(c_658,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_642])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_213,plain,(
    ! [A_90,B_91] : k5_xboole_0(k5_xboole_0(A_90,B_91),k2_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_231,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_213])).

tff(c_240,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = k3_xboole_0(A_1,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_231])).

tff(c_730,plain,(
    ! [A_110] : k3_xboole_0(A_110,A_110) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_240])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_736,plain,(
    ! [A_110] : k5_xboole_0(A_110,A_110) = k4_xboole_0(A_110,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_10])).

tff(c_741,plain,(
    ! [A_110] : k4_xboole_0(A_110,A_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_736])).

tff(c_50,plain,(
    ! [B_58] : k4_xboole_0(k1_tarski(B_58),k1_tarski(B_58)) != k1_tarski(B_58) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_744,plain,(
    ! [B_58] : k1_tarski(B_58) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_50])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_125,plain,(
    ! [A_75,B_76] : k3_tarski(k2_tarski(A_75,B_76)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_137,plain,(
    ! [A_27] : k3_tarski(k1_tarski(A_27)) = k2_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_125])).

tff(c_140,plain,(
    ! [A_27] : k3_tarski(k1_tarski(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_137])).

tff(c_762,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_3'(A_112,B_113),A_112)
      | r1_tarski(B_113,k1_setfam_1(A_112))
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_767,plain,(
    ! [A_14,B_113] :
      ( '#skF_3'(k1_tarski(A_14),B_113) = A_14
      | r1_tarski(B_113,k1_setfam_1(k1_tarski(A_14)))
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_762,c_20])).

tff(c_3149,plain,(
    ! [A_203,B_204] :
      ( '#skF_3'(k1_tarski(A_203),B_204) = A_203
      | r1_tarski(B_204,k1_setfam_1(k1_tarski(A_203))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_767])).

tff(c_54,plain,(
    ! [A_59] : r1_tarski(k1_setfam_1(A_59),k3_tarski(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_154,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    ! [A_59] :
      ( k3_tarski(A_59) = k1_setfam_1(A_59)
      | ~ r1_tarski(k3_tarski(A_59),k1_setfam_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_54,c_154])).

tff(c_3157,plain,(
    ! [A_203] :
      ( k3_tarski(k1_tarski(A_203)) = k1_setfam_1(k1_tarski(A_203))
      | '#skF_3'(k1_tarski(A_203),k3_tarski(k1_tarski(A_203))) = A_203 ) ),
    inference(resolution,[status(thm)],[c_3149,c_162])).

tff(c_3499,plain,(
    ! [A_210] :
      ( k1_setfam_1(k1_tarski(A_210)) = A_210
      | '#skF_3'(k1_tarski(A_210),A_210) = A_210 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_3157])).

tff(c_3542,plain,(
    '#skF_3'(k1_tarski('#skF_4'),'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3499,c_60])).

tff(c_56,plain,(
    ! [B_61,A_60] :
      ( ~ r1_tarski(B_61,'#skF_3'(A_60,B_61))
      | r1_tarski(B_61,k1_setfam_1(A_60))
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3557,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4',k1_setfam_1(k1_tarski('#skF_4')))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3542,c_56])).

tff(c_3564,plain,
    ( r1_tarski('#skF_4',k1_setfam_1(k1_tarski('#skF_4')))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3557])).

tff(c_3565,plain,(
    r1_tarski('#skF_4',k1_setfam_1(k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_3564])).

tff(c_141,plain,(
    ! [A_77] : k3_tarski(k1_tarski(A_77)) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_137])).

tff(c_147,plain,(
    ! [A_77] : r1_tarski(k1_setfam_1(k1_tarski(A_77)),A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_54])).

tff(c_161,plain,(
    ! [A_77] :
      ( k1_setfam_1(k1_tarski(A_77)) = A_77
      | ~ r1_tarski(A_77,k1_setfam_1(k1_tarski(A_77))) ) ),
    inference(resolution,[status(thm)],[c_147,c_154])).

tff(c_3622,plain,(
    k1_setfam_1(k1_tarski('#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3565,c_161])).

tff(c_3631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.77  
% 4.41/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.78  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.41/1.78  
% 4.41/1.78  %Foreground sorts:
% 4.41/1.78  
% 4.41/1.78  
% 4.41/1.78  %Background operators:
% 4.41/1.78  
% 4.41/1.78  
% 4.41/1.78  %Foreground operators:
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.41/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.41/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.41/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.41/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.41/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.41/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.41/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.41/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.41/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.41/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.41/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.41/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.41/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.41/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.41/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.41/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.41/1.78  
% 4.48/1.79  tff(f_87, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.48/1.79  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.48/1.79  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.48/1.79  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.48/1.79  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.48/1.79  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.48/1.79  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.48/1.79  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.48/1.79  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.48/1.79  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.48/1.79  tff(f_68, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.48/1.79  tff(f_84, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 4.48/1.79  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.48/1.79  tff(f_75, axiom, (![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_setfam_1)).
% 4.48/1.79  tff(c_60, plain, (k1_setfam_1(k1_tarski('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.79  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.48/1.79  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.48/1.79  tff(c_292, plain, (![A_93, B_94, C_95]: (k5_xboole_0(k5_xboole_0(A_93, B_94), C_95)=k5_xboole_0(A_93, k5_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.79  tff(c_570, plain, (![A_103, C_104]: (k5_xboole_0(A_103, k5_xboole_0(A_103, C_104))=k5_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_16, c_292])).
% 4.48/1.79  tff(c_642, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_570])).
% 4.48/1.79  tff(c_658, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_642])).
% 4.48/1.79  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.48/1.79  tff(c_213, plain, (![A_90, B_91]: (k5_xboole_0(k5_xboole_0(A_90, B_91), k2_xboole_0(A_90, B_91))=k3_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.48/1.79  tff(c_231, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_213])).
% 4.48/1.79  tff(c_240, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=k3_xboole_0(A_1, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_231])).
% 4.48/1.79  tff(c_730, plain, (![A_110]: (k3_xboole_0(A_110, A_110)=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_658, c_240])).
% 4.48/1.79  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.48/1.79  tff(c_736, plain, (![A_110]: (k5_xboole_0(A_110, A_110)=k4_xboole_0(A_110, A_110))), inference(superposition, [status(thm), theory('equality')], [c_730, c_10])).
% 4.48/1.79  tff(c_741, plain, (![A_110]: (k4_xboole_0(A_110, A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_736])).
% 4.48/1.79  tff(c_50, plain, (![B_58]: (k4_xboole_0(k1_tarski(B_58), k1_tarski(B_58))!=k1_tarski(B_58))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.48/1.79  tff(c_744, plain, (![B_58]: (k1_tarski(B_58)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_741, c_50])).
% 4.48/1.79  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.48/1.79  tff(c_34, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.48/1.79  tff(c_125, plain, (![A_75, B_76]: (k3_tarski(k2_tarski(A_75, B_76))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.48/1.79  tff(c_137, plain, (![A_27]: (k3_tarski(k1_tarski(A_27))=k2_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_34, c_125])).
% 4.48/1.79  tff(c_140, plain, (![A_27]: (k3_tarski(k1_tarski(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_137])).
% 4.48/1.79  tff(c_762, plain, (![A_112, B_113]: (r2_hidden('#skF_3'(A_112, B_113), A_112) | r1_tarski(B_113, k1_setfam_1(A_112)) | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.48/1.79  tff(c_20, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.79  tff(c_767, plain, (![A_14, B_113]: ('#skF_3'(k1_tarski(A_14), B_113)=A_14 | r1_tarski(B_113, k1_setfam_1(k1_tarski(A_14))) | k1_tarski(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_762, c_20])).
% 4.48/1.79  tff(c_3149, plain, (![A_203, B_204]: ('#skF_3'(k1_tarski(A_203), B_204)=A_203 | r1_tarski(B_204, k1_setfam_1(k1_tarski(A_203))))), inference(negUnitSimplification, [status(thm)], [c_744, c_767])).
% 4.48/1.79  tff(c_54, plain, (![A_59]: (r1_tarski(k1_setfam_1(A_59), k3_tarski(A_59)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.48/1.79  tff(c_154, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.48/1.79  tff(c_162, plain, (![A_59]: (k3_tarski(A_59)=k1_setfam_1(A_59) | ~r1_tarski(k3_tarski(A_59), k1_setfam_1(A_59)))), inference(resolution, [status(thm)], [c_54, c_154])).
% 4.48/1.79  tff(c_3157, plain, (![A_203]: (k3_tarski(k1_tarski(A_203))=k1_setfam_1(k1_tarski(A_203)) | '#skF_3'(k1_tarski(A_203), k3_tarski(k1_tarski(A_203)))=A_203)), inference(resolution, [status(thm)], [c_3149, c_162])).
% 4.48/1.79  tff(c_3499, plain, (![A_210]: (k1_setfam_1(k1_tarski(A_210))=A_210 | '#skF_3'(k1_tarski(A_210), A_210)=A_210)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_3157])).
% 4.48/1.79  tff(c_3542, plain, ('#skF_3'(k1_tarski('#skF_4'), '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3499, c_60])).
% 4.48/1.79  tff(c_56, plain, (![B_61, A_60]: (~r1_tarski(B_61, '#skF_3'(A_60, B_61)) | r1_tarski(B_61, k1_setfam_1(A_60)) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.48/1.79  tff(c_3557, plain, (~r1_tarski('#skF_4', '#skF_4') | r1_tarski('#skF_4', k1_setfam_1(k1_tarski('#skF_4'))) | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3542, c_56])).
% 4.48/1.79  tff(c_3564, plain, (r1_tarski('#skF_4', k1_setfam_1(k1_tarski('#skF_4'))) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3557])).
% 4.48/1.79  tff(c_3565, plain, (r1_tarski('#skF_4', k1_setfam_1(k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_744, c_3564])).
% 4.48/1.79  tff(c_141, plain, (![A_77]: (k3_tarski(k1_tarski(A_77))=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_137])).
% 4.48/1.79  tff(c_147, plain, (![A_77]: (r1_tarski(k1_setfam_1(k1_tarski(A_77)), A_77))), inference(superposition, [status(thm), theory('equality')], [c_141, c_54])).
% 4.48/1.79  tff(c_161, plain, (![A_77]: (k1_setfam_1(k1_tarski(A_77))=A_77 | ~r1_tarski(A_77, k1_setfam_1(k1_tarski(A_77))))), inference(resolution, [status(thm)], [c_147, c_154])).
% 4.48/1.79  tff(c_3622, plain, (k1_setfam_1(k1_tarski('#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_3565, c_161])).
% 4.48/1.79  tff(c_3631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3622])).
% 4.48/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.79  
% 4.48/1.79  Inference rules
% 4.48/1.79  ----------------------
% 4.48/1.79  #Ref     : 0
% 4.48/1.79  #Sup     : 858
% 4.48/1.79  #Fact    : 0
% 4.48/1.79  #Define  : 0
% 4.48/1.79  #Split   : 0
% 4.48/1.79  #Chain   : 0
% 4.48/1.79  #Close   : 0
% 4.48/1.79  
% 4.48/1.79  Ordering : KBO
% 4.48/1.79  
% 4.48/1.79  Simplification rules
% 4.48/1.79  ----------------------
% 4.48/1.79  #Subsume      : 13
% 4.48/1.79  #Demod        : 720
% 4.48/1.79  #Tautology    : 579
% 4.48/1.79  #SimpNegUnit  : 8
% 4.48/1.79  #BackRed      : 7
% 4.48/1.79  
% 4.48/1.79  #Partial instantiations: 0
% 4.48/1.79  #Strategies tried      : 1
% 4.48/1.79  
% 4.48/1.79  Timing (in seconds)
% 4.48/1.79  ----------------------
% 4.48/1.79  Preprocessing        : 0.34
% 4.48/1.79  Parsing              : 0.18
% 4.48/1.79  CNF conversion       : 0.02
% 4.48/1.79  Main loop            : 0.71
% 4.48/1.79  Inferencing          : 0.25
% 4.48/1.79  Reduction            : 0.30
% 4.48/1.79  Demodulation         : 0.24
% 4.48/1.79  BG Simplification    : 0.03
% 4.48/1.79  Subsumption          : 0.09
% 4.48/1.79  Abstraction          : 0.04
% 4.48/1.79  MUC search           : 0.00
% 4.48/1.79  Cooper               : 0.00
% 4.48/1.79  Total                : 1.07
% 4.48/1.79  Index Insertion      : 0.00
% 4.48/1.79  Index Deletion       : 0.00
% 4.48/1.79  Index Matching       : 0.00
% 4.48/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
