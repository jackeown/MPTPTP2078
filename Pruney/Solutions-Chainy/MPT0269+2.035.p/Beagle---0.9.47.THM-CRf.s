%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:48 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 243 expanded)
%              Number of leaves         :   43 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 ( 259 expanded)
%              Number of equality atoms :   55 ( 218 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_95,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_93,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_60,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tarski(A_58),B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_18,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_583,plain,(
    ! [A_125,B_126] : k5_xboole_0(k5_xboole_0(A_125,B_126),k2_xboole_0(A_125,B_126)) = k3_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] : k5_xboole_0(k5_xboole_0(A_19,B_20),C_21) = k5_xboole_0(A_19,k5_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3269,plain,(
    ! [A_4266,B_4267] : k5_xboole_0(A_4266,k5_xboole_0(B_4267,k2_xboole_0(A_4266,B_4267))) = k3_xboole_0(A_4266,B_4267) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_26])).

tff(c_64,plain,(
    ! [A_62] : k3_tarski(k1_tarski(A_62)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_166,plain,(
    ! [A_87,B_88] : k3_tarski(k2_tarski(A_87,B_88)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_175,plain,(
    ! [A_30] : k3_tarski(k1_tarski(A_30)) = k2_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_166])).

tff(c_178,plain,(
    ! [A_30] : k2_xboole_0(A_30,A_30) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_175])).

tff(c_14,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_635,plain,(
    ! [A_22] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_22,A_22)) = k3_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_583])).

tff(c_639,plain,(
    ! [A_22] : k5_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_14,c_635])).

tff(c_344,plain,(
    ! [A_117,B_118,C_119] : k5_xboole_0(k5_xboole_0(A_117,B_118),C_119) = k5_xboole_0(A_117,k5_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_385,plain,(
    ! [A_22,C_119] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_119)) = k5_xboole_0(k1_xboole_0,C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_344])).

tff(c_640,plain,(
    ! [A_22,C_119] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_119)) = C_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_385])).

tff(c_3284,plain,(
    ! [B_4267,A_4266] : k5_xboole_0(B_4267,k2_xboole_0(A_4266,B_4267)) = k5_xboole_0(A_4266,k3_xboole_0(A_4266,B_4267)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3269,c_640])).

tff(c_3354,plain,(
    ! [B_4320,A_4321] : k5_xboole_0(B_4320,k2_xboole_0(A_4321,B_4320)) = k4_xboole_0(A_4321,B_4320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3284])).

tff(c_3474,plain,(
    ! [B_4428,A_4429] : k5_xboole_0(B_4428,k4_xboole_0(A_4429,B_4428)) = k2_xboole_0(A_4429,B_4428) ),
    inference(superposition,[status(thm),theory(equality)],[c_3354,c_640])).

tff(c_3536,plain,(
    k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k2_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3474])).

tff(c_3548,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3536])).

tff(c_24,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_243,plain,(
    ! [A_97,B_98] :
      ( r2_xboole_0(A_97,B_98)
      | B_98 = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( ~ r2_xboole_0(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_267,plain,(
    ! [B_101,A_102] :
      ( ~ r1_tarski(B_101,A_102)
      | B_101 = A_102
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(resolution,[status(thm)],[c_243,c_22])).

tff(c_279,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(k2_xboole_0(A_17,B_18),A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_267])).

tff(c_3670,plain,
    ( k2_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3548,c_279])).

tff(c_3738,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_3670])).

tff(c_3739,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3738])).

tff(c_3754,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_3739])).

tff(c_3673,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3548,c_24])).

tff(c_16,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_289,plain,(
    ! [C_106,B_107,A_108] :
      ( r2_hidden(C_106,B_107)
      | ~ r2_hidden(C_106,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_326,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_2'(A_113),B_114)
      | ~ r1_tarski(A_113,B_114)
      | k1_xboole_0 = A_113 ) ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_32,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4573,plain,(
    ! [A_14735,A_14736] :
      ( A_14735 = '#skF_2'(A_14736)
      | ~ r1_tarski(A_14736,k1_tarski(A_14735))
      | k1_xboole_0 = A_14736 ) ),
    inference(resolution,[status(thm)],[c_326,c_32])).

tff(c_4578,plain,
    ( '#skF_2'('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3673,c_4573])).

tff(c_4597,plain,(
    '#skF_2'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4578])).

tff(c_4631,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4597,c_16])).

tff(c_4636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3754,c_4631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.98  
% 4.89/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.98  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 4.89/1.98  
% 4.89/1.98  %Foreground sorts:
% 4.89/1.98  
% 4.89/1.98  
% 4.89/1.98  %Background operators:
% 4.89/1.98  
% 4.89/1.98  
% 4.89/1.98  %Foreground operators:
% 4.89/1.98  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.89/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.89/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.89/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.89/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.89/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.89/1.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.89/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.89/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.89/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.89/1.98  tff('#skF_5', type, '#skF_5': $i).
% 4.89/1.98  tff('#skF_6', type, '#skF_6': $i).
% 4.89/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.89/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.98  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.89/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.89/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.89/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.89/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.89/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.89/1.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.89/1.98  
% 5.21/1.99  tff(f_105, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 5.21/1.99  tff(f_91, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.21/1.99  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.21/1.99  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.21/1.99  tff(f_66, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.21/1.99  tff(f_62, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.21/1.99  tff(f_95, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 5.21/1.99  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.21/1.99  tff(f_93, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.21/1.99  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.21/1.99  tff(f_64, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.21/1.99  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.21/1.99  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.21/1.99  tff(f_58, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 5.21/1.99  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.21/1.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.21/1.99  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.21/1.99  tff(c_68, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.21/1.99  tff(c_60, plain, (![A_58, B_59]: (r1_tarski(k1_tarski(A_58), B_59) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.21/1.99  tff(c_66, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.21/1.99  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.21/1.99  tff(c_70, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.21/1.99  tff(c_18, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.21/1.99  tff(c_583, plain, (![A_125, B_126]: (k5_xboole_0(k5_xboole_0(A_125, B_126), k2_xboole_0(A_125, B_126))=k3_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.21/1.99  tff(c_26, plain, (![A_19, B_20, C_21]: (k5_xboole_0(k5_xboole_0(A_19, B_20), C_21)=k5_xboole_0(A_19, k5_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.21/1.99  tff(c_3269, plain, (![A_4266, B_4267]: (k5_xboole_0(A_4266, k5_xboole_0(B_4267, k2_xboole_0(A_4266, B_4267)))=k3_xboole_0(A_4266, B_4267))), inference(superposition, [status(thm), theory('equality')], [c_583, c_26])).
% 5.21/1.99  tff(c_64, plain, (![A_62]: (k3_tarski(k1_tarski(A_62))=A_62)), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.21/1.99  tff(c_44, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.21/1.99  tff(c_166, plain, (![A_87, B_88]: (k3_tarski(k2_tarski(A_87, B_88))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.21/1.99  tff(c_175, plain, (![A_30]: (k3_tarski(k1_tarski(A_30))=k2_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_44, c_166])).
% 5.21/1.99  tff(c_178, plain, (![A_30]: (k2_xboole_0(A_30, A_30)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_175])).
% 5.21/1.99  tff(c_14, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.21/1.99  tff(c_28, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.21/1.99  tff(c_635, plain, (![A_22]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_22, A_22))=k3_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_28, c_583])).
% 5.21/1.99  tff(c_639, plain, (![A_22]: (k5_xboole_0(k1_xboole_0, A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_14, c_635])).
% 5.21/1.99  tff(c_344, plain, (![A_117, B_118, C_119]: (k5_xboole_0(k5_xboole_0(A_117, B_118), C_119)=k5_xboole_0(A_117, k5_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.21/1.99  tff(c_385, plain, (![A_22, C_119]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_119))=k5_xboole_0(k1_xboole_0, C_119))), inference(superposition, [status(thm), theory('equality')], [c_28, c_344])).
% 5.21/1.99  tff(c_640, plain, (![A_22, C_119]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_119))=C_119)), inference(demodulation, [status(thm), theory('equality')], [c_639, c_385])).
% 5.21/1.99  tff(c_3284, plain, (![B_4267, A_4266]: (k5_xboole_0(B_4267, k2_xboole_0(A_4266, B_4267))=k5_xboole_0(A_4266, k3_xboole_0(A_4266, B_4267)))), inference(superposition, [status(thm), theory('equality')], [c_3269, c_640])).
% 5.21/1.99  tff(c_3354, plain, (![B_4320, A_4321]: (k5_xboole_0(B_4320, k2_xboole_0(A_4321, B_4320))=k4_xboole_0(A_4321, B_4320))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3284])).
% 5.21/1.99  tff(c_3474, plain, (![B_4428, A_4429]: (k5_xboole_0(B_4428, k4_xboole_0(A_4429, B_4428))=k2_xboole_0(A_4429, B_4428))), inference(superposition, [status(thm), theory('equality')], [c_3354, c_640])).
% 5.21/1.99  tff(c_3536, plain, (k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k2_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_3474])).
% 5.21/1.99  tff(c_3548, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3536])).
% 5.21/1.99  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.21/1.99  tff(c_243, plain, (![A_97, B_98]: (r2_xboole_0(A_97, B_98) | B_98=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.21/1.99  tff(c_22, plain, (![B_16, A_15]: (~r2_xboole_0(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.21/1.99  tff(c_267, plain, (![B_101, A_102]: (~r1_tarski(B_101, A_102) | B_101=A_102 | ~r1_tarski(A_102, B_101))), inference(resolution, [status(thm)], [c_243, c_22])).
% 5.21/1.99  tff(c_279, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(k2_xboole_0(A_17, B_18), A_17))), inference(resolution, [status(thm)], [c_24, c_267])).
% 5.21/1.99  tff(c_3670, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3548, c_279])).
% 5.21/1.99  tff(c_3738, plain, (k1_tarski('#skF_6')='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_3670])).
% 5.21/1.99  tff(c_3739, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_3738])).
% 5.21/1.99  tff(c_3754, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_3739])).
% 5.21/1.99  tff(c_3673, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3548, c_24])).
% 5.21/1.99  tff(c_16, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.21/1.99  tff(c_289, plain, (![C_106, B_107, A_108]: (r2_hidden(C_106, B_107) | ~r2_hidden(C_106, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.21/1.99  tff(c_326, plain, (![A_113, B_114]: (r2_hidden('#skF_2'(A_113), B_114) | ~r1_tarski(A_113, B_114) | k1_xboole_0=A_113)), inference(resolution, [status(thm)], [c_16, c_289])).
% 5.21/1.99  tff(c_32, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.21/1.99  tff(c_4573, plain, (![A_14735, A_14736]: (A_14735='#skF_2'(A_14736) | ~r1_tarski(A_14736, k1_tarski(A_14735)) | k1_xboole_0=A_14736)), inference(resolution, [status(thm)], [c_326, c_32])).
% 5.21/1.99  tff(c_4578, plain, ('#skF_2'('#skF_5')='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3673, c_4573])).
% 5.21/1.99  tff(c_4597, plain, ('#skF_2'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_68, c_4578])).
% 5.21/1.99  tff(c_4631, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4597, c_16])).
% 5.21/1.99  tff(c_4636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3754, c_4631])).
% 5.21/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.99  
% 5.21/1.99  Inference rules
% 5.21/1.99  ----------------------
% 5.21/1.99  #Ref     : 0
% 5.21/1.99  #Sup     : 821
% 5.21/1.99  #Fact    : 0
% 5.21/1.99  #Define  : 0
% 5.21/1.99  #Split   : 3
% 5.21/1.99  #Chain   : 0
% 5.21/1.99  #Close   : 0
% 5.21/1.99  
% 5.21/1.99  Ordering : KBO
% 5.21/1.99  
% 5.21/1.99  Simplification rules
% 5.21/1.99  ----------------------
% 5.21/1.99  #Subsume      : 28
% 5.21/1.99  #Demod        : 551
% 5.21/1.99  #Tautology    : 541
% 5.21/1.99  #SimpNegUnit  : 12
% 5.21/1.99  #BackRed      : 5
% 5.21/1.99  
% 5.21/1.99  #Partial instantiations: 3650
% 5.21/1.99  #Strategies tried      : 1
% 5.21/1.99  
% 5.21/1.99  Timing (in seconds)
% 5.21/1.99  ----------------------
% 5.21/2.00  Preprocessing        : 0.35
% 5.21/2.00  Parsing              : 0.18
% 5.21/2.00  CNF conversion       : 0.03
% 5.21/2.00  Main loop            : 0.88
% 5.21/2.00  Inferencing          : 0.41
% 5.21/2.00  Reduction            : 0.28
% 5.21/2.00  Demodulation         : 0.22
% 5.21/2.00  BG Simplification    : 0.04
% 5.21/2.00  Subsumption          : 0.11
% 5.21/2.00  Abstraction          : 0.04
% 5.21/2.00  MUC search           : 0.00
% 5.21/2.00  Cooper               : 0.00
% 5.21/2.00  Total                : 1.27
% 5.21/2.00  Index Insertion      : 0.00
% 5.21/2.00  Index Deletion       : 0.00
% 5.21/2.00  Index Matching       : 0.00
% 5.21/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
