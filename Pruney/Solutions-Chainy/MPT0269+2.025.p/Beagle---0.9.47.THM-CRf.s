%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:47 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 239 expanded)
%              Number of leaves         :   41 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :   85 ( 252 expanded)
%              Number of equality atoms :   54 ( 217 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_89,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tarski(A_56),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_417,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k2_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3316,plain,(
    ! [A_4315,B_4316] : k5_xboole_0(A_4315,k5_xboole_0(B_4316,k2_xboole_0(A_4315,B_4316))) = k3_xboole_0(A_4315,B_4316) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_28])).

tff(c_62,plain,(
    ! [A_60] : k3_tarski(k1_tarski(A_60)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_159,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_168,plain,(
    ! [A_28] : k3_tarski(k1_tarski(A_28)) = k2_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_159])).

tff(c_171,plain,(
    ! [A_28] : k2_xboole_0(A_28,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_168])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_300,plain,(
    ! [A_104,B_105] : k5_xboole_0(k5_xboole_0(A_104,B_105),k2_xboole_0(A_104,B_105)) = k3_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_324,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,A_20)) = k3_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_300])).

tff(c_328,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_8,c_324])).

tff(c_485,plain,(
    ! [A_20,C_111] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_417])).

tff(c_498,plain,(
    ! [A_20,C_111] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_485])).

tff(c_3331,plain,(
    ! [B_4316,A_4315] : k5_xboole_0(B_4316,k2_xboole_0(A_4315,B_4316)) = k5_xboole_0(A_4315,k3_xboole_0(A_4315,B_4316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3316,c_498])).

tff(c_3401,plain,(
    ! [B_4369,A_4370] : k5_xboole_0(B_4369,k2_xboole_0(A_4370,B_4369)) = k4_xboole_0(A_4370,B_4369) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3331])).

tff(c_3521,plain,(
    ! [B_4477,A_4478] : k5_xboole_0(B_4477,k4_xboole_0(A_4478,B_4477)) = k2_xboole_0(A_4478,B_4477) ),
    inference(superposition,[status(thm),theory(equality)],[c_3401,c_498])).

tff(c_3583,plain,(
    k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k2_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_3521])).

tff(c_3595,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3583])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_220,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_228,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(k2_xboole_0(A_15,B_16),A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_220])).

tff(c_3609,plain,
    ( k2_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3595,c_228])).

tff(c_3677,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3595,c_3609])).

tff(c_3678,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3677])).

tff(c_3693,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_3678])).

tff(c_3612,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3595,c_22])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_260,plain,(
    ! [C_94,B_95,A_96] :
      ( r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_282,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_2'(A_100),B_101)
      | ~ r1_tarski(A_100,B_101)
      | k1_xboole_0 = A_100 ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_30,plain,(
    ! [C_27,A_23] :
      ( C_27 = A_23
      | ~ r2_hidden(C_27,k1_tarski(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_293,plain,(
    ! [A_23,A_100] :
      ( A_23 = '#skF_2'(A_100)
      | ~ r1_tarski(A_100,k1_tarski(A_23))
      | k1_xboole_0 = A_100 ) ),
    inference(resolution,[status(thm)],[c_282,c_30])).

tff(c_3697,plain,
    ( '#skF_2'('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3612,c_293])).

tff(c_3743,plain,(
    '#skF_2'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3697])).

tff(c_3755,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3743,c_10])).

tff(c_3760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3693,c_3755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.84  
% 4.61/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.85  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 4.61/1.85  
% 4.61/1.85  %Foreground sorts:
% 4.61/1.85  
% 4.61/1.85  
% 4.61/1.85  %Background operators:
% 4.61/1.85  
% 4.61/1.85  
% 4.61/1.85  %Foreground operators:
% 4.61/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.61/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.61/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.61/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.61/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.61/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.61/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.61/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.61/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.61/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.61/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.61/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.61/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.61/1.85  
% 4.81/1.86  tff(f_99, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.81/1.86  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.81/1.86  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.81/1.86  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.81/1.86  tff(f_56, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.81/1.86  tff(f_60, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.81/1.86  tff(f_89, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 4.81/1.86  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.81/1.86  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.81/1.86  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.81/1.86  tff(f_58, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.81/1.86  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.81/1.86  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.81/1.86  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.81/1.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.81/1.86  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.81/1.86  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.81/1.86  tff(c_58, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), B_57) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.81/1.86  tff(c_64, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.81/1.86  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.81/1.86  tff(c_68, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.81/1.86  tff(c_18, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.81/1.86  tff(c_417, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.81/1.86  tff(c_28, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k2_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.81/1.86  tff(c_3316, plain, (![A_4315, B_4316]: (k5_xboole_0(A_4315, k5_xboole_0(B_4316, k2_xboole_0(A_4315, B_4316)))=k3_xboole_0(A_4315, B_4316))), inference(superposition, [status(thm), theory('equality')], [c_417, c_28])).
% 4.81/1.86  tff(c_62, plain, (![A_60]: (k3_tarski(k1_tarski(A_60))=A_60)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.81/1.86  tff(c_42, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.81/1.86  tff(c_159, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.81/1.86  tff(c_168, plain, (![A_28]: (k3_tarski(k1_tarski(A_28))=k2_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_42, c_159])).
% 4.81/1.86  tff(c_171, plain, (![A_28]: (k2_xboole_0(A_28, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_168])).
% 4.81/1.86  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.81/1.86  tff(c_26, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.81/1.86  tff(c_300, plain, (![A_104, B_105]: (k5_xboole_0(k5_xboole_0(A_104, B_105), k2_xboole_0(A_104, B_105))=k3_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.81/1.86  tff(c_324, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, A_20))=k3_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_26, c_300])).
% 4.81/1.86  tff(c_328, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_8, c_324])).
% 4.81/1.86  tff(c_485, plain, (![A_20, C_111]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_26, c_417])).
% 4.81/1.86  tff(c_498, plain, (![A_20, C_111]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_485])).
% 4.81/1.86  tff(c_3331, plain, (![B_4316, A_4315]: (k5_xboole_0(B_4316, k2_xboole_0(A_4315, B_4316))=k5_xboole_0(A_4315, k3_xboole_0(A_4315, B_4316)))), inference(superposition, [status(thm), theory('equality')], [c_3316, c_498])).
% 4.81/1.86  tff(c_3401, plain, (![B_4369, A_4370]: (k5_xboole_0(B_4369, k2_xboole_0(A_4370, B_4369))=k4_xboole_0(A_4370, B_4369))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3331])).
% 4.81/1.86  tff(c_3521, plain, (![B_4477, A_4478]: (k5_xboole_0(B_4477, k4_xboole_0(A_4478, B_4477))=k2_xboole_0(A_4478, B_4477))), inference(superposition, [status(thm), theory('equality')], [c_3401, c_498])).
% 4.81/1.86  tff(c_3583, plain, (k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k2_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_3521])).
% 4.81/1.86  tff(c_3595, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3583])).
% 4.81/1.86  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.81/1.86  tff(c_220, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.81/1.86  tff(c_228, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(k2_xboole_0(A_15, B_16), A_15))), inference(resolution, [status(thm)], [c_22, c_220])).
% 4.81/1.86  tff(c_3609, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3595, c_228])).
% 4.81/1.86  tff(c_3677, plain, (k1_tarski('#skF_6')='#skF_5' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3595, c_3609])).
% 4.81/1.86  tff(c_3678, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_3677])).
% 4.81/1.86  tff(c_3693, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_3678])).
% 4.81/1.86  tff(c_3612, plain, (r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3595, c_22])).
% 4.81/1.86  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.81/1.86  tff(c_260, plain, (![C_94, B_95, A_96]: (r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.86  tff(c_282, plain, (![A_100, B_101]: (r2_hidden('#skF_2'(A_100), B_101) | ~r1_tarski(A_100, B_101) | k1_xboole_0=A_100)), inference(resolution, [status(thm)], [c_10, c_260])).
% 4.81/1.86  tff(c_30, plain, (![C_27, A_23]: (C_27=A_23 | ~r2_hidden(C_27, k1_tarski(A_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.81/1.86  tff(c_293, plain, (![A_23, A_100]: (A_23='#skF_2'(A_100) | ~r1_tarski(A_100, k1_tarski(A_23)) | k1_xboole_0=A_100)), inference(resolution, [status(thm)], [c_282, c_30])).
% 4.81/1.86  tff(c_3697, plain, ('#skF_2'('#skF_5')='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3612, c_293])).
% 4.81/1.86  tff(c_3743, plain, ('#skF_2'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_66, c_3697])).
% 4.81/1.86  tff(c_3755, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3743, c_10])).
% 4.81/1.86  tff(c_3760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3693, c_3755])).
% 4.81/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.86  
% 4.81/1.86  Inference rules
% 4.81/1.86  ----------------------
% 4.81/1.86  #Ref     : 0
% 4.81/1.86  #Sup     : 686
% 4.81/1.86  #Fact    : 0
% 4.81/1.86  #Define  : 0
% 4.81/1.86  #Split   : 2
% 4.81/1.86  #Chain   : 0
% 4.81/1.86  #Close   : 0
% 4.81/1.86  
% 4.81/1.86  Ordering : KBO
% 4.81/1.86  
% 4.81/1.86  Simplification rules
% 4.81/1.86  ----------------------
% 4.81/1.86  #Subsume      : 19
% 4.81/1.86  #Demod        : 432
% 4.81/1.86  #Tautology    : 443
% 4.81/1.86  #SimpNegUnit  : 7
% 4.81/1.86  #BackRed      : 2
% 4.81/1.86  
% 4.81/1.86  #Partial instantiations: 1740
% 4.81/1.86  #Strategies tried      : 1
% 4.81/1.86  
% 4.81/1.86  Timing (in seconds)
% 4.81/1.86  ----------------------
% 4.81/1.86  Preprocessing        : 0.35
% 4.81/1.86  Parsing              : 0.18
% 4.81/1.86  CNF conversion       : 0.03
% 4.81/1.86  Main loop            : 0.74
% 4.81/1.86  Inferencing          : 0.32
% 4.81/1.86  Reduction            : 0.25
% 4.81/1.86  Demodulation         : 0.20
% 4.81/1.86  BG Simplification    : 0.03
% 4.81/1.86  Subsumption          : 0.10
% 4.81/1.86  Abstraction          : 0.03
% 4.81/1.86  MUC search           : 0.00
% 4.81/1.87  Cooper               : 0.00
% 4.81/1.87  Total                : 1.12
% 4.81/1.87  Index Insertion      : 0.00
% 4.81/1.87  Index Deletion       : 0.00
% 4.81/1.87  Index Matching       : 0.00
% 4.81/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
