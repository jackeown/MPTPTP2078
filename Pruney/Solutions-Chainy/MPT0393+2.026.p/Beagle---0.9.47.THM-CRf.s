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
% DateTime   : Thu Dec  3 09:57:20 EST 2020

% Result     : Theorem 53.62s
% Output     : CNFRefutation 53.62s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 129 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 240 expanded)
%              Number of equality atoms :   39 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(c_74,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1609,plain,(
    ! [A_177,B_178,C_179] :
      ( r2_hidden('#skF_2'(A_177,B_178,C_179),A_177)
      | r2_hidden('#skF_3'(A_177,B_178,C_179),C_179)
      | k4_xboole_0(A_177,B_178) = C_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1669,plain,(
    ! [A_177,C_179] :
      ( r2_hidden('#skF_3'(A_177,A_177,C_179),C_179)
      | k4_xboole_0(A_177,A_177) = C_179 ) ),
    inference(resolution,[status(thm)],[c_1609,c_22])).

tff(c_2512,plain,(
    ! [A_2174,C_2175] :
      ( r2_hidden('#skF_3'(A_2174,A_2174,C_2175),C_2175)
      | k4_xboole_0(A_2174,A_2174) = C_2175 ) ),
    inference(resolution,[status(thm)],[c_1609,c_22])).

tff(c_32,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_126,plain,(
    ! [D_56,B_57,A_58] :
      ( ~ r2_hidden(D_56,B_57)
      | ~ r2_hidden(D_56,k4_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_133,plain,(
    ! [D_56,A_14] :
      ( ~ r2_hidden(D_56,k1_xboole_0)
      | ~ r2_hidden(D_56,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_126])).

tff(c_3391,plain,(
    ! [A_4298,A_4299] :
      ( ~ r2_hidden('#skF_3'(A_4298,A_4298,k1_xboole_0),A_4299)
      | k4_xboole_0(A_4298,A_4298) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2512,c_133])).

tff(c_3423,plain,(
    ! [A_177] : k4_xboole_0(A_177,A_177) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1669,c_3391])).

tff(c_58,plain,(
    ! [B_28] : k4_xboole_0(k1_tarski(B_28),k1_tarski(B_28)) != k1_tarski(B_28) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3431,plain,(
    ! [B_28] : k1_tarski(B_28) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3423,c_58])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_538,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_6'(A_114,B_115),A_114)
      | r1_tarski(B_115,k1_setfam_1(A_114))
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_222,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(k1_tarski(A_75),k1_tarski(B_76)) = k1_tarski(A_75)
      | B_76 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,(
    ! [C_31,B_30] : ~ r2_hidden(C_31,k4_xboole_0(B_30,k1_tarski(C_31))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_238,plain,(
    ! [B_76,A_75] :
      ( ~ r2_hidden(B_76,k1_tarski(A_75))
      | B_76 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_64])).

tff(c_565,plain,(
    ! [A_75,B_115] :
      ( '#skF_6'(k1_tarski(A_75),B_115) = A_75
      | r1_tarski(B_115,k1_setfam_1(k1_tarski(A_75)))
      | k1_tarski(A_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_538,c_238])).

tff(c_277550,plain,(
    ! [A_63468,B_63469] :
      ( '#skF_6'(k1_tarski(A_63468),B_63469) = A_63468
      | r1_tarski(B_63469,k1_setfam_1(k1_tarski(A_63468))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3431,c_565])).

tff(c_88,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_36])).

tff(c_120,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4282,plain,(
    ! [A_5200,B_5201,B_5202] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_5200,B_5201),B_5202),A_5200)
      | r1_tarski(k4_xboole_0(A_5200,B_5201),B_5202) ) ),
    inference(resolution,[status(thm)],[c_120,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4341,plain,(
    ! [A_5261,B_5262] : r1_tarski(k4_xboole_0(A_5261,B_5262),A_5261) ),
    inference(resolution,[status(thm)],[c_4282,c_4])).

tff(c_72,plain,(
    ! [B_36,C_37,A_35] :
      ( r1_tarski(k1_setfam_1(B_36),C_37)
      | ~ r1_tarski(A_35,C_37)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4391,plain,(
    ! [B_5321,A_5322,B_5323] :
      ( r1_tarski(k1_setfam_1(B_5321),A_5322)
      | ~ r2_hidden(k4_xboole_0(A_5322,B_5323),B_5321) ) ),
    inference(resolution,[status(thm)],[c_4341,c_72])).

tff(c_4431,plain,(
    ! [A_5382,B_5383] : r1_tarski(k1_setfam_1(k1_tarski(k4_xboole_0(A_5382,B_5383))),A_5382) ),
    inference(resolution,[status(thm)],[c_94,c_4391])).

tff(c_4483,plain,(
    ! [A_5442] : r1_tarski(k1_setfam_1(k1_tarski(A_5442)),A_5442) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4431])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4524,plain,(
    ! [A_5442] :
      ( k1_setfam_1(k1_tarski(A_5442)) = A_5442
      | ~ r1_tarski(A_5442,k1_setfam_1(k1_tarski(A_5442))) ) ),
    inference(resolution,[status(thm)],[c_4483,c_26])).

tff(c_284526,plain,(
    ! [A_64360] :
      ( k1_setfam_1(k1_tarski(A_64360)) = A_64360
      | '#skF_6'(k1_tarski(A_64360),A_64360) = A_64360 ) ),
    inference(resolution,[status(thm)],[c_277550,c_4524])).

tff(c_285617,plain,(
    '#skF_6'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_284526,c_74])).

tff(c_68,plain,(
    ! [B_33,A_32] :
      ( ~ r1_tarski(B_33,'#skF_6'(A_32,B_33))
      | r1_tarski(B_33,k1_setfam_1(A_32))
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_285636,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7')))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_285617,c_68])).

tff(c_285679,plain,
    ( r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7')))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_285636])).

tff(c_285680,plain,(
    r1_tarski('#skF_7',k1_setfam_1(k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3431,c_285679])).

tff(c_285710,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_285680,c_4524])).

tff(c_285791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_285710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:03:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 53.62/43.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.62/43.36  
% 53.62/43.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.62/43.36  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 53.62/43.36  
% 53.62/43.36  %Foreground sorts:
% 53.62/43.36  
% 53.62/43.36  
% 53.62/43.36  %Background operators:
% 53.62/43.36  
% 53.62/43.36  
% 53.62/43.36  %Foreground operators:
% 53.62/43.36  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 53.62/43.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 53.62/43.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 53.62/43.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 53.62/43.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 53.62/43.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 53.62/43.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 53.62/43.36  tff('#skF_7', type, '#skF_7': $i).
% 53.62/43.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 53.62/43.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 53.62/43.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 53.62/43.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 53.62/43.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 53.62/43.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 53.62/43.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 53.62/43.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 53.62/43.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 53.62/43.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 53.62/43.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 53.62/43.36  
% 53.62/43.38  tff(f_95, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 53.62/43.38  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 53.62/43.38  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 53.62/43.38  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 53.62/43.38  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 53.62/43.38  tff(f_86, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 53.62/43.38  tff(f_77, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 53.62/43.38  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 53.62/43.38  tff(f_59, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 53.62/43.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 53.62/43.38  tff(f_92, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 53.62/43.38  tff(c_74, plain, (k1_setfam_1(k1_tarski('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_95])).
% 53.62/43.38  tff(c_1609, plain, (![A_177, B_178, C_179]: (r2_hidden('#skF_2'(A_177, B_178, C_179), A_177) | r2_hidden('#skF_3'(A_177, B_178, C_179), C_179) | k4_xboole_0(A_177, B_178)=C_179)), inference(cnfTransformation, [status(thm)], [f_42])).
% 53.62/43.38  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 53.62/43.38  tff(c_1669, plain, (![A_177, C_179]: (r2_hidden('#skF_3'(A_177, A_177, C_179), C_179) | k4_xboole_0(A_177, A_177)=C_179)), inference(resolution, [status(thm)], [c_1609, c_22])).
% 53.62/43.38  tff(c_2512, plain, (![A_2174, C_2175]: (r2_hidden('#skF_3'(A_2174, A_2174, C_2175), C_2175) | k4_xboole_0(A_2174, A_2174)=C_2175)), inference(resolution, [status(thm)], [c_1609, c_22])).
% 53.62/43.38  tff(c_32, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 53.62/43.38  tff(c_126, plain, (![D_56, B_57, A_58]: (~r2_hidden(D_56, B_57) | ~r2_hidden(D_56, k4_xboole_0(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 53.62/43.38  tff(c_133, plain, (![D_56, A_14]: (~r2_hidden(D_56, k1_xboole_0) | ~r2_hidden(D_56, A_14))), inference(superposition, [status(thm), theory('equality')], [c_32, c_126])).
% 53.62/43.38  tff(c_3391, plain, (![A_4298, A_4299]: (~r2_hidden('#skF_3'(A_4298, A_4298, k1_xboole_0), A_4299) | k4_xboole_0(A_4298, A_4298)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2512, c_133])).
% 53.62/43.38  tff(c_3423, plain, (![A_177]: (k4_xboole_0(A_177, A_177)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1669, c_3391])).
% 53.62/43.38  tff(c_58, plain, (![B_28]: (k4_xboole_0(k1_tarski(B_28), k1_tarski(B_28))!=k1_tarski(B_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 53.62/43.38  tff(c_3431, plain, (![B_28]: (k1_tarski(B_28)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3423, c_58])).
% 53.62/43.38  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 53.62/43.38  tff(c_538, plain, (![A_114, B_115]: (r2_hidden('#skF_6'(A_114, B_115), A_114) | r1_tarski(B_115, k1_setfam_1(A_114)) | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.62/43.38  tff(c_222, plain, (![A_75, B_76]: (k4_xboole_0(k1_tarski(A_75), k1_tarski(B_76))=k1_tarski(A_75) | B_76=A_75)), inference(cnfTransformation, [status(thm)], [f_70])).
% 53.62/43.38  tff(c_64, plain, (![C_31, B_30]: (~r2_hidden(C_31, k4_xboole_0(B_30, k1_tarski(C_31))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 53.62/43.38  tff(c_238, plain, (![B_76, A_75]: (~r2_hidden(B_76, k1_tarski(A_75)) | B_76=A_75)), inference(superposition, [status(thm), theory('equality')], [c_222, c_64])).
% 53.62/43.38  tff(c_565, plain, (![A_75, B_115]: ('#skF_6'(k1_tarski(A_75), B_115)=A_75 | r1_tarski(B_115, k1_setfam_1(k1_tarski(A_75))) | k1_tarski(A_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_538, c_238])).
% 53.62/43.38  tff(c_277550, plain, (![A_63468, B_63469]: ('#skF_6'(k1_tarski(A_63468), B_63469)=A_63468 | r1_tarski(B_63469, k1_setfam_1(k1_tarski(A_63468))))), inference(negUnitSimplification, [status(thm)], [c_3431, c_565])).
% 53.62/43.38  tff(c_88, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 53.62/43.38  tff(c_36, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 53.62/43.38  tff(c_94, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_36])).
% 53.62/43.38  tff(c_120, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 53.62/43.38  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 53.62/43.38  tff(c_4282, plain, (![A_5200, B_5201, B_5202]: (r2_hidden('#skF_1'(k4_xboole_0(A_5200, B_5201), B_5202), A_5200) | r1_tarski(k4_xboole_0(A_5200, B_5201), B_5202))), inference(resolution, [status(thm)], [c_120, c_12])).
% 53.62/43.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 53.62/43.38  tff(c_4341, plain, (![A_5261, B_5262]: (r1_tarski(k4_xboole_0(A_5261, B_5262), A_5261))), inference(resolution, [status(thm)], [c_4282, c_4])).
% 53.62/43.38  tff(c_72, plain, (![B_36, C_37, A_35]: (r1_tarski(k1_setfam_1(B_36), C_37) | ~r1_tarski(A_35, C_37) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 53.62/43.38  tff(c_4391, plain, (![B_5321, A_5322, B_5323]: (r1_tarski(k1_setfam_1(B_5321), A_5322) | ~r2_hidden(k4_xboole_0(A_5322, B_5323), B_5321))), inference(resolution, [status(thm)], [c_4341, c_72])).
% 53.62/43.38  tff(c_4431, plain, (![A_5382, B_5383]: (r1_tarski(k1_setfam_1(k1_tarski(k4_xboole_0(A_5382, B_5383))), A_5382))), inference(resolution, [status(thm)], [c_94, c_4391])).
% 53.62/43.38  tff(c_4483, plain, (![A_5442]: (r1_tarski(k1_setfam_1(k1_tarski(A_5442)), A_5442))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4431])).
% 53.62/43.38  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 53.62/43.38  tff(c_4524, plain, (![A_5442]: (k1_setfam_1(k1_tarski(A_5442))=A_5442 | ~r1_tarski(A_5442, k1_setfam_1(k1_tarski(A_5442))))), inference(resolution, [status(thm)], [c_4483, c_26])).
% 53.62/43.38  tff(c_284526, plain, (![A_64360]: (k1_setfam_1(k1_tarski(A_64360))=A_64360 | '#skF_6'(k1_tarski(A_64360), A_64360)=A_64360)), inference(resolution, [status(thm)], [c_277550, c_4524])).
% 53.62/43.38  tff(c_285617, plain, ('#skF_6'(k1_tarski('#skF_7'), '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_284526, c_74])).
% 53.62/43.38  tff(c_68, plain, (![B_33, A_32]: (~r1_tarski(B_33, '#skF_6'(A_32, B_33)) | r1_tarski(B_33, k1_setfam_1(A_32)) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.62/43.38  tff(c_285636, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7'))) | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_285617, c_68])).
% 53.62/43.38  tff(c_285679, plain, (r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7'))) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_285636])).
% 53.62/43.38  tff(c_285680, plain, (r1_tarski('#skF_7', k1_setfam_1(k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_3431, c_285679])).
% 53.62/43.38  tff(c_285710, plain, (k1_setfam_1(k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_285680, c_4524])).
% 53.62/43.38  tff(c_285791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_285710])).
% 53.62/43.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.62/43.38  
% 53.62/43.38  Inference rules
% 53.62/43.38  ----------------------
% 53.62/43.38  #Ref     : 0
% 53.62/43.38  #Sup     : 67915
% 53.62/43.38  #Fact    : 68
% 53.62/43.38  #Define  : 0
% 53.62/43.38  #Split   : 14
% 53.62/43.38  #Chain   : 0
% 53.62/43.38  #Close   : 0
% 53.62/43.38  
% 53.62/43.38  Ordering : KBO
% 53.62/43.38  
% 53.62/43.38  Simplification rules
% 53.62/43.38  ----------------------
% 53.62/43.38  #Subsume      : 33146
% 53.62/43.38  #Demod        : 41830
% 53.62/43.38  #Tautology    : 18850
% 53.62/43.38  #SimpNegUnit  : 708
% 53.62/43.38  #BackRed      : 4
% 53.62/43.38  
% 53.62/43.38  #Partial instantiations: 30310
% 53.62/43.38  #Strategies tried      : 1
% 53.62/43.38  
% 53.62/43.38  Timing (in seconds)
% 53.62/43.38  ----------------------
% 53.62/43.38  Preprocessing        : 0.32
% 53.62/43.38  Parsing              : 0.16
% 53.62/43.38  CNF conversion       : 0.03
% 53.62/43.38  Main loop            : 42.30
% 53.62/43.38  Inferencing          : 5.68
% 53.62/43.39  Reduction            : 13.36
% 53.62/43.39  Demodulation         : 10.54
% 53.62/43.39  BG Simplification    : 0.52
% 53.62/43.39  Subsumption          : 21.36
% 53.62/43.39  Abstraction          : 1.01
% 53.62/43.39  MUC search           : 0.00
% 53.62/43.39  Cooper               : 0.00
% 53.62/43.39  Total                : 42.66
% 53.62/43.39  Index Insertion      : 0.00
% 53.62/43.39  Index Deletion       : 0.00
% 53.62/43.39  Index Matching       : 0.00
% 53.62/43.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
