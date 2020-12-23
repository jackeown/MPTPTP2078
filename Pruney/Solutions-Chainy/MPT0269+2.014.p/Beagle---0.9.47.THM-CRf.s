%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:45 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 237 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 318 expanded)
%              Number of equality atoms :   51 ( 231 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_66,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_236,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_254,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = k4_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_236])).

tff(c_258,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_254])).

tff(c_82,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_336,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_368,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_336])).

tff(c_376,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_368])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_466,plain,(
    ! [D_77,A_78,B_79] :
      ( r2_hidden(D_77,A_78)
      | ~ r2_hidden(D_77,k4_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_551,plain,(
    ! [D_91,A_92,B_93] :
      ( r2_hidden(D_91,A_92)
      | ~ r2_hidden(D_91,k3_xboole_0(A_92,B_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_466])).

tff(c_623,plain,(
    ! [D_96,B_97,A_98] :
      ( r2_hidden(D_96,B_97)
      | ~ r2_hidden(D_96,k3_xboole_0(A_98,B_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_551])).

tff(c_648,plain,(
    ! [D_99] :
      ( r2_hidden(D_99,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_99,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_623])).

tff(c_54,plain,(
    ! [C_28,A_24] :
      ( C_28 = A_24
      | ~ r2_hidden(C_28,k1_tarski(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_653,plain,(
    ! [D_100] :
      ( D_100 = '#skF_7'
      | ~ r2_hidden(D_100,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_648,c_54])).

tff(c_657,plain,
    ( '#skF_3'('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_653])).

tff(c_660,plain,(
    '#skF_3'('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_657])).

tff(c_664,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_34])).

tff(c_667,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_664])).

tff(c_78,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_541,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_777,plain,(
    ! [B_119,A_120] :
      ( B_119 = A_120
      | ~ r1_tarski(B_119,A_120)
      | k4_xboole_0(A_120,B_119) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_541])).

tff(c_1443,plain,(
    ! [B_144,A_145] :
      ( B_144 = A_145
      | k4_xboole_0(B_144,A_145) != k1_xboole_0
      | k4_xboole_0(A_145,B_144) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_777])).

tff(c_1459,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1443])).

tff(c_1472,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1459])).

tff(c_811,plain,(
    ! [A_124,B_125] : k4_xboole_0(A_124,k3_xboole_0(A_124,B_125)) = k3_xboole_0(A_124,k4_xboole_0(A_124,B_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_50])).

tff(c_1198,plain,(
    ! [A_140,B_141] : k4_xboole_0(A_140,k3_xboole_0(B_141,A_140)) = k3_xboole_0(A_140,k4_xboole_0(A_140,B_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_811])).

tff(c_1253,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')) = k4_xboole_0(k1_tarski('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_1198])).

tff(c_1507,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_149,B_150)),B_150)
      | k3_xboole_0(A_149,B_150) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_623])).

tff(c_1550,plain,
    ( r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')),k4_xboole_0(k1_tarski('#skF_7'),'#skF_6'))
    | k3_xboole_0(k1_tarski('#skF_7'),k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_1507])).

tff(c_1586,plain,
    ( r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')),k4_xboole_0(k1_tarski('#skF_7'),'#skF_6'))
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_1550])).

tff(c_1587,plain,(
    r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')),k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1472,c_1586])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1667,plain,(
    r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')),k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1587,c_8])).

tff(c_1671,plain,(
    '#skF_3'(k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1667,c_54])).

tff(c_494,plain,(
    ! [D_81,B_82,A_83] :
      ( ~ r2_hidden(D_81,B_82)
      | ~ r2_hidden(D_81,k4_xboole_0(A_83,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_497,plain,(
    ! [D_81,A_21,B_22] :
      ( ~ r2_hidden(D_81,k4_xboole_0(A_21,B_22))
      | ~ r2_hidden(D_81,k3_xboole_0(A_21,B_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_494])).

tff(c_1657,plain,(
    ~ r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')),k3_xboole_0(k1_tarski('#skF_7'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_1587,c_497])).

tff(c_1665,plain,(
    ~ r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'),'#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_2,c_1657])).

tff(c_1673,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1665])).

tff(c_1678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_1673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.53  
% 3.34/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.53  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 3.34/1.53  
% 3.34/1.53  %Foreground sorts:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Background operators:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Foreground operators:
% 3.34/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.34/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.53  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.34/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.34/1.53  
% 3.34/1.55  tff(f_99, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.34/1.55  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.34/1.55  tff(f_70, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.34/1.55  tff(f_66, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.34/1.55  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.55  tff(f_68, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.34/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.34/1.55  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.34/1.55  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.34/1.55  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.34/1.55  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.34/1.55  tff(c_80, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.34/1.55  tff(c_34, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.34/1.55  tff(c_52, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.34/1.55  tff(c_48, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.34/1.55  tff(c_236, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.55  tff(c_254, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=k4_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_236])).
% 3.34/1.55  tff(c_258, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_254])).
% 3.34/1.55  tff(c_82, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.34/1.55  tff(c_336, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.55  tff(c_368, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_336])).
% 3.34/1.55  tff(c_376, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_368])).
% 3.34/1.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.55  tff(c_50, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.55  tff(c_466, plain, (![D_77, A_78, B_79]: (r2_hidden(D_77, A_78) | ~r2_hidden(D_77, k4_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.55  tff(c_551, plain, (![D_91, A_92, B_93]: (r2_hidden(D_91, A_92) | ~r2_hidden(D_91, k3_xboole_0(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_466])).
% 3.34/1.55  tff(c_623, plain, (![D_96, B_97, A_98]: (r2_hidden(D_96, B_97) | ~r2_hidden(D_96, k3_xboole_0(A_98, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_551])).
% 3.34/1.55  tff(c_648, plain, (![D_99]: (r2_hidden(D_99, k1_tarski('#skF_7')) | ~r2_hidden(D_99, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_376, c_623])).
% 3.34/1.55  tff(c_54, plain, (![C_28, A_24]: (C_28=A_24 | ~r2_hidden(C_28, k1_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.34/1.55  tff(c_653, plain, (![D_100]: (D_100='#skF_7' | ~r2_hidden(D_100, '#skF_6'))), inference(resolution, [status(thm)], [c_648, c_54])).
% 3.34/1.55  tff(c_657, plain, ('#skF_3'('#skF_6')='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_34, c_653])).
% 3.34/1.55  tff(c_660, plain, ('#skF_3'('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_80, c_657])).
% 3.34/1.55  tff(c_664, plain, (r2_hidden('#skF_7', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_660, c_34])).
% 3.34/1.55  tff(c_667, plain, (r2_hidden('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_80, c_664])).
% 3.34/1.55  tff(c_78, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.34/1.55  tff(c_42, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.55  tff(c_541, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.55  tff(c_777, plain, (![B_119, A_120]: (B_119=A_120 | ~r1_tarski(B_119, A_120) | k4_xboole_0(A_120, B_119)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_541])).
% 3.34/1.55  tff(c_1443, plain, (![B_144, A_145]: (B_144=A_145 | k4_xboole_0(B_144, A_145)!=k1_xboole_0 | k4_xboole_0(A_145, B_144)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_777])).
% 3.34/1.55  tff(c_1459, plain, (k1_tarski('#skF_7')='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_82, c_1443])).
% 3.34/1.55  tff(c_1472, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_1459])).
% 3.34/1.55  tff(c_811, plain, (![A_124, B_125]: (k4_xboole_0(A_124, k3_xboole_0(A_124, B_125))=k3_xboole_0(A_124, k4_xboole_0(A_124, B_125)))), inference(superposition, [status(thm), theory('equality')], [c_336, c_50])).
% 3.34/1.55  tff(c_1198, plain, (![A_140, B_141]: (k4_xboole_0(A_140, k3_xboole_0(B_141, A_140))=k3_xboole_0(A_140, k4_xboole_0(A_140, B_141)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_811])).
% 3.34/1.55  tff(c_1253, plain, (k3_xboole_0(k1_tarski('#skF_7'), k4_xboole_0(k1_tarski('#skF_7'), '#skF_6'))=k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_376, c_1198])).
% 3.34/1.55  tff(c_1507, plain, (![A_149, B_150]: (r2_hidden('#skF_3'(k3_xboole_0(A_149, B_150)), B_150) | k3_xboole_0(A_149, B_150)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_623])).
% 3.34/1.55  tff(c_1550, plain, (r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')), k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')) | k3_xboole_0(k1_tarski('#skF_7'), k4_xboole_0(k1_tarski('#skF_7'), '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1253, c_1507])).
% 3.34/1.55  tff(c_1586, plain, (r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')), k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')) | k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1253, c_1550])).
% 3.34/1.55  tff(c_1587, plain, (r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')), k4_xboole_0(k1_tarski('#skF_7'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1472, c_1586])).
% 3.34/1.55  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.55  tff(c_1667, plain, (r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')), k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_1587, c_8])).
% 3.34/1.55  tff(c_1671, plain, ('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'), '#skF_6'))='#skF_7'), inference(resolution, [status(thm)], [c_1667, c_54])).
% 3.34/1.55  tff(c_494, plain, (![D_81, B_82, A_83]: (~r2_hidden(D_81, B_82) | ~r2_hidden(D_81, k4_xboole_0(A_83, B_82)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.55  tff(c_497, plain, (![D_81, A_21, B_22]: (~r2_hidden(D_81, k4_xboole_0(A_21, B_22)) | ~r2_hidden(D_81, k3_xboole_0(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_494])).
% 3.34/1.55  tff(c_1657, plain, (~r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')), k3_xboole_0(k1_tarski('#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_1587, c_497])).
% 3.34/1.55  tff(c_1665, plain, (~r2_hidden('#skF_3'(k4_xboole_0(k1_tarski('#skF_7'), '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_2, c_1657])).
% 3.34/1.55  tff(c_1673, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1665])).
% 3.34/1.55  tff(c_1678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_667, c_1673])).
% 3.34/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  Inference rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Ref     : 0
% 3.34/1.55  #Sup     : 376
% 3.34/1.55  #Fact    : 0
% 3.34/1.55  #Define  : 0
% 3.34/1.55  #Split   : 0
% 3.34/1.55  #Chain   : 0
% 3.34/1.55  #Close   : 0
% 3.34/1.55  
% 3.34/1.55  Ordering : KBO
% 3.34/1.55  
% 3.34/1.55  Simplification rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Subsume      : 57
% 3.34/1.55  #Demod        : 183
% 3.34/1.55  #Tautology    : 199
% 3.34/1.55  #SimpNegUnit  : 29
% 3.34/1.55  #BackRed      : 4
% 3.34/1.55  
% 3.34/1.55  #Partial instantiations: 0
% 3.34/1.55  #Strategies tried      : 1
% 3.34/1.55  
% 3.34/1.55  Timing (in seconds)
% 3.34/1.55  ----------------------
% 3.34/1.55  Preprocessing        : 0.33
% 3.34/1.55  Parsing              : 0.17
% 3.34/1.55  CNF conversion       : 0.02
% 3.34/1.55  Main loop            : 0.45
% 3.34/1.55  Inferencing          : 0.15
% 3.34/1.55  Reduction            : 0.17
% 3.34/1.55  Demodulation         : 0.13
% 3.34/1.55  BG Simplification    : 0.02
% 3.34/1.55  Subsumption          : 0.08
% 3.34/1.55  Abstraction          : 0.02
% 3.34/1.55  MUC search           : 0.00
% 3.34/1.55  Cooper               : 0.00
% 3.34/1.55  Total                : 0.81
% 3.34/1.55  Index Insertion      : 0.00
% 3.34/1.55  Index Deletion       : 0.00
% 3.34/1.55  Index Matching       : 0.00
% 3.34/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
