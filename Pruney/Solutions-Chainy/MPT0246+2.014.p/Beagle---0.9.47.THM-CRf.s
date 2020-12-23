%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:01 EST 2020

% Result     : Theorem 20.31s
% Output     : CNFRefutation 20.31s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 160 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 330 expanded)
%              Number of equality atoms :   81 ( 222 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_50,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_63,plain,(
    ! [A_48] :
      ( v1_xboole_0(A_48)
      | r2_hidden('#skF_1'(A_48),A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [C_42] :
      ( C_42 = '#skF_5'
      | ~ r2_hidden(C_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_72,plain,
    ( '#skF_1'('#skF_4') = '#skF_5'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_46])).

tff(c_73,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_73,c_6])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_76])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_81,plain,(
    '#skF_1'('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_4')
    | r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4])).

tff(c_89,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_86])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( '#skF_2'(A_6,B_7,C_8,D_9) = C_8
      | '#skF_2'(A_6,B_7,C_8,D_9) = B_7
      | '#skF_2'(A_6,B_7,C_8,D_9) = A_6
      | '#skF_3'(A_6,B_7,C_8,D_9) != A_6
      | k1_enumset1(A_6,B_7,C_8) = D_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_720,plain,(
    ! [B_7,C_8,D_9] :
      ( '#skF_2'(B_7,B_7,C_8,D_9) = C_8
      | '#skF_3'(B_7,B_7,C_8,D_9) != B_7
      | k1_enumset1(B_7,B_7,C_8) = D_9
      | '#skF_2'(B_7,B_7,C_8,D_9) = B_7 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_26])).

tff(c_727,plain,(
    ! [B_7,C_8,D_9] :
      ( '#skF_2'(B_7,B_7,C_8,D_9) = C_8
      | '#skF_3'(B_7,B_7,C_8,D_9) != B_7
      | k2_tarski(B_7,C_8) = D_9
      | '#skF_2'(B_7,B_7,C_8,D_9) = B_7 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_720])).

tff(c_1530,plain,(
    ! [C_8,D_9] :
      ( '#skF_3'(C_8,C_8,C_8,D_9) != C_8
      | k2_tarski(C_8,C_8) = D_9
      | '#skF_2'(C_8,C_8,C_8,D_9) = C_8 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_727])).

tff(c_1998,plain,(
    ! [C_3795,D_3796] :
      ( '#skF_3'(C_3795,C_3795,C_3795,D_3796) != C_3795
      | k1_tarski(C_3795) = D_3796
      | '#skF_2'(C_3795,C_3795,C_3795,D_3796) = C_3795 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1530])).

tff(c_2285,plain,(
    ! [D_5732] :
      ( D_5732 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_5732) != '#skF_5'
      | '#skF_2'('#skF_5','#skF_5','#skF_5',D_5732) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1998,c_50])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8,D_9),D_9)
      | '#skF_3'(A_6,B_7,C_8,D_9) != A_6
      | k1_enumset1(A_6,B_7,C_8) = D_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2312,plain,(
    ! [D_5732] :
      ( ~ r2_hidden('#skF_5',D_5732)
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_5732) != '#skF_5'
      | k1_enumset1('#skF_5','#skF_5','#skF_5') = D_5732
      | D_5732 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_5732) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2285,c_24])).

tff(c_2353,plain,(
    ! [D_5868] :
      ( ~ r2_hidden('#skF_5',D_5868)
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_5868) != '#skF_5'
      | k1_tarski('#skF_5') = D_5868
      | D_5868 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_5868) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_2312])).

tff(c_2394,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_89,c_2353])).

tff(c_2403,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2394])).

tff(c_6289,plain,(
    ! [A_19444,B_19445,C_19446,D_19447] :
      ( '#skF_2'(A_19444,B_19445,C_19446,D_19447) = C_19446
      | '#skF_2'(A_19444,B_19445,C_19446,D_19447) = B_19445
      | '#skF_2'(A_19444,B_19445,C_19446,D_19447) = A_19444
      | r2_hidden('#skF_3'(A_19444,B_19445,C_19446,D_19447),D_19447)
      | k1_enumset1(A_19444,B_19445,C_19446) = D_19447 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6622,plain,(
    ! [A_20080,B_20081,C_20082] :
      ( '#skF_3'(A_20080,B_20081,C_20082,'#skF_4') = '#skF_5'
      | '#skF_2'(A_20080,B_20081,C_20082,'#skF_4') = C_20082
      | '#skF_2'(A_20080,B_20081,C_20082,'#skF_4') = B_20081
      | '#skF_2'(A_20080,B_20081,C_20082,'#skF_4') = A_20080
      | k1_enumset1(A_20080,B_20081,C_20082) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_6289,c_46])).

tff(c_6678,plain,(
    ! [B_20081,C_20082] :
      ( k2_tarski(B_20081,C_20082) = '#skF_4'
      | '#skF_3'(B_20081,B_20081,C_20082,'#skF_4') = '#skF_5'
      | '#skF_2'(B_20081,B_20081,C_20082,'#skF_4') = C_20082
      | '#skF_2'(B_20081,B_20081,C_20082,'#skF_4') = B_20081
      | '#skF_2'(B_20081,B_20081,C_20082,'#skF_4') = B_20081 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_34])).

tff(c_99279,plain,(
    ! [C_20082] :
      ( k2_tarski(C_20082,C_20082) = '#skF_4'
      | '#skF_3'(C_20082,C_20082,C_20082,'#skF_4') = '#skF_5'
      | '#skF_2'(C_20082,C_20082,C_20082,'#skF_4') = C_20082 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6678])).

tff(c_101356,plain,(
    ! [C_90667] :
      ( k1_tarski(C_90667) = '#skF_4'
      | '#skF_3'(C_90667,C_90667,C_90667,'#skF_4') = '#skF_5'
      | '#skF_2'(C_90667,C_90667,C_90667,'#skF_4') = C_90667 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99279])).

tff(c_101376,plain,
    ( '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5'
    | '#skF_2'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_101356,c_50])).

tff(c_102147,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2403,c_101376])).

tff(c_28,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8,D_9),D_9)
      | r2_hidden('#skF_3'(A_6,B_7,C_8,D_9),D_9)
      | k1_enumset1(A_6,B_7,C_8) = D_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102451,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k1_enumset1('#skF_5','#skF_5','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_102147,c_28])).

tff(c_102722,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_89,c_102451])).

tff(c_102723,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_102722])).

tff(c_102742,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_102723,c_46])).

tff(c_102747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2403,c_102742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.31/12.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.31/12.84  
% 20.31/12.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.31/12.85  %$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 20.31/12.85  
% 20.31/12.85  %Foreground sorts:
% 20.31/12.85  
% 20.31/12.85  
% 20.31/12.85  %Background operators:
% 20.31/12.85  
% 20.31/12.85  
% 20.31/12.85  %Foreground operators:
% 20.31/12.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.31/12.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.31/12.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.31/12.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 20.31/12.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.31/12.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.31/12.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.31/12.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.31/12.85  tff('#skF_5', type, '#skF_5': $i).
% 20.31/12.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 20.31/12.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.31/12.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.31/12.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.31/12.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.31/12.85  tff('#skF_4', type, '#skF_4': $i).
% 20.31/12.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.31/12.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 20.31/12.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 20.31/12.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.31/12.85  
% 20.31/12.86  tff(f_79, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 20.31/12.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 20.31/12.86  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 20.31/12.86  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 20.31/12.86  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 20.31/12.86  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 20.31/12.86  tff(c_50, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 20.31/12.86  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 20.31/12.86  tff(c_63, plain, (![A_48]: (v1_xboole_0(A_48) | r2_hidden('#skF_1'(A_48), A_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.31/12.86  tff(c_46, plain, (![C_42]: (C_42='#skF_5' | ~r2_hidden(C_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 20.31/12.86  tff(c_72, plain, ('#skF_1'('#skF_4')='#skF_5' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_63, c_46])).
% 20.31/12.86  tff(c_73, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 20.31/12.86  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.31/12.86  tff(c_76, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_73, c_6])).
% 20.31/12.86  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_76])).
% 20.31/12.86  tff(c_82, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 20.31/12.86  tff(c_81, plain, ('#skF_1'('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_72])).
% 20.31/12.86  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.31/12.86  tff(c_86, plain, (v1_xboole_0('#skF_4') | r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_81, c_4])).
% 20.31/12.86  tff(c_89, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_86])).
% 20.31/12.86  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.31/12.86  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 20.31/12.86  tff(c_26, plain, (![A_6, B_7, C_8, D_9]: ('#skF_2'(A_6, B_7, C_8, D_9)=C_8 | '#skF_2'(A_6, B_7, C_8, D_9)=B_7 | '#skF_2'(A_6, B_7, C_8, D_9)=A_6 | '#skF_3'(A_6, B_7, C_8, D_9)!=A_6 | k1_enumset1(A_6, B_7, C_8)=D_9)), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.31/12.86  tff(c_720, plain, (![B_7, C_8, D_9]: ('#skF_2'(B_7, B_7, C_8, D_9)=C_8 | '#skF_3'(B_7, B_7, C_8, D_9)!=B_7 | k1_enumset1(B_7, B_7, C_8)=D_9 | '#skF_2'(B_7, B_7, C_8, D_9)=B_7)), inference(factorization, [status(thm), theory('equality')], [c_26])).
% 20.31/12.86  tff(c_727, plain, (![B_7, C_8, D_9]: ('#skF_2'(B_7, B_7, C_8, D_9)=C_8 | '#skF_3'(B_7, B_7, C_8, D_9)!=B_7 | k2_tarski(B_7, C_8)=D_9 | '#skF_2'(B_7, B_7, C_8, D_9)=B_7)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_720])).
% 20.31/12.86  tff(c_1530, plain, (![C_8, D_9]: ('#skF_3'(C_8, C_8, C_8, D_9)!=C_8 | k2_tarski(C_8, C_8)=D_9 | '#skF_2'(C_8, C_8, C_8, D_9)=C_8)), inference(factorization, [status(thm), theory('equality')], [c_727])).
% 20.31/12.86  tff(c_1998, plain, (![C_3795, D_3796]: ('#skF_3'(C_3795, C_3795, C_3795, D_3796)!=C_3795 | k1_tarski(C_3795)=D_3796 | '#skF_2'(C_3795, C_3795, C_3795, D_3796)=C_3795)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1530])).
% 20.31/12.86  tff(c_2285, plain, (![D_5732]: (D_5732!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_5732)!='#skF_5' | '#skF_2'('#skF_5', '#skF_5', '#skF_5', D_5732)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1998, c_50])).
% 20.31/12.86  tff(c_24, plain, (![A_6, B_7, C_8, D_9]: (~r2_hidden('#skF_2'(A_6, B_7, C_8, D_9), D_9) | '#skF_3'(A_6, B_7, C_8, D_9)!=A_6 | k1_enumset1(A_6, B_7, C_8)=D_9)), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.31/12.86  tff(c_2312, plain, (![D_5732]: (~r2_hidden('#skF_5', D_5732) | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_5732)!='#skF_5' | k1_enumset1('#skF_5', '#skF_5', '#skF_5')=D_5732 | D_5732!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_5732)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2285, c_24])).
% 20.31/12.86  tff(c_2353, plain, (![D_5868]: (~r2_hidden('#skF_5', D_5868) | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_5868)!='#skF_5' | k1_tarski('#skF_5')=D_5868 | D_5868!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_5868)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_2312])).
% 20.31/12.86  tff(c_2394, plain, (k1_tarski('#skF_5')='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(resolution, [status(thm)], [c_89, c_2353])).
% 20.31/12.86  tff(c_2403, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_50, c_2394])).
% 20.31/12.86  tff(c_6289, plain, (![A_19444, B_19445, C_19446, D_19447]: ('#skF_2'(A_19444, B_19445, C_19446, D_19447)=C_19446 | '#skF_2'(A_19444, B_19445, C_19446, D_19447)=B_19445 | '#skF_2'(A_19444, B_19445, C_19446, D_19447)=A_19444 | r2_hidden('#skF_3'(A_19444, B_19445, C_19446, D_19447), D_19447) | k1_enumset1(A_19444, B_19445, C_19446)=D_19447)), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.31/12.86  tff(c_6622, plain, (![A_20080, B_20081, C_20082]: ('#skF_3'(A_20080, B_20081, C_20082, '#skF_4')='#skF_5' | '#skF_2'(A_20080, B_20081, C_20082, '#skF_4')=C_20082 | '#skF_2'(A_20080, B_20081, C_20082, '#skF_4')=B_20081 | '#skF_2'(A_20080, B_20081, C_20082, '#skF_4')=A_20080 | k1_enumset1(A_20080, B_20081, C_20082)='#skF_4')), inference(resolution, [status(thm)], [c_6289, c_46])).
% 20.31/12.86  tff(c_6678, plain, (![B_20081, C_20082]: (k2_tarski(B_20081, C_20082)='#skF_4' | '#skF_3'(B_20081, B_20081, C_20082, '#skF_4')='#skF_5' | '#skF_2'(B_20081, B_20081, C_20082, '#skF_4')=C_20082 | '#skF_2'(B_20081, B_20081, C_20082, '#skF_4')=B_20081 | '#skF_2'(B_20081, B_20081, C_20082, '#skF_4')=B_20081)), inference(superposition, [status(thm), theory('equality')], [c_6622, c_34])).
% 20.31/12.86  tff(c_99279, plain, (![C_20082]: (k2_tarski(C_20082, C_20082)='#skF_4' | '#skF_3'(C_20082, C_20082, C_20082, '#skF_4')='#skF_5' | '#skF_2'(C_20082, C_20082, C_20082, '#skF_4')=C_20082)), inference(factorization, [status(thm), theory('equality')], [c_6678])).
% 20.31/12.86  tff(c_101356, plain, (![C_90667]: (k1_tarski(C_90667)='#skF_4' | '#skF_3'(C_90667, C_90667, C_90667, '#skF_4')='#skF_5' | '#skF_2'(C_90667, C_90667, C_90667, '#skF_4')=C_90667)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_99279])).
% 20.31/12.86  tff(c_101376, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5' | '#skF_2'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_101356, c_50])).
% 20.31/12.86  tff(c_102147, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2403, c_101376])).
% 20.31/12.86  tff(c_28, plain, (![A_6, B_7, C_8, D_9]: (~r2_hidden('#skF_2'(A_6, B_7, C_8, D_9), D_9) | r2_hidden('#skF_3'(A_6, B_7, C_8, D_9), D_9) | k1_enumset1(A_6, B_7, C_8)=D_9)), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.31/12.86  tff(c_102451, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k1_enumset1('#skF_5', '#skF_5', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_102147, c_28])).
% 20.31/12.86  tff(c_102722, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_89, c_102451])).
% 20.31/12.86  tff(c_102723, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_102722])).
% 20.31/12.86  tff(c_102742, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_102723, c_46])).
% 20.31/12.86  tff(c_102747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2403, c_102742])).
% 20.31/12.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.31/12.86  
% 20.31/12.86  Inference rules
% 20.31/12.86  ----------------------
% 20.31/12.86  #Ref     : 0
% 20.31/12.86  #Sup     : 16866
% 20.31/12.86  #Fact    : 362
% 20.31/12.86  #Define  : 0
% 20.31/12.86  #Split   : 1
% 20.31/12.86  #Chain   : 0
% 20.31/12.86  #Close   : 0
% 20.31/12.86  
% 20.31/12.86  Ordering : KBO
% 20.31/12.86  
% 20.31/12.86  Simplification rules
% 20.31/12.86  ----------------------
% 20.31/12.86  #Subsume      : 10995
% 20.31/12.86  #Demod        : 786
% 20.31/12.86  #Tautology    : 4763
% 20.31/12.86  #SimpNegUnit  : 120
% 20.31/12.86  #BackRed      : 0
% 20.31/12.86  
% 20.31/12.86  #Partial instantiations: 25840
% 20.31/12.86  #Strategies tried      : 1
% 20.31/12.86  
% 20.31/12.86  Timing (in seconds)
% 20.31/12.86  ----------------------
% 20.31/12.86  Preprocessing        : 0.32
% 20.31/12.86  Parsing              : 0.16
% 20.31/12.86  CNF conversion       : 0.02
% 20.31/12.86  Main loop            : 11.78
% 20.31/12.86  Inferencing          : 4.17
% 20.31/12.86  Reduction            : 1.79
% 20.31/12.86  Demodulation         : 1.21
% 20.31/12.86  BG Simplification    : 0.26
% 20.31/12.86  Subsumption          : 5.31
% 20.31/12.86  Abstraction          : 0.55
% 20.31/12.87  MUC search           : 0.00
% 20.31/12.87  Cooper               : 0.00
% 20.31/12.87  Total                : 12.13
% 20.31/12.87  Index Insertion      : 0.00
% 20.31/12.87  Index Deletion       : 0.00
% 20.31/12.87  Index Matching       : 0.00
% 20.31/12.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
