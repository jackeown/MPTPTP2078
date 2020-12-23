%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:20 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   64 (  72 expanded)
%              Number of leaves         :   33 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 (  74 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_64,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_76,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    ! [C_30] : r2_hidden(C_30,k1_tarski(C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_78,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_127,plain,(
    ! [B_56,A_57] : k3_xboole_0(B_56,A_57) = k3_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_127])).

tff(c_22,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_931,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_hidden(A_125,B_126)
      | ~ r2_hidden(A_125,C_127)
      | r2_hidden(A_125,k5_xboole_0(B_126,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1405,plain,(
    ! [A_162,A_163,B_164] :
      ( r2_hidden(A_162,A_163)
      | ~ r2_hidden(A_162,k3_xboole_0(A_163,B_164))
      | r2_hidden(A_162,k4_xboole_0(A_163,B_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_931])).

tff(c_26,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_270,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_294,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_270])).

tff(c_297,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_294])).

tff(c_28,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_346,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,k3_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_374,plain,(
    ! [A_83,B_84] :
      ( ~ r1_xboole_0(A_83,B_84)
      | k3_xboole_0(A_83,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_346])).

tff(c_398,plain,(
    ! [A_88,B_89] : k3_xboole_0(k4_xboole_0(A_88,B_89),B_89) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_374])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_444,plain,(
    ! [B_90,A_91] : k3_xboole_0(B_90,k4_xboole_0(A_91,B_90)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_2])).

tff(c_452,plain,(
    ! [B_90,A_91] : k4_xboole_0(B_90,k4_xboole_0(A_91,B_90)) = k5_xboole_0(B_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_22])).

tff(c_478,plain,(
    ! [B_92,A_93] : k4_xboole_0(B_92,k4_xboole_0(A_93,B_92)) = B_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_452])).

tff(c_522,plain,(
    ! [B_94,A_95] : r1_xboole_0(B_94,k4_xboole_0(A_95,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_28])).

tff(c_74,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,B_42)
      | ~ r1_xboole_0(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_541,plain,(
    ! [A_41,A_95] : ~ r2_hidden(A_41,k4_xboole_0(A_95,k1_tarski(A_41))) ),
    inference(resolution,[status(thm)],[c_522,c_74])).

tff(c_1442,plain,(
    ! [A_165,A_166] :
      ( r2_hidden(A_165,A_166)
      | ~ r2_hidden(A_165,k3_xboole_0(A_166,k1_tarski(A_165))) ) ),
    inference(resolution,[status(thm)],[c_1405,c_541])).

tff(c_1456,plain,
    ( r2_hidden('#skF_7',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_1442])).

tff(c_1478,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1456])).

tff(c_54,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1510,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1478,c_54])).

tff(c_1514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.49  
% 3.09/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.49  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.09/1.49  
% 3.09/1.49  %Foreground sorts:
% 3.09/1.49  
% 3.09/1.49  
% 3.09/1.49  %Background operators:
% 3.09/1.49  
% 3.09/1.49  
% 3.09/1.49  %Foreground operators:
% 3.09/1.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.09/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.09/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.09/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.09/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.09/1.49  
% 3.09/1.51  tff(f_104, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.09/1.51  tff(f_86, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.09/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.09/1.51  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.09/1.51  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.09/1.51  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.09/1.51  tff(f_60, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.09/1.51  tff(f_64, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.09/1.51  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.09/1.51  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.09/1.51  tff(f_99, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.09/1.51  tff(c_76, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.09/1.51  tff(c_56, plain, (![C_30]: (r2_hidden(C_30, k1_tarski(C_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.51  tff(c_78, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.09/1.51  tff(c_127, plain, (![B_56, A_57]: (k3_xboole_0(B_56, A_57)=k3_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.51  tff(c_171, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_78, c_127])).
% 3.09/1.51  tff(c_22, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.51  tff(c_931, plain, (![A_125, B_126, C_127]: (r2_hidden(A_125, B_126) | ~r2_hidden(A_125, C_127) | r2_hidden(A_125, k5_xboole_0(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.09/1.51  tff(c_1405, plain, (![A_162, A_163, B_164]: (r2_hidden(A_162, A_163) | ~r2_hidden(A_162, k3_xboole_0(A_163, B_164)) | r2_hidden(A_162, k4_xboole_0(A_163, B_164)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_931])).
% 3.09/1.51  tff(c_26, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.09/1.51  tff(c_24, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.09/1.51  tff(c_270, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.51  tff(c_294, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_270])).
% 3.09/1.51  tff(c_297, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_294])).
% 3.09/1.51  tff(c_28, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.51  tff(c_20, plain, (![A_11]: (r2_hidden('#skF_2'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.09/1.51  tff(c_346, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, k3_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.51  tff(c_374, plain, (![A_83, B_84]: (~r1_xboole_0(A_83, B_84) | k3_xboole_0(A_83, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_346])).
% 3.09/1.51  tff(c_398, plain, (![A_88, B_89]: (k3_xboole_0(k4_xboole_0(A_88, B_89), B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_374])).
% 3.09/1.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.51  tff(c_444, plain, (![B_90, A_91]: (k3_xboole_0(B_90, k4_xboole_0(A_91, B_90))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_398, c_2])).
% 3.09/1.51  tff(c_452, plain, (![B_90, A_91]: (k4_xboole_0(B_90, k4_xboole_0(A_91, B_90))=k5_xboole_0(B_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_444, c_22])).
% 3.09/1.51  tff(c_478, plain, (![B_92, A_93]: (k4_xboole_0(B_92, k4_xboole_0(A_93, B_92))=B_92)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_452])).
% 3.09/1.51  tff(c_522, plain, (![B_94, A_95]: (r1_xboole_0(B_94, k4_xboole_0(A_95, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_478, c_28])).
% 3.09/1.51  tff(c_74, plain, (![A_41, B_42]: (~r2_hidden(A_41, B_42) | ~r1_xboole_0(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.09/1.51  tff(c_541, plain, (![A_41, A_95]: (~r2_hidden(A_41, k4_xboole_0(A_95, k1_tarski(A_41))))), inference(resolution, [status(thm)], [c_522, c_74])).
% 3.09/1.51  tff(c_1442, plain, (![A_165, A_166]: (r2_hidden(A_165, A_166) | ~r2_hidden(A_165, k3_xboole_0(A_166, k1_tarski(A_165))))), inference(resolution, [status(thm)], [c_1405, c_541])).
% 3.09/1.51  tff(c_1456, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8')) | ~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_1442])).
% 3.09/1.51  tff(c_1478, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1456])).
% 3.09/1.51  tff(c_54, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.51  tff(c_1510, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_1478, c_54])).
% 3.09/1.51  tff(c_1514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1510])).
% 3.09/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.51  
% 3.09/1.51  Inference rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Ref     : 0
% 3.09/1.51  #Sup     : 329
% 3.09/1.51  #Fact    : 0
% 3.09/1.51  #Define  : 0
% 3.09/1.51  #Split   : 2
% 3.09/1.51  #Chain   : 0
% 3.09/1.51  #Close   : 0
% 3.09/1.51  
% 3.09/1.51  Ordering : KBO
% 3.09/1.51  
% 3.09/1.51  Simplification rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Subsume      : 50
% 3.09/1.51  #Demod        : 160
% 3.09/1.51  #Tautology    : 199
% 3.09/1.51  #SimpNegUnit  : 35
% 3.09/1.51  #BackRed      : 2
% 3.09/1.51  
% 3.09/1.51  #Partial instantiations: 0
% 3.09/1.51  #Strategies tried      : 1
% 3.09/1.51  
% 3.09/1.51  Timing (in seconds)
% 3.09/1.51  ----------------------
% 3.09/1.51  Preprocessing        : 0.32
% 3.09/1.51  Parsing              : 0.16
% 3.09/1.51  CNF conversion       : 0.02
% 3.09/1.51  Main loop            : 0.43
% 3.09/1.51  Inferencing          : 0.15
% 3.09/1.51  Reduction            : 0.16
% 3.09/1.51  Demodulation         : 0.12
% 3.09/1.51  BG Simplification    : 0.02
% 3.09/1.51  Subsumption          : 0.07
% 3.09/1.51  Abstraction          : 0.02
% 3.09/1.51  MUC search           : 0.00
% 3.09/1.51  Cooper               : 0.00
% 3.09/1.51  Total                : 0.77
% 3.09/1.51  Index Insertion      : 0.00
% 3.09/1.51  Index Deletion       : 0.00
% 3.09/1.51  Index Matching       : 0.00
% 3.09/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
