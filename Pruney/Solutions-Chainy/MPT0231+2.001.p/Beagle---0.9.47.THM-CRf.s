%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:14 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 105 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_5 > #skF_8 > #skF_7 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_108,plain,(
    '#skF_10' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [E_25,A_19,C_21] : r2_hidden(E_25,k1_enumset1(A_19,E_25,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_265,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_287,plain,(
    ! [A_89] :
      ( k1_xboole_0 = A_89
      | ~ r1_tarski(A_89,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_265])).

tff(c_300,plain,(
    ! [B_16] : k4_xboole_0(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_287])).

tff(c_319,plain,(
    ! [D_91,B_92,A_93] :
      ( ~ r2_hidden(D_91,B_92)
      | ~ r2_hidden(D_91,k4_xboole_0(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_333,plain,(
    ! [D_94,B_95] :
      ( ~ r2_hidden(D_94,B_95)
      | ~ r2_hidden(D_94,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_319])).

tff(c_352,plain,(
    ! [E_25] : ~ r2_hidden(E_25,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_333])).

tff(c_110,plain,(
    r1_tarski(k2_tarski('#skF_10','#skF_11'),k1_tarski('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_393,plain,(
    ! [B_105,A_106] :
      ( k1_tarski(B_105) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k1_tarski(B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_409,plain,
    ( k2_tarski('#skF_10','#skF_11') = k1_tarski('#skF_12')
    | k2_tarski('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_393])).

tff(c_1069,plain,(
    k2_tarski('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_78,plain,(
    ! [D_36,B_32] : r2_hidden(D_36,k2_tarski(D_36,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1085,plain,(
    r2_hidden('#skF_10',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_78])).

tff(c_1093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_1085])).

tff(c_1094,plain,(
    k2_tarski('#skF_10','#skF_11') = k1_tarski('#skF_12') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_280,plain,
    ( k2_tarski('#skF_10','#skF_11') = k1_tarski('#skF_12')
    | ~ r1_tarski(k1_tarski('#skF_12'),k2_tarski('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_110,c_265])).

tff(c_369,plain,(
    ~ r1_tarski(k1_tarski('#skF_12'),k2_tarski('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_1098,plain,(
    ~ r1_tarski(k1_tarski('#skF_12'),k1_tarski('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_369])).

tff(c_1102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1098])).

tff(c_1103,plain,(
    k2_tarski('#skF_10','#skF_11') = k1_tarski('#skF_12') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_1131,plain,(
    r2_hidden('#skF_10',k1_tarski('#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_78])).

tff(c_62,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1141,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1131,c_62])).

tff(c_1145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_1141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:45:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.49  
% 2.95/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_5 > #skF_8 > #skF_7 > #skF_12
% 2.95/1.49  
% 2.95/1.49  %Foreground sorts:
% 2.95/1.49  
% 2.95/1.49  
% 2.95/1.49  %Background operators:
% 2.95/1.49  
% 2.95/1.49  
% 2.95/1.49  %Foreground operators:
% 2.95/1.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.95/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.95/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.49  tff('#skF_11', type, '#skF_11': $i).
% 2.95/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.95/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.49  tff('#skF_10', type, '#skF_10': $i).
% 2.95/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.95/1.49  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.95/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.95/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.95/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.49  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.95/1.49  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.95/1.49  tff('#skF_12', type, '#skF_12': $i).
% 2.95/1.49  
% 3.14/1.50  tff(f_120, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 3.14/1.50  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.50  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.14/1.50  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.14/1.50  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.14/1.50  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.14/1.50  tff(f_113, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.14/1.50  tff(f_96, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.14/1.50  tff(f_87, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.14/1.50  tff(c_108, plain, ('#skF_10'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.14/1.50  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.50  tff(c_42, plain, (![E_25, A_19, C_21]: (r2_hidden(E_25, k1_enumset1(A_19, E_25, C_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.14/1.50  tff(c_34, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.50  tff(c_32, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.14/1.50  tff(c_265, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.50  tff(c_287, plain, (![A_89]: (k1_xboole_0=A_89 | ~r1_tarski(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_265])).
% 3.14/1.50  tff(c_300, plain, (![B_16]: (k4_xboole_0(k1_xboole_0, B_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_287])).
% 3.14/1.50  tff(c_319, plain, (![D_91, B_92, A_93]: (~r2_hidden(D_91, B_92) | ~r2_hidden(D_91, k4_xboole_0(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.50  tff(c_333, plain, (![D_94, B_95]: (~r2_hidden(D_94, B_95) | ~r2_hidden(D_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_300, c_319])).
% 3.14/1.50  tff(c_352, plain, (![E_25]: (~r2_hidden(E_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_333])).
% 3.14/1.50  tff(c_110, plain, (r1_tarski(k2_tarski('#skF_10', '#skF_11'), k1_tarski('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.14/1.50  tff(c_393, plain, (![B_105, A_106]: (k1_tarski(B_105)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k1_tarski(B_105)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.14/1.50  tff(c_409, plain, (k2_tarski('#skF_10', '#skF_11')=k1_tarski('#skF_12') | k2_tarski('#skF_10', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_393])).
% 3.14/1.50  tff(c_1069, plain, (k2_tarski('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_409])).
% 3.14/1.50  tff(c_78, plain, (![D_36, B_32]: (r2_hidden(D_36, k2_tarski(D_36, B_32)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.50  tff(c_1085, plain, (r2_hidden('#skF_10', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1069, c_78])).
% 3.14/1.50  tff(c_1093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_1085])).
% 3.14/1.50  tff(c_1094, plain, (k2_tarski('#skF_10', '#skF_11')=k1_tarski('#skF_12')), inference(splitRight, [status(thm)], [c_409])).
% 3.14/1.50  tff(c_280, plain, (k2_tarski('#skF_10', '#skF_11')=k1_tarski('#skF_12') | ~r1_tarski(k1_tarski('#skF_12'), k2_tarski('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_110, c_265])).
% 3.14/1.50  tff(c_369, plain, (~r1_tarski(k1_tarski('#skF_12'), k2_tarski('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_280])).
% 3.14/1.50  tff(c_1098, plain, (~r1_tarski(k1_tarski('#skF_12'), k1_tarski('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_369])).
% 3.14/1.50  tff(c_1102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1098])).
% 3.14/1.50  tff(c_1103, plain, (k2_tarski('#skF_10', '#skF_11')=k1_tarski('#skF_12')), inference(splitRight, [status(thm)], [c_280])).
% 3.14/1.50  tff(c_1131, plain, (r2_hidden('#skF_10', k1_tarski('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_78])).
% 3.14/1.50  tff(c_62, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.14/1.50  tff(c_1141, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_1131, c_62])).
% 3.14/1.50  tff(c_1145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_1141])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 145
% 3.14/1.50  #Fact    : 0
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 2
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 19
% 3.14/1.50  #Demod        : 36
% 3.14/1.50  #Tautology    : 64
% 3.14/1.50  #SimpNegUnit  : 3
% 3.14/1.50  #BackRed      : 6
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 756
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.51  Preprocessing        : 0.34
% 3.14/1.51  Parsing              : 0.16
% 3.14/1.51  CNF conversion       : 0.03
% 3.14/1.51  Main loop            : 0.37
% 3.14/1.51  Inferencing          : 0.15
% 3.14/1.51  Reduction            : 0.11
% 3.14/1.51  Demodulation         : 0.08
% 3.14/1.51  BG Simplification    : 0.03
% 3.14/1.51  Subsumption          : 0.07
% 3.14/1.51  Abstraction          : 0.02
% 3.14/1.51  MUC search           : 0.00
% 3.14/1.51  Cooper               : 0.00
% 3.14/1.51  Total                : 0.74
% 3.14/1.51  Index Insertion      : 0.00
% 3.14/1.51  Index Deletion       : 0.00
% 3.14/1.51  Index Matching       : 0.00
% 3.14/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
