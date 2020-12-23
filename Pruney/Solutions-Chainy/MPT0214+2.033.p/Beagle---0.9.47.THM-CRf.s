%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:34 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (  74 expanded)
%              Number of leaves         :   37 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 (  61 expanded)
%              Number of equality atoms :   43 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ! [A_29,B_30,C_31] : k2_enumset1(A_29,A_29,B_30,C_31) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    ! [A_32,B_33,C_34,D_35] : k3_enumset1(A_32,A_32,B_33,C_34,D_35) = k2_enumset1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_933,plain,(
    ! [B_2370,E_2371,A_2367,C_2369,D_2368] : k2_xboole_0(k2_enumset1(A_2367,B_2370,C_2369,D_2368),k1_tarski(E_2371)) = k3_enumset1(A_2367,B_2370,C_2369,D_2368,E_2371) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_992,plain,(
    ! [A_29,B_30,C_31,E_2371] : k3_enumset1(A_29,A_29,B_30,C_31,E_2371) = k2_xboole_0(k1_enumset1(A_29,B_30,C_31),k1_tarski(E_2371)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_933])).

tff(c_996,plain,(
    ! [A_2428,B_2429,C_2430,E_2431] : k2_xboole_0(k1_enumset1(A_2428,B_2429,C_2430),k1_tarski(E_2431)) = k2_enumset1(A_2428,B_2429,C_2430,E_2431) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_992])).

tff(c_1055,plain,(
    ! [A_27,B_28,E_2431] : k2_xboole_0(k2_tarski(A_27,B_28),k1_tarski(E_2431)) = k2_enumset1(A_27,A_27,B_28,E_2431) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_996])).

tff(c_1059,plain,(
    ! [A_2488,B_2489,E_2490] : k2_xboole_0(k2_tarski(A_2488,B_2489),k1_tarski(E_2490)) = k1_enumset1(A_2488,B_2489,E_2490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1055])).

tff(c_1118,plain,(
    ! [A_26,E_2490] : k2_xboole_0(k1_tarski(A_26),k1_tarski(E_2490)) = k1_enumset1(A_26,A_26,E_2490) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1059])).

tff(c_1122,plain,(
    ! [A_2547,E_2548] : k2_xboole_0(k1_tarski(A_2547),k1_tarski(E_2548)) = k2_tarski(A_2547,E_2548) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1118])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_141,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_141])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_158,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_2])).

tff(c_161,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_167,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k4_xboole_0(B_80,A_79)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_167])).

tff(c_179,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_176])).

tff(c_1128,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_179])).

tff(c_112,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    ! [B_70,A_69] : r2_hidden(B_70,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_14])).

tff(c_1243,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1128,c_124])).

tff(c_36,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1276,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1243,c_36])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.20/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.20/1.50  
% 3.20/1.51  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.20/1.51  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.20/1.51  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.20/1.51  tff(f_67, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.20/1.51  tff(f_69, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.20/1.51  tff(f_61, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.20/1.51  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.51  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.20/1.51  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.20/1.51  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.51  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.20/1.51  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.20/1.51  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.20/1.51  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.51  tff(c_52, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.20/1.51  tff(c_50, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.51  tff(c_54, plain, (![A_29, B_30, C_31]: (k2_enumset1(A_29, A_29, B_30, C_31)=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.51  tff(c_56, plain, (![A_32, B_33, C_34, D_35]: (k3_enumset1(A_32, A_32, B_33, C_34, D_35)=k2_enumset1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.51  tff(c_933, plain, (![B_2370, E_2371, A_2367, C_2369, D_2368]: (k2_xboole_0(k2_enumset1(A_2367, B_2370, C_2369, D_2368), k1_tarski(E_2371))=k3_enumset1(A_2367, B_2370, C_2369, D_2368, E_2371))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.20/1.51  tff(c_992, plain, (![A_29, B_30, C_31, E_2371]: (k3_enumset1(A_29, A_29, B_30, C_31, E_2371)=k2_xboole_0(k1_enumset1(A_29, B_30, C_31), k1_tarski(E_2371)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_933])).
% 3.20/1.51  tff(c_996, plain, (![A_2428, B_2429, C_2430, E_2431]: (k2_xboole_0(k1_enumset1(A_2428, B_2429, C_2430), k1_tarski(E_2431))=k2_enumset1(A_2428, B_2429, C_2430, E_2431))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_992])).
% 3.20/1.51  tff(c_1055, plain, (![A_27, B_28, E_2431]: (k2_xboole_0(k2_tarski(A_27, B_28), k1_tarski(E_2431))=k2_enumset1(A_27, A_27, B_28, E_2431))), inference(superposition, [status(thm), theory('equality')], [c_52, c_996])).
% 3.20/1.51  tff(c_1059, plain, (![A_2488, B_2489, E_2490]: (k2_xboole_0(k2_tarski(A_2488, B_2489), k1_tarski(E_2490))=k1_enumset1(A_2488, B_2489, E_2490))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1055])).
% 3.20/1.51  tff(c_1118, plain, (![A_26, E_2490]: (k2_xboole_0(k1_tarski(A_26), k1_tarski(E_2490))=k1_enumset1(A_26, A_26, E_2490))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1059])).
% 3.20/1.51  tff(c_1122, plain, (![A_2547, E_2548]: (k2_xboole_0(k1_tarski(A_2547), k1_tarski(E_2548))=k2_tarski(A_2547, E_2548))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1118])).
% 3.20/1.51  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.51  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.51  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.51  tff(c_141, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.51  tff(c_145, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_141])).
% 3.20/1.51  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.51  tff(c_158, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_2])).
% 3.20/1.51  tff(c_161, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_158])).
% 3.20/1.51  tff(c_167, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k4_xboole_0(B_80, A_79))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.51  tff(c_176, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_161, c_167])).
% 3.20/1.51  tff(c_179, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_176])).
% 3.20/1.51  tff(c_1128, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1122, c_179])).
% 3.20/1.51  tff(c_112, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.20/1.51  tff(c_14, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.20/1.51  tff(c_124, plain, (![B_70, A_69]: (r2_hidden(B_70, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_14])).
% 3.20/1.51  tff(c_1243, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1128, c_124])).
% 3.20/1.51  tff(c_36, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.51  tff(c_1276, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1243, c_36])).
% 3.20/1.51  tff(c_1318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1276])).
% 3.20/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  
% 3.20/1.51  Inference rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Ref     : 0
% 3.20/1.51  #Sup     : 138
% 3.20/1.51  #Fact    : 0
% 3.20/1.51  #Define  : 0
% 3.20/1.51  #Split   : 6
% 3.20/1.51  #Chain   : 0
% 3.20/1.51  #Close   : 0
% 3.20/1.51  
% 3.20/1.51  Ordering : KBO
% 3.20/1.51  
% 3.20/1.51  Simplification rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Subsume      : 3
% 3.20/1.51  #Demod        : 10
% 3.20/1.51  #Tautology    : 48
% 3.20/1.51  #SimpNegUnit  : 1
% 3.20/1.51  #BackRed      : 0
% 3.20/1.51  
% 3.20/1.51  #Partial instantiations: 855
% 3.20/1.51  #Strategies tried      : 1
% 3.20/1.51  
% 3.20/1.51  Timing (in seconds)
% 3.20/1.51  ----------------------
% 3.20/1.51  Preprocessing        : 0.34
% 3.20/1.51  Parsing              : 0.18
% 3.20/1.51  CNF conversion       : 0.02
% 3.20/1.51  Main loop            : 0.38
% 3.20/1.51  Inferencing          : 0.20
% 3.20/1.51  Reduction            : 0.08
% 3.20/1.51  Demodulation         : 0.06
% 3.20/1.51  BG Simplification    : 0.02
% 3.20/1.51  Subsumption          : 0.05
% 3.20/1.52  Abstraction          : 0.02
% 3.20/1.52  MUC search           : 0.00
% 3.20/1.52  Cooper               : 0.00
% 3.20/1.52  Total                : 0.75
% 3.20/1.52  Index Insertion      : 0.00
% 3.20/1.52  Index Deletion       : 0.00
% 3.20/1.52  Index Matching       : 0.00
% 3.20/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
