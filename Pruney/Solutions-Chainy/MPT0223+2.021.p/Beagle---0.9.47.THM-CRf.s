%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:19 EST 2020

% Result     : Theorem 12.32s
% Output     : CNFRefutation 12.32s
% Verified   : 
% Statistics : Number of formulae       :   75 (  80 expanded)
%              Number of leaves         :   37 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :   73 (  81 expanded)
%              Number of equality atoms :   36 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_84,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    ! [C_37] : r2_hidden(C_37,k1_tarski(C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_86,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_163,plain,(
    ! [B_69,A_70] : k3_xboole_0(B_69,A_70) = k3_xboole_0(A_70,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_207,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_163])).

tff(c_20,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3825,plain,(
    ! [A_2783,B_2784,C_2785] :
      ( r2_hidden(A_2783,B_2784)
      | ~ r2_hidden(A_2783,C_2785)
      | r2_hidden(A_2783,k5_xboole_0(B_2784,C_2785)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_25576,plain,(
    ! [A_6516,A_6517,B_6518] :
      ( r2_hidden(A_6516,A_6517)
      | ~ r2_hidden(A_6516,k3_xboole_0(A_6517,B_6518))
      | r2_hidden(A_6516,k4_xboole_0(A_6517,B_6518)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3825])).

tff(c_34,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [B_58,A_59] :
      ( r1_xboole_0(B_58,A_59)
      | ~ r1_xboole_0(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    ! [A_23] : r1_xboole_0(k1_xboole_0,A_23) ),
    inference(resolution,[status(thm)],[c_34,c_139])).

tff(c_1245,plain,(
    ! [A_121,B_122,C_123] : k4_xboole_0(k3_xboole_0(A_121,B_122),C_123) = k3_xboole_0(A_121,k4_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_464,plain,(
    ! [A_90,B_91] : k4_xboole_0(A_90,k4_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_493,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_464])).

tff(c_499,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_493])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_560,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_587,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_560])).

tff(c_594,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_587])).

tff(c_22,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_581,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_560])).

tff(c_792,plain,(
    ! [A_104,B_105] : k4_xboole_0(A_104,k2_xboole_0(A_104,B_105)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_581])).

tff(c_823,plain,(
    ! [A_21,B_22] : k4_xboole_0(k3_xboole_0(A_21,B_22),A_21) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_792])).

tff(c_1349,plain,(
    ! [C_124,B_125] : k3_xboole_0(C_124,k4_xboole_0(B_125,C_124)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_823])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( ~ r1_xboole_0(k3_xboole_0(A_24,B_25),B_25)
      | r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1378,plain,(
    ! [B_125,C_124] :
      ( ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(B_125,C_124))
      | r1_xboole_0(C_124,k4_xboole_0(B_125,C_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_36])).

tff(c_1480,plain,(
    ! [C_128,B_129] : r1_xboole_0(C_128,k4_xboole_0(B_129,C_128)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1378])).

tff(c_82,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden(A_48,B_49)
      | ~ r1_xboole_0(k1_tarski(A_48),B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1514,plain,(
    ! [A_48,B_129] : ~ r2_hidden(A_48,k4_xboole_0(B_129,k1_tarski(A_48))) ),
    inference(resolution,[status(thm)],[c_1480,c_82])).

tff(c_42026,plain,(
    ! [A_8467,A_8468] :
      ( r2_hidden(A_8467,A_8468)
      | ~ r2_hidden(A_8467,k3_xboole_0(A_8468,k1_tarski(A_8467))) ) ),
    inference(resolution,[status(thm)],[c_25576,c_1514])).

tff(c_42088,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_42026])).

tff(c_42121,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_42088])).

tff(c_62,plain,(
    ! [C_37,A_33] :
      ( C_37 = A_33
      | ~ r2_hidden(C_37,k1_tarski(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42134,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42121,c_62])).

tff(c_42175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_42134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:08:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.32/5.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.32/5.32  
% 12.32/5.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.32/5.32  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 12.32/5.32  
% 12.32/5.32  %Foreground sorts:
% 12.32/5.32  
% 12.32/5.32  
% 12.32/5.32  %Background operators:
% 12.32/5.32  
% 12.32/5.32  
% 12.32/5.32  %Foreground operators:
% 12.32/5.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.32/5.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.32/5.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.32/5.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.32/5.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.32/5.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.32/5.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.32/5.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.32/5.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.32/5.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.32/5.32  tff('#skF_5', type, '#skF_5': $i).
% 12.32/5.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 12.32/5.32  tff('#skF_6', type, '#skF_6': $i).
% 12.32/5.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.32/5.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.32/5.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.32/5.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.32/5.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.32/5.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.32/5.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 12.32/5.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.32/5.32  
% 12.32/5.34  tff(f_102, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 12.32/5.34  tff(f_84, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 12.32/5.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.32/5.34  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.32/5.34  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 12.32/5.34  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.32/5.34  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.32/5.34  tff(f_52, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.32/5.34  tff(f_54, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 12.32/5.34  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 12.32/5.34  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.32/5.34  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.32/5.34  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 12.32/5.34  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 12.32/5.34  tff(f_62, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 12.32/5.34  tff(f_97, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 12.32/5.34  tff(c_84, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.32/5.34  tff(c_64, plain, (![C_37]: (r2_hidden(C_37, k1_tarski(C_37)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.32/5.34  tff(c_86, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.32/5.34  tff(c_163, plain, (![B_69, A_70]: (k3_xboole_0(B_69, A_70)=k3_xboole_0(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.32/5.34  tff(c_207, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_86, c_163])).
% 12.32/5.34  tff(c_20, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.32/5.34  tff(c_3825, plain, (![A_2783, B_2784, C_2785]: (r2_hidden(A_2783, B_2784) | ~r2_hidden(A_2783, C_2785) | r2_hidden(A_2783, k5_xboole_0(B_2784, C_2785)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.32/5.34  tff(c_25576, plain, (![A_6516, A_6517, B_6518]: (r2_hidden(A_6516, A_6517) | ~r2_hidden(A_6516, k3_xboole_0(A_6517, B_6518)) | r2_hidden(A_6516, k4_xboole_0(A_6517, B_6518)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3825])).
% 12.32/5.34  tff(c_34, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.32/5.34  tff(c_139, plain, (![B_58, A_59]: (r1_xboole_0(B_58, A_59) | ~r1_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.32/5.34  tff(c_142, plain, (![A_23]: (r1_xboole_0(k1_xboole_0, A_23))), inference(resolution, [status(thm)], [c_34, c_139])).
% 12.32/5.34  tff(c_1245, plain, (![A_121, B_122, C_123]: (k4_xboole_0(k3_xboole_0(A_121, B_122), C_123)=k3_xboole_0(A_121, k4_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.32/5.34  tff(c_32, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.32/5.34  tff(c_24, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.32/5.34  tff(c_26, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.32/5.34  tff(c_464, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k4_xboole_0(A_90, B_91))=k3_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.32/5.34  tff(c_493, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_464])).
% 12.32/5.34  tff(c_499, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_493])).
% 12.32/5.34  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.32/5.34  tff(c_560, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.32/5.34  tff(c_587, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_560])).
% 12.32/5.34  tff(c_594, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_499, c_587])).
% 12.32/5.34  tff(c_22, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.32/5.34  tff(c_581, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k5_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_22, c_560])).
% 12.32/5.34  tff(c_792, plain, (![A_104, B_105]: (k4_xboole_0(A_104, k2_xboole_0(A_104, B_105))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_594, c_581])).
% 12.32/5.34  tff(c_823, plain, (![A_21, B_22]: (k4_xboole_0(k3_xboole_0(A_21, B_22), A_21)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_792])).
% 12.32/5.34  tff(c_1349, plain, (![C_124, B_125]: (k3_xboole_0(C_124, k4_xboole_0(B_125, C_124))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1245, c_823])).
% 12.32/5.34  tff(c_36, plain, (![A_24, B_25]: (~r1_xboole_0(k3_xboole_0(A_24, B_25), B_25) | r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.32/5.34  tff(c_1378, plain, (![B_125, C_124]: (~r1_xboole_0(k1_xboole_0, k4_xboole_0(B_125, C_124)) | r1_xboole_0(C_124, k4_xboole_0(B_125, C_124)))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_36])).
% 12.32/5.34  tff(c_1480, plain, (![C_128, B_129]: (r1_xboole_0(C_128, k4_xboole_0(B_129, C_128)))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1378])).
% 12.32/5.34  tff(c_82, plain, (![A_48, B_49]: (~r2_hidden(A_48, B_49) | ~r1_xboole_0(k1_tarski(A_48), B_49))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.32/5.34  tff(c_1514, plain, (![A_48, B_129]: (~r2_hidden(A_48, k4_xboole_0(B_129, k1_tarski(A_48))))), inference(resolution, [status(thm)], [c_1480, c_82])).
% 12.32/5.34  tff(c_42026, plain, (![A_8467, A_8468]: (r2_hidden(A_8467, A_8468) | ~r2_hidden(A_8467, k3_xboole_0(A_8468, k1_tarski(A_8467))))), inference(resolution, [status(thm)], [c_25576, c_1514])).
% 12.32/5.34  tff(c_42088, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_42026])).
% 12.32/5.34  tff(c_42121, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_42088])).
% 12.32/5.34  tff(c_62, plain, (![C_37, A_33]: (C_37=A_33 | ~r2_hidden(C_37, k1_tarski(A_33)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.32/5.34  tff(c_42134, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42121, c_62])).
% 12.32/5.34  tff(c_42175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_42134])).
% 12.32/5.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.32/5.34  
% 12.32/5.34  Inference rules
% 12.32/5.34  ----------------------
% 12.32/5.34  #Ref     : 0
% 12.32/5.34  #Sup     : 9754
% 12.32/5.34  #Fact    : 4
% 12.32/5.34  #Define  : 0
% 12.32/5.34  #Split   : 5
% 12.32/5.34  #Chain   : 0
% 12.32/5.34  #Close   : 0
% 12.32/5.34  
% 12.32/5.34  Ordering : KBO
% 12.32/5.34  
% 12.32/5.34  Simplification rules
% 12.32/5.34  ----------------------
% 12.32/5.34  #Subsume      : 558
% 12.32/5.34  #Demod        : 10836
% 12.32/5.34  #Tautology    : 6858
% 12.32/5.34  #SimpNegUnit  : 95
% 12.32/5.34  #BackRed      : 7
% 12.32/5.34  
% 12.32/5.34  #Partial instantiations: 3632
% 12.32/5.34  #Strategies tried      : 1
% 12.32/5.34  
% 12.32/5.34  Timing (in seconds)
% 12.32/5.34  ----------------------
% 12.32/5.34  Preprocessing        : 0.36
% 12.32/5.34  Parsing              : 0.18
% 12.32/5.34  CNF conversion       : 0.03
% 12.32/5.34  Main loop            : 4.23
% 12.32/5.34  Inferencing          : 0.85
% 12.32/5.34  Reduction            : 2.38
% 12.32/5.34  Demodulation         : 2.10
% 12.32/5.34  BG Simplification    : 0.09
% 12.32/5.34  Subsumption          : 0.72
% 12.32/5.34  Abstraction          : 0.14
% 12.32/5.34  MUC search           : 0.00
% 12.32/5.34  Cooper               : 0.00
% 12.32/5.34  Total                : 4.61
% 12.32/5.34  Index Insertion      : 0.00
% 12.32/5.34  Index Deletion       : 0.00
% 12.32/5.34  Index Matching       : 0.00
% 12.32/5.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
