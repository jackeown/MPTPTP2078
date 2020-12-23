%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 16.29s
% Output     : CNFRefutation 16.52s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 178 expanded)
%              Number of leaves         :   30 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :   90 ( 267 expanded)
%              Number of equality atoms :   35 ( 130 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_44,plain,(
    ! [C_29] : r2_hidden(C_29,k1_tarski(C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_116,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_tarski('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_66])).

tff(c_212,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_274,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(D_74,A_75)
      | ~ r2_hidden(D_74,k3_xboole_0(A_75,B_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_14])).

tff(c_303,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,'#skF_8')
      | ~ r2_hidden(D_77,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_274])).

tff(c_318,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_303])).

tff(c_64,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1473,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(D_130,k4_xboole_0(A_131,B_132))
      | r2_hidden(D_130,B_132)
      | ~ r2_hidden(D_130,A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16024,plain,(
    ! [D_305,A_306,B_307] :
      ( r2_hidden(D_305,k3_xboole_0(A_306,B_307))
      | r2_hidden(D_305,k4_xboole_0(A_306,B_307))
      | ~ r2_hidden(D_305,A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1473])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39374,plain,(
    ! [D_648,B_649,A_650] :
      ( ~ r2_hidden(D_648,B_649)
      | r2_hidden(D_648,k3_xboole_0(A_650,B_649))
      | ~ r2_hidden(D_648,A_650) ) ),
    inference(resolution,[status(thm)],[c_16024,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    k3_xboole_0('#skF_6','#skF_8') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_70,plain,(
    k3_xboole_0('#skF_8','#skF_6') != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_68,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_162,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_171,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_162])).

tff(c_474,plain,(
    ! [A_90,B_91,C_92] : k3_xboole_0(k3_xboole_0(A_90,B_91),C_92) = k3_xboole_0(A_90,k3_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_844,plain,(
    ! [C_104] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_7',C_104)) = k3_xboole_0('#skF_6',C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_474])).

tff(c_898,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_9')) = k3_xboole_0('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_844])).

tff(c_914,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_9')) = k3_xboole_0('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_898])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_537,plain,(
    ! [A_93,C_94] : k3_xboole_0(A_93,k3_xboole_0(A_93,C_94)) = k3_xboole_0(A_93,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_474])).

tff(c_581,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_537])).

tff(c_919,plain,(
    k3_xboole_0(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) = k3_xboole_0(k1_tarski('#skF_9'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_581])).

tff(c_937,plain,(
    k3_xboole_0(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) = k3_xboole_0('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_2,c_919])).

tff(c_190,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15270,plain,(
    ! [A_293,B_294,B_295] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_293,B_294),B_295),A_293)
      | r1_tarski(k4_xboole_0(A_293,B_294),B_295) ) ),
    inference(resolution,[status(thm)],[c_190,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15430,plain,(
    ! [A_298,B_299] : r1_tarski(k4_xboole_0(A_298,B_299),A_298) ),
    inference(resolution,[status(thm)],[c_15270,c_6])).

tff(c_15522,plain,(
    ! [A_300,B_301] : r1_tarski(k3_xboole_0(A_300,B_301),A_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_15430])).

tff(c_15646,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_6'),k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_15522])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16884,plain,
    ( k3_xboole_0('#skF_8','#skF_6') = k1_tarski('#skF_9')
    | ~ r1_tarski(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_15646,c_30])).

tff(c_16898,plain,(
    ~ r1_tarski(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_16884])).

tff(c_42,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_211,plain,(
    ! [A_25,B_62] :
      ( '#skF_1'(k1_tarski(A_25),B_62) = A_25
      | r1_tarski(k1_tarski(A_25),B_62) ) ),
    inference(resolution,[status(thm)],[c_190,c_42])).

tff(c_16906,plain,(
    '#skF_1'(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_211,c_16898])).

tff(c_22365,plain,
    ( ~ r2_hidden('#skF_9',k3_xboole_0('#skF_8','#skF_6'))
    | r1_tarski(k1_tarski('#skF_9'),k3_xboole_0('#skF_8','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16906,c_6])).

tff(c_22380,plain,(
    ~ r2_hidden('#skF_9',k3_xboole_0('#skF_8','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_16898,c_22365])).

tff(c_39399,plain,
    ( ~ r2_hidden('#skF_9','#skF_6')
    | ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_39374,c_22380])).

tff(c_39668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_64,c_39399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.29/7.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.52/7.93  
% 16.52/7.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.52/7.93  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 16.52/7.93  
% 16.52/7.93  %Foreground sorts:
% 16.52/7.93  
% 16.52/7.93  
% 16.52/7.93  %Background operators:
% 16.52/7.93  
% 16.52/7.93  
% 16.52/7.93  %Foreground operators:
% 16.52/7.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.52/7.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.52/7.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.52/7.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.52/7.93  tff('#skF_7', type, '#skF_7': $i).
% 16.52/7.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.52/7.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.52/7.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.52/7.93  tff('#skF_6', type, '#skF_6': $i).
% 16.52/7.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.52/7.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.52/7.93  tff('#skF_9', type, '#skF_9': $i).
% 16.52/7.93  tff('#skF_8', type, '#skF_8': $i).
% 16.52/7.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.52/7.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.52/7.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.52/7.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.52/7.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.52/7.93  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.52/7.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.52/7.93  
% 16.52/7.95  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 16.52/7.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.52/7.95  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 16.52/7.95  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.52/7.95  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.52/7.95  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 16.52/7.95  tff(f_54, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 16.52/7.95  tff(f_46, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 16.52/7.95  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.52/7.95  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.52/7.95  tff(c_44, plain, (![C_29]: (r2_hidden(C_29, k1_tarski(C_29)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.52/7.95  tff(c_101, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.52/7.95  tff(c_66, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.52/7.95  tff(c_116, plain, (k3_xboole_0('#skF_8', '#skF_7')=k1_tarski('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_101, c_66])).
% 16.52/7.95  tff(c_212, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.52/7.95  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.52/7.95  tff(c_274, plain, (![D_74, A_75, B_76]: (r2_hidden(D_74, A_75) | ~r2_hidden(D_74, k3_xboole_0(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_14])).
% 16.52/7.95  tff(c_303, plain, (![D_77]: (r2_hidden(D_77, '#skF_8') | ~r2_hidden(D_77, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_116, c_274])).
% 16.52/7.95  tff(c_318, plain, (r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_44, c_303])).
% 16.52/7.95  tff(c_64, plain, (r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.52/7.95  tff(c_40, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.52/7.95  tff(c_1473, plain, (![D_130, A_131, B_132]: (r2_hidden(D_130, k4_xboole_0(A_131, B_132)) | r2_hidden(D_130, B_132) | ~r2_hidden(D_130, A_131))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.52/7.95  tff(c_16024, plain, (![D_305, A_306, B_307]: (r2_hidden(D_305, k3_xboole_0(A_306, B_307)) | r2_hidden(D_305, k4_xboole_0(A_306, B_307)) | ~r2_hidden(D_305, A_306))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1473])).
% 16.52/7.95  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.52/7.95  tff(c_39374, plain, (![D_648, B_649, A_650]: (~r2_hidden(D_648, B_649) | r2_hidden(D_648, k3_xboole_0(A_650, B_649)) | ~r2_hidden(D_648, A_650))), inference(resolution, [status(thm)], [c_16024, c_12])).
% 16.52/7.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.52/7.95  tff(c_62, plain, (k3_xboole_0('#skF_6', '#skF_8')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.52/7.95  tff(c_70, plain, (k3_xboole_0('#skF_8', '#skF_6')!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 16.52/7.95  tff(c_68, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.52/7.95  tff(c_162, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.52/7.95  tff(c_171, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_68, c_162])).
% 16.52/7.95  tff(c_474, plain, (![A_90, B_91, C_92]: (k3_xboole_0(k3_xboole_0(A_90, B_91), C_92)=k3_xboole_0(A_90, k3_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.52/7.95  tff(c_844, plain, (![C_104]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_7', C_104))=k3_xboole_0('#skF_6', C_104))), inference(superposition, [status(thm), theory('equality')], [c_171, c_474])).
% 16.52/7.95  tff(c_898, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_9'))=k3_xboole_0('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_66, c_844])).
% 16.52/7.95  tff(c_914, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_9'))=k3_xboole_0('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_898])).
% 16.52/7.95  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.52/7.95  tff(c_537, plain, (![A_93, C_94]: (k3_xboole_0(A_93, k3_xboole_0(A_93, C_94))=k3_xboole_0(A_93, C_94))), inference(superposition, [status(thm), theory('equality')], [c_28, c_474])).
% 16.52/7.95  tff(c_581, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_537])).
% 16.52/7.95  tff(c_919, plain, (k3_xboole_0(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))=k3_xboole_0(k1_tarski('#skF_9'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_914, c_581])).
% 16.52/7.95  tff(c_937, plain, (k3_xboole_0(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))=k3_xboole_0('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_914, c_2, c_919])).
% 16.52/7.95  tff(c_190, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.52/7.95  tff(c_15270, plain, (![A_293, B_294, B_295]: (r2_hidden('#skF_1'(k4_xboole_0(A_293, B_294), B_295), A_293) | r1_tarski(k4_xboole_0(A_293, B_294), B_295))), inference(resolution, [status(thm)], [c_190, c_14])).
% 16.52/7.95  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.52/7.95  tff(c_15430, plain, (![A_298, B_299]: (r1_tarski(k4_xboole_0(A_298, B_299), A_298))), inference(resolution, [status(thm)], [c_15270, c_6])).
% 16.52/7.95  tff(c_15522, plain, (![A_300, B_301]: (r1_tarski(k3_xboole_0(A_300, B_301), A_300))), inference(superposition, [status(thm), theory('equality')], [c_40, c_15430])).
% 16.52/7.95  tff(c_15646, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_6'), k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_937, c_15522])).
% 16.52/7.95  tff(c_30, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.52/7.95  tff(c_16884, plain, (k3_xboole_0('#skF_8', '#skF_6')=k1_tarski('#skF_9') | ~r1_tarski(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_15646, c_30])).
% 16.52/7.95  tff(c_16898, plain, (~r1_tarski(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_16884])).
% 16.52/7.95  tff(c_42, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.52/7.95  tff(c_211, plain, (![A_25, B_62]: ('#skF_1'(k1_tarski(A_25), B_62)=A_25 | r1_tarski(k1_tarski(A_25), B_62))), inference(resolution, [status(thm)], [c_190, c_42])).
% 16.52/7.95  tff(c_16906, plain, ('#skF_1'(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))='#skF_9'), inference(resolution, [status(thm)], [c_211, c_16898])).
% 16.52/7.95  tff(c_22365, plain, (~r2_hidden('#skF_9', k3_xboole_0('#skF_8', '#skF_6')) | r1_tarski(k1_tarski('#skF_9'), k3_xboole_0('#skF_8', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16906, c_6])).
% 16.52/7.95  tff(c_22380, plain, (~r2_hidden('#skF_9', k3_xboole_0('#skF_8', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_16898, c_22365])).
% 16.52/7.95  tff(c_39399, plain, (~r2_hidden('#skF_9', '#skF_6') | ~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_39374, c_22380])).
% 16.52/7.95  tff(c_39668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_64, c_39399])).
% 16.52/7.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.52/7.95  
% 16.52/7.95  Inference rules
% 16.52/7.95  ----------------------
% 16.52/7.95  #Ref     : 0
% 16.52/7.95  #Sup     : 9709
% 16.52/7.95  #Fact    : 0
% 16.52/7.95  #Define  : 0
% 16.52/7.95  #Split   : 3
% 16.52/7.95  #Chain   : 0
% 16.52/7.95  #Close   : 0
% 16.52/7.95  
% 16.52/7.95  Ordering : KBO
% 16.52/7.95  
% 16.52/7.95  Simplification rules
% 16.52/7.95  ----------------------
% 16.52/7.95  #Subsume      : 1625
% 16.52/7.95  #Demod        : 9279
% 16.52/7.95  #Tautology    : 3397
% 16.52/7.95  #SimpNegUnit  : 19
% 16.52/7.95  #BackRed      : 31
% 16.52/7.95  
% 16.52/7.95  #Partial instantiations: 0
% 16.52/7.95  #Strategies tried      : 1
% 16.52/7.95  
% 16.52/7.95  Timing (in seconds)
% 16.52/7.95  ----------------------
% 16.52/7.95  Preprocessing        : 0.34
% 16.52/7.95  Parsing              : 0.17
% 16.52/7.95  CNF conversion       : 0.03
% 16.52/7.95  Main loop            : 6.84
% 16.52/7.95  Inferencing          : 1.04
% 16.52/7.95  Reduction            : 3.75
% 16.52/7.95  Demodulation         : 3.27
% 16.52/7.95  BG Simplification    : 0.14
% 16.52/7.95  Subsumption          : 1.57
% 16.52/7.95  Abstraction          : 0.18
% 16.52/7.95  MUC search           : 0.00
% 16.52/7.95  Cooper               : 0.00
% 16.52/7.95  Total                : 7.21
% 16.52/7.95  Index Insertion      : 0.00
% 16.52/7.95  Index Deletion       : 0.00
% 16.52/7.95  Index Matching       : 0.00
% 16.52/7.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
