%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:18 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 152 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 344 expanded)
%              Number of equality atoms :   66 ( 255 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_84,plain,
    ( k1_xboole_0 != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_99,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_479,plain,(
    ! [A_133,B_134] :
      ( k2_xboole_0(A_133,B_134) = B_134
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_491,plain,(
    ! [B_15] : k2_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_479])).

tff(c_86,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_109,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_90,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_115,plain,(
    ! [A_67,B_68] : r1_tarski(A_67,k2_xboole_0(A_67,B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_115])).

tff(c_430,plain,(
    ! [B_120,A_121] :
      ( k1_tarski(B_120) = A_121
      | k1_xboole_0 = A_121
      | ~ r1_tarski(A_121,k1_tarski(B_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_433,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_118,c_430])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_99,c_433])).

tff(c_446,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_468,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | A_12 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_26])).

tff(c_664,plain,(
    ! [D_170,B_171,A_172] :
      ( ~ r2_hidden(D_170,B_171)
      | r2_hidden(D_170,k2_xboole_0(A_172,B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_677,plain,(
    ! [D_170] :
      ( ~ r2_hidden(D_170,'#skF_9')
      | r2_hidden(D_170,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_664])).

tff(c_56,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_685,plain,(
    ! [D_174,B_175,A_176] :
      ( D_174 = B_175
      | D_174 = A_176
      | ~ r2_hidden(D_174,k2_tarski(A_176,B_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_763,plain,(
    ! [D_179,A_180] :
      ( D_179 = A_180
      | D_179 = A_180
      | ~ r2_hidden(D_179,k1_tarski(A_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_685])).

tff(c_787,plain,(
    ! [D_181] :
      ( D_181 = '#skF_7'
      | ~ r2_hidden(D_181,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_677,c_763])).

tff(c_797,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_468,c_787])).

tff(c_813,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_820,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_90])).

tff(c_822,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_820])).

tff(c_824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_822])).

tff(c_826,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_445,plain,(
    k1_tarski('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_679,plain,(
    ! [D_173] :
      ( ~ r2_hidden(D_173,'#skF_9')
      | r2_hidden(D_173,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_664])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_798,plain,(
    ! [A_182] :
      ( r1_tarski(A_182,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_182,k1_tarski('#skF_7')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_679,c_4])).

tff(c_803,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_798])).

tff(c_70,plain,(
    ! [B_55,A_54] :
      ( k1_tarski(B_55) = A_54
      | k1_xboole_0 = A_54
      | ~ r1_tarski(A_54,k1_tarski(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2092,plain,(
    ! [B_6860,A_6861] :
      ( k1_tarski(B_6860) = A_6861
      | A_6861 = '#skF_8'
      | ~ r1_tarski(A_6861,k1_tarski(B_6860)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_70])).

tff(c_2107,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_803,c_2092])).

tff(c_2123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_826,c_445,c_2107])).

tff(c_2124,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2125,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2167,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_2125,c_88])).

tff(c_2126,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_90])).

tff(c_2422,plain,(
    ! [D_7019,B_7020,A_7021] :
      ( ~ r2_hidden(D_7019,B_7020)
      | r2_hidden(D_7019,k2_xboole_0(A_7021,B_7020)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2440,plain,(
    ! [D_7022] :
      ( ~ r2_hidden(D_7022,'#skF_9')
      | r2_hidden(D_7022,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2126,c_2422])).

tff(c_2522,plain,(
    ! [B_7025] :
      ( r2_hidden('#skF_1'('#skF_9',B_7025),'#skF_8')
      | r1_tarski('#skF_9',B_7025) ) ),
    inference(resolution,[status(thm)],[c_6,c_2440])).

tff(c_2527,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_2522,c_4])).

tff(c_2824,plain,(
    ! [B_7050,A_7051] :
      ( k1_tarski(B_7050) = A_7051
      | k1_xboole_0 = A_7051
      | ~ r1_tarski(A_7051,k1_tarski(B_7050)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2827,plain,(
    ! [A_7051] :
      ( k1_tarski('#skF_7') = A_7051
      | k1_xboole_0 = A_7051
      | ~ r1_tarski(A_7051,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2125,c_2824])).

tff(c_2840,plain,(
    ! [A_7052] :
      ( A_7052 = '#skF_8'
      | k1_xboole_0 = A_7052
      | ~ r1_tarski(A_7052,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_2827])).

tff(c_2843,plain,
    ( '#skF_9' = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2527,c_2840])).

tff(c_2854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2124,c_2167,c_2843])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.71  
% 4.06/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.72  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 4.06/1.72  
% 4.06/1.72  %Foreground sorts:
% 4.06/1.72  
% 4.06/1.72  
% 4.06/1.72  %Background operators:
% 4.06/1.72  
% 4.06/1.72  
% 4.06/1.72  %Foreground operators:
% 4.06/1.72  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.06/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.72  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.06/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.06/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.06/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.06/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.06/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.06/1.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.06/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.06/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.06/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.06/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.06/1.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.06/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.06/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.06/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.06/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.06/1.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.06/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.06/1.72  
% 4.06/1.73  tff(f_117, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.06/1.73  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.06/1.73  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.06/1.73  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.06/1.73  tff(f_90, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.06/1.73  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.06/1.73  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.06/1.73  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.06/1.73  tff(f_70, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.06/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.06/1.73  tff(c_84, plain, (k1_xboole_0!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.06/1.73  tff(c_99, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_84])).
% 4.06/1.73  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.06/1.73  tff(c_479, plain, (![A_133, B_134]: (k2_xboole_0(A_133, B_134)=B_134 | ~r1_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.06/1.73  tff(c_491, plain, (![B_15]: (k2_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_479])).
% 4.06/1.73  tff(c_86, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.06/1.73  tff(c_109, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_86])).
% 4.06/1.73  tff(c_90, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.06/1.73  tff(c_115, plain, (![A_67, B_68]: (r1_tarski(A_67, k2_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.06/1.73  tff(c_118, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_115])).
% 4.06/1.73  tff(c_430, plain, (![B_120, A_121]: (k1_tarski(B_120)=A_121 | k1_xboole_0=A_121 | ~r1_tarski(A_121, k1_tarski(B_120)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.73  tff(c_433, plain, (k1_tarski('#skF_7')='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_118, c_430])).
% 4.06/1.73  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_99, c_433])).
% 4.06/1.73  tff(c_446, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_86])).
% 4.06/1.73  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.73  tff(c_468, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | A_12='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_26])).
% 4.06/1.73  tff(c_664, plain, (![D_170, B_171, A_172]: (~r2_hidden(D_170, B_171) | r2_hidden(D_170, k2_xboole_0(A_172, B_171)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.06/1.73  tff(c_677, plain, (![D_170]: (~r2_hidden(D_170, '#skF_9') | r2_hidden(D_170, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_664])).
% 4.06/1.73  tff(c_56, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.06/1.73  tff(c_685, plain, (![D_174, B_175, A_176]: (D_174=B_175 | D_174=A_176 | ~r2_hidden(D_174, k2_tarski(A_176, B_175)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.06/1.73  tff(c_763, plain, (![D_179, A_180]: (D_179=A_180 | D_179=A_180 | ~r2_hidden(D_179, k1_tarski(A_180)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_685])).
% 4.06/1.73  tff(c_787, plain, (![D_181]: (D_181='#skF_7' | ~r2_hidden(D_181, '#skF_9'))), inference(resolution, [status(thm)], [c_677, c_763])).
% 4.06/1.73  tff(c_797, plain, ('#skF_4'('#skF_9')='#skF_7' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_468, c_787])).
% 4.06/1.73  tff(c_813, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_797])).
% 4.06/1.73  tff(c_820, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_813, c_90])).
% 4.06/1.73  tff(c_822, plain, (k1_tarski('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_491, c_820])).
% 4.06/1.73  tff(c_824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_822])).
% 4.06/1.73  tff(c_826, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_797])).
% 4.06/1.73  tff(c_445, plain, (k1_tarski('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_86])).
% 4.06/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.73  tff(c_679, plain, (![D_173]: (~r2_hidden(D_173, '#skF_9') | r2_hidden(D_173, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_664])).
% 4.06/1.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.73  tff(c_798, plain, (![A_182]: (r1_tarski(A_182, k1_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_182, k1_tarski('#skF_7')), '#skF_9'))), inference(resolution, [status(thm)], [c_679, c_4])).
% 4.06/1.73  tff(c_803, plain, (r1_tarski('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_798])).
% 4.06/1.73  tff(c_70, plain, (![B_55, A_54]: (k1_tarski(B_55)=A_54 | k1_xboole_0=A_54 | ~r1_tarski(A_54, k1_tarski(B_55)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.73  tff(c_2092, plain, (![B_6860, A_6861]: (k1_tarski(B_6860)=A_6861 | A_6861='#skF_8' | ~r1_tarski(A_6861, k1_tarski(B_6860)))), inference(demodulation, [status(thm), theory('equality')], [c_446, c_70])).
% 4.06/1.73  tff(c_2107, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_803, c_2092])).
% 4.06/1.73  tff(c_2123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_826, c_445, c_2107])).
% 4.06/1.73  tff(c_2124, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 4.06/1.73  tff(c_2125, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_84])).
% 4.06/1.73  tff(c_88, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.06/1.73  tff(c_2167, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2125, c_2125, c_88])).
% 4.06/1.73  tff(c_2126, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2125, c_90])).
% 4.06/1.73  tff(c_2422, plain, (![D_7019, B_7020, A_7021]: (~r2_hidden(D_7019, B_7020) | r2_hidden(D_7019, k2_xboole_0(A_7021, B_7020)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.06/1.73  tff(c_2440, plain, (![D_7022]: (~r2_hidden(D_7022, '#skF_9') | r2_hidden(D_7022, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2126, c_2422])).
% 4.06/1.73  tff(c_2522, plain, (![B_7025]: (r2_hidden('#skF_1'('#skF_9', B_7025), '#skF_8') | r1_tarski('#skF_9', B_7025))), inference(resolution, [status(thm)], [c_6, c_2440])).
% 4.06/1.73  tff(c_2527, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_2522, c_4])).
% 4.06/1.73  tff(c_2824, plain, (![B_7050, A_7051]: (k1_tarski(B_7050)=A_7051 | k1_xboole_0=A_7051 | ~r1_tarski(A_7051, k1_tarski(B_7050)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.73  tff(c_2827, plain, (![A_7051]: (k1_tarski('#skF_7')=A_7051 | k1_xboole_0=A_7051 | ~r1_tarski(A_7051, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2125, c_2824])).
% 4.06/1.73  tff(c_2840, plain, (![A_7052]: (A_7052='#skF_8' | k1_xboole_0=A_7052 | ~r1_tarski(A_7052, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2125, c_2827])).
% 4.06/1.73  tff(c_2843, plain, ('#skF_9'='#skF_8' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2527, c_2840])).
% 4.06/1.73  tff(c_2854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2124, c_2167, c_2843])).
% 4.06/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.73  
% 4.06/1.73  Inference rules
% 4.06/1.73  ----------------------
% 4.06/1.73  #Ref     : 0
% 4.06/1.73  #Sup     : 625
% 4.06/1.73  #Fact    : 0
% 4.06/1.73  #Define  : 0
% 4.06/1.73  #Split   : 5
% 4.06/1.73  #Chain   : 0
% 4.06/1.73  #Close   : 0
% 4.06/1.73  
% 4.06/1.73  Ordering : KBO
% 4.06/1.73  
% 4.06/1.73  Simplification rules
% 4.06/1.73  ----------------------
% 4.06/1.73  #Subsume      : 77
% 4.06/1.73  #Demod        : 158
% 4.06/1.73  #Tautology    : 215
% 4.06/1.73  #SimpNegUnit  : 14
% 4.06/1.73  #BackRed      : 9
% 4.06/1.73  
% 4.06/1.73  #Partial instantiations: 2480
% 4.06/1.73  #Strategies tried      : 1
% 4.06/1.73  
% 4.06/1.73  Timing (in seconds)
% 4.06/1.73  ----------------------
% 4.06/1.73  Preprocessing        : 0.34
% 4.06/1.73  Parsing              : 0.17
% 4.06/1.73  CNF conversion       : 0.03
% 4.06/1.73  Main loop            : 0.64
% 4.06/1.73  Inferencing          : 0.27
% 4.06/1.73  Reduction            : 0.18
% 4.06/1.73  Demodulation         : 0.13
% 4.06/1.73  BG Simplification    : 0.03
% 4.06/1.73  Subsumption          : 0.11
% 4.06/1.73  Abstraction          : 0.03
% 4.06/1.73  MUC search           : 0.00
% 4.06/1.73  Cooper               : 0.00
% 4.06/1.73  Total                : 1.01
% 4.06/1.73  Index Insertion      : 0.00
% 4.06/1.73  Index Deletion       : 0.00
% 4.06/1.73  Index Matching       : 0.00
% 4.06/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
