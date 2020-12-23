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
% DateTime   : Thu Dec  3 09:50:23 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 190 expanded)
%              Number of leaves         :   32 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 304 expanded)
%              Number of equality atoms :   44 ( 168 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tarski(A_47),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_75,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_75])).

tff(c_305,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_321,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_305])).

tff(c_331,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_335,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_331])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_381,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_409,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95),B_96)
      | ~ r1_tarski(A_95,B_96)
      | k1_xboole_0 = A_95 ) ),
    inference(resolution,[status(thm)],[c_8,c_381])).

tff(c_20,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2543,plain,(
    ! [A_3008,A_3009] :
      ( A_3008 = '#skF_2'(A_3009)
      | ~ r1_tarski(A_3009,k1_tarski(A_3008))
      | k1_xboole_0 = A_3009 ) ),
    inference(resolution,[status(thm)],[c_409,c_20])).

tff(c_2561,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_2543])).

tff(c_2573,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2561])).

tff(c_2581,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2573,c_8])).

tff(c_2586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_335,c_2581])).

tff(c_2587,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_18,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_211,plain,(
    ! [B_76,A_77] : k3_tarski(k2_tarski(B_76,A_77)) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_50,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_237,plain,(
    ! [B_78,A_79] : k2_xboole_0(B_78,A_79) = k2_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_50])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_284,plain,(
    ! [A_80,B_81] : r1_tarski(A_80,k2_xboole_0(B_81,A_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_16])).

tff(c_300,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_284])).

tff(c_2589,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2587,c_300])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2630,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_2589,c_10])).

tff(c_2633,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2630])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2697,plain,(
    ! [C_3108] :
      ( C_3108 = '#skF_5'
      | ~ r2_hidden(C_3108,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2587,c_20])).

tff(c_2843,plain,(
    ! [B_3118] :
      ( '#skF_1'('#skF_6',B_3118) = '#skF_5'
      | r1_tarski('#skF_6',B_3118) ) ),
    inference(resolution,[status(thm)],[c_6,c_2697])).

tff(c_2853,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2843,c_2633])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2858,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2853,c_4])).

tff(c_2864,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2633,c_2858])).

tff(c_2675,plain,(
    ! [C_3105,B_3106,A_3107] :
      ( r2_hidden(C_3105,B_3106)
      | ~ r2_hidden(C_3105,A_3107)
      | ~ r1_tarski(A_3107,B_3106) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4947,plain,(
    ! [A_7240,B_7241] :
      ( r2_hidden('#skF_2'(A_7240),B_7241)
      | ~ r1_tarski(A_7240,B_7241)
      | k1_xboole_0 = A_7240 ) ),
    inference(resolution,[status(thm)],[c_8,c_2675])).

tff(c_2614,plain,(
    ! [C_18] :
      ( C_18 = '#skF_5'
      | ~ r2_hidden(C_18,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2587,c_20])).

tff(c_4969,plain,(
    ! [A_7288] :
      ( '#skF_2'(A_7288) = '#skF_5'
      | ~ r1_tarski(A_7288,'#skF_6')
      | k1_xboole_0 = A_7288 ) ),
    inference(resolution,[status(thm)],[c_4947,c_2614])).

tff(c_4976,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2589,c_4969])).

tff(c_4990,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4976])).

tff(c_5001,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_4990,c_8])).

tff(c_5006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2864,c_5001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:51:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/1.94  
% 4.94/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/1.94  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 4.94/1.94  
% 4.94/1.94  %Foreground sorts:
% 4.94/1.94  
% 4.94/1.94  
% 4.94/1.94  %Background operators:
% 4.94/1.94  
% 4.94/1.94  
% 4.94/1.94  %Foreground operators:
% 4.94/1.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.94/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.94/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.94/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/1.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.94/1.94  tff('#skF_7', type, '#skF_7': $i).
% 4.94/1.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.94/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.94/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.94/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.94/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.94/1.94  tff('#skF_6', type, '#skF_6': $i).
% 4.94/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.94/1.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.94/1.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.94/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.94/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.94/1.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.94/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.94/1.94  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.94/1.94  
% 4.94/1.96  tff(f_90, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 4.94/1.96  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.94/1.96  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.94/1.96  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.94/1.96  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.94/1.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.94/1.96  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.94/1.96  tff(f_50, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.94/1.96  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.94/1.96  tff(c_52, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.94/1.96  tff(c_56, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.94/1.96  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.94/1.96  tff(c_48, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.94/1.96  tff(c_58, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.94/1.96  tff(c_75, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.94/1.96  tff(c_78, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_75])).
% 4.94/1.96  tff(c_305, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.94/1.96  tff(c_321, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_78, c_305])).
% 4.94/1.96  tff(c_331, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_321])).
% 4.94/1.96  tff(c_335, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_331])).
% 4.94/1.96  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.94/1.96  tff(c_381, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.94/1.96  tff(c_409, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95), B_96) | ~r1_tarski(A_95, B_96) | k1_xboole_0=A_95)), inference(resolution, [status(thm)], [c_8, c_381])).
% 4.94/1.96  tff(c_20, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.94/1.96  tff(c_2543, plain, (![A_3008, A_3009]: (A_3008='#skF_2'(A_3009) | ~r1_tarski(A_3009, k1_tarski(A_3008)) | k1_xboole_0=A_3009)), inference(resolution, [status(thm)], [c_409, c_20])).
% 4.94/1.96  tff(c_2561, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_78, c_2543])).
% 4.94/1.96  tff(c_2573, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_2561])).
% 4.94/1.96  tff(c_2581, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2573, c_8])).
% 4.94/1.96  tff(c_2586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_335, c_2581])).
% 4.94/1.96  tff(c_2587, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_321])).
% 4.94/1.96  tff(c_18, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.94/1.96  tff(c_124, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.94/1.96  tff(c_211, plain, (![B_76, A_77]: (k3_tarski(k2_tarski(B_76, A_77))=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_18, c_124])).
% 4.94/1.96  tff(c_50, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.94/1.96  tff(c_237, plain, (![B_78, A_79]: (k2_xboole_0(B_78, A_79)=k2_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_211, c_50])).
% 4.94/1.96  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.94/1.96  tff(c_284, plain, (![A_80, B_81]: (r1_tarski(A_80, k2_xboole_0(B_81, A_80)))), inference(superposition, [status(thm), theory('equality')], [c_237, c_16])).
% 4.94/1.96  tff(c_300, plain, (r1_tarski('#skF_7', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_284])).
% 4.94/1.96  tff(c_2589, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2587, c_300])).
% 4.94/1.96  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.94/1.96  tff(c_2630, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_2589, c_10])).
% 4.94/1.96  tff(c_2633, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_2630])).
% 4.94/1.96  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.94/1.96  tff(c_2697, plain, (![C_3108]: (C_3108='#skF_5' | ~r2_hidden(C_3108, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2587, c_20])).
% 4.94/1.96  tff(c_2843, plain, (![B_3118]: ('#skF_1'('#skF_6', B_3118)='#skF_5' | r1_tarski('#skF_6', B_3118))), inference(resolution, [status(thm)], [c_6, c_2697])).
% 4.94/1.96  tff(c_2853, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_2843, c_2633])).
% 4.94/1.96  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.94/1.96  tff(c_2858, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2853, c_4])).
% 4.94/1.96  tff(c_2864, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2633, c_2858])).
% 4.94/1.96  tff(c_2675, plain, (![C_3105, B_3106, A_3107]: (r2_hidden(C_3105, B_3106) | ~r2_hidden(C_3105, A_3107) | ~r1_tarski(A_3107, B_3106))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.94/1.96  tff(c_4947, plain, (![A_7240, B_7241]: (r2_hidden('#skF_2'(A_7240), B_7241) | ~r1_tarski(A_7240, B_7241) | k1_xboole_0=A_7240)), inference(resolution, [status(thm)], [c_8, c_2675])).
% 4.94/1.96  tff(c_2614, plain, (![C_18]: (C_18='#skF_5' | ~r2_hidden(C_18, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2587, c_20])).
% 4.94/1.96  tff(c_4969, plain, (![A_7288]: ('#skF_2'(A_7288)='#skF_5' | ~r1_tarski(A_7288, '#skF_6') | k1_xboole_0=A_7288)), inference(resolution, [status(thm)], [c_4947, c_2614])).
% 4.94/1.96  tff(c_4976, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2589, c_4969])).
% 4.94/1.96  tff(c_4990, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_52, c_4976])).
% 4.94/1.96  tff(c_5001, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_4990, c_8])).
% 4.94/1.96  tff(c_5006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2864, c_5001])).
% 4.94/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/1.96  
% 4.94/1.96  Inference rules
% 4.94/1.96  ----------------------
% 4.94/1.96  #Ref     : 0
% 4.94/1.96  #Sup     : 692
% 4.94/1.96  #Fact    : 0
% 4.94/1.96  #Define  : 0
% 4.94/1.96  #Split   : 10
% 4.94/1.96  #Chain   : 0
% 4.94/1.96  #Close   : 0
% 4.94/1.96  
% 4.94/1.96  Ordering : KBO
% 4.94/1.96  
% 4.94/1.96  Simplification rules
% 4.94/1.96  ----------------------
% 4.94/1.96  #Subsume      : 58
% 4.94/1.96  #Demod        : 216
% 4.94/1.96  #Tautology    : 258
% 4.94/1.96  #SimpNegUnit  : 35
% 4.94/1.96  #BackRed      : 3
% 4.94/1.96  
% 4.94/1.96  #Partial instantiations: 2772
% 4.94/1.96  #Strategies tried      : 1
% 4.94/1.96  
% 4.94/1.96  Timing (in seconds)
% 4.94/1.96  ----------------------
% 4.94/1.96  Preprocessing        : 0.32
% 4.94/1.96  Parsing              : 0.17
% 4.94/1.96  CNF conversion       : 0.02
% 4.94/1.96  Main loop            : 0.89
% 4.94/1.96  Inferencing          : 0.42
% 4.94/1.96  Reduction            : 0.26
% 4.94/1.96  Demodulation         : 0.19
% 4.94/1.96  BG Simplification    : 0.03
% 4.94/1.96  Subsumption          : 0.12
% 4.94/1.96  Abstraction          : 0.03
% 4.94/1.96  MUC search           : 0.00
% 4.94/1.96  Cooper               : 0.00
% 4.94/1.96  Total                : 1.24
% 4.94/1.96  Index Insertion      : 0.00
% 4.94/1.96  Index Deletion       : 0.00
% 4.94/1.96  Index Matching       : 0.00
% 4.94/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
