%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 100 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_48,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_178,plain,(
    ! [A_79,B_80] :
      ( ~ r1_xboole_0(A_79,B_80)
      | k3_xboole_0(A_79,B_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_182,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_178])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_183,plain,(
    ! [A_81] : k3_xboole_0(A_81,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_178])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_188,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = k4_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_10])).

tff(c_203,plain,(
    ! [A_81] : k4_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_219,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_234,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k3_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_219])).

tff(c_237,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_234])).

tff(c_42,plain,(
    ! [B_51] : k4_xboole_0(k1_tarski(B_51),k1_tarski(B_51)) != k1_tarski(B_51) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_258,plain,(
    ! [B_51] : k1_tarski(B_51) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_42])).

tff(c_50,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_317,plain,(
    ! [B_93,A_94] :
      ( k1_tarski(B_93) = A_94
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,k1_tarski(B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_327,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_317])).

tff(c_336,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_40,plain,(
    ! [A_48,B_49] : k3_xboole_0(k1_tarski(A_48),k2_tarski(A_48,B_49)) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_342,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_40])).

tff(c_348,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_342])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_348])).

tff(c_351,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_38,plain,(
    ! [A_46,B_47] : r1_tarski(k1_tarski(A_46),k2_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_362,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_38])).

tff(c_46,plain,(
    ! [B_53,A_52] :
      ( B_53 = A_52
      | ~ r1_tarski(k1_tarski(A_52),k1_tarski(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_387,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_362,c_46])).

tff(c_394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.43  
% 2.47/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.47/1.43  
% 2.47/1.43  %Foreground sorts:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Background operators:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Foreground operators:
% 2.47/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.43  
% 2.47/1.44  tff(f_95, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.47/1.44  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.47/1.44  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.44  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.47/1.44  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.47/1.44  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.47/1.44  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.47/1.44  tff(f_86, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.47/1.44  tff(f_77, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.47/1.44  tff(f_81, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.47/1.44  tff(f_79, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.47/1.44  tff(f_90, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.47/1.44  tff(c_48, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.47/1.44  tff(c_16, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.44  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.44  tff(c_103, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.44  tff(c_178, plain, (![A_79, B_80]: (~r1_xboole_0(A_79, B_80) | k3_xboole_0(A_79, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_103])).
% 2.47/1.44  tff(c_182, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_178])).
% 2.47/1.44  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.47/1.44  tff(c_183, plain, (![A_81]: (k3_xboole_0(A_81, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_178])).
% 2.47/1.44  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.44  tff(c_188, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=k4_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_183, c_10])).
% 2.47/1.44  tff(c_203, plain, (![A_81]: (k4_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_188])).
% 2.47/1.44  tff(c_219, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.44  tff(c_234, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k3_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_219])).
% 2.47/1.44  tff(c_237, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_182, c_234])).
% 2.47/1.44  tff(c_42, plain, (![B_51]: (k4_xboole_0(k1_tarski(B_51), k1_tarski(B_51))!=k1_tarski(B_51))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.44  tff(c_258, plain, (![B_51]: (k1_tarski(B_51)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_42])).
% 2.47/1.44  tff(c_50, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.47/1.44  tff(c_317, plain, (![B_93, A_94]: (k1_tarski(B_93)=A_94 | k1_xboole_0=A_94 | ~r1_tarski(A_94, k1_tarski(B_93)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.47/1.44  tff(c_327, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_317])).
% 2.47/1.44  tff(c_336, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_327])).
% 2.47/1.44  tff(c_40, plain, (![A_48, B_49]: (k3_xboole_0(k1_tarski(A_48), k2_tarski(A_48, B_49))=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.47/1.44  tff(c_342, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_336, c_40])).
% 2.47/1.44  tff(c_348, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_182, c_342])).
% 2.47/1.44  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_348])).
% 2.47/1.44  tff(c_351, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_327])).
% 2.47/1.44  tff(c_38, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), k2_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.44  tff(c_362, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_351, c_38])).
% 2.47/1.44  tff(c_46, plain, (![B_53, A_52]: (B_53=A_52 | ~r1_tarski(k1_tarski(A_52), k1_tarski(B_53)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.47/1.44  tff(c_387, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_362, c_46])).
% 2.47/1.44  tff(c_394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_387])).
% 2.47/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.44  
% 2.47/1.44  Inference rules
% 2.47/1.44  ----------------------
% 2.47/1.44  #Ref     : 0
% 2.47/1.44  #Sup     : 76
% 2.47/1.44  #Fact    : 0
% 2.47/1.44  #Define  : 0
% 2.47/1.44  #Split   : 1
% 2.47/1.44  #Chain   : 0
% 2.47/1.44  #Close   : 0
% 2.47/1.44  
% 2.47/1.44  Ordering : KBO
% 2.47/1.44  
% 2.47/1.44  Simplification rules
% 2.47/1.44  ----------------------
% 2.47/1.44  #Subsume      : 2
% 2.47/1.44  #Demod        : 19
% 2.47/1.44  #Tautology    : 55
% 2.47/1.44  #SimpNegUnit  : 6
% 2.47/1.44  #BackRed      : 5
% 2.47/1.44  
% 2.47/1.44  #Partial instantiations: 0
% 2.47/1.44  #Strategies tried      : 1
% 2.47/1.44  
% 2.47/1.44  Timing (in seconds)
% 2.47/1.44  ----------------------
% 2.47/1.45  Preprocessing        : 0.39
% 2.47/1.45  Parsing              : 0.19
% 2.47/1.45  CNF conversion       : 0.03
% 2.47/1.45  Main loop            : 0.20
% 2.47/1.45  Inferencing          : 0.07
% 2.47/1.45  Reduction            : 0.06
% 2.47/1.45  Demodulation         : 0.04
% 2.47/1.45  BG Simplification    : 0.02
% 2.47/1.45  Subsumption          : 0.03
% 2.47/1.45  Abstraction          : 0.01
% 2.47/1.45  MUC search           : 0.00
% 2.47/1.45  Cooper               : 0.00
% 2.47/1.45  Total                : 0.62
% 2.47/1.45  Index Insertion      : 0.00
% 2.47/1.45  Index Deletion       : 0.00
% 2.47/1.45  Index Matching       : 0.00
% 2.47/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
