%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:25 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 264 expanded)
%              Number of leaves         :   33 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 447 expanded)
%              Number of equality atoms :   27 ( 187 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tarski(A_47),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_242,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_255,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_242])).

tff(c_263,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_267,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_263])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_106,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_120,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_57,c_106])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_268,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_336,plain,(
    ! [B_95,A_96,C_97] :
      ( ~ r1_xboole_0(B_95,A_96)
      | ~ r2_hidden(C_97,k3_xboole_0(A_96,B_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_268])).

tff(c_345,plain,(
    ! [C_97] :
      ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
      | ~ r2_hidden(C_97,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_336])).

tff(c_366,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_369,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_366])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_369])).

tff(c_376,plain,(
    ! [C_101] : ~ r2_hidden(C_101,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_380,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_376])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_380])).

tff(c_385,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_389,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_50])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_456,plain,(
    ! [A_105] :
      ( r1_tarski(A_105,'#skF_4')
      | ~ r1_tarski(A_105,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_16])).

tff(c_466,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_456])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_468,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_466,c_10])).

tff(c_474,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_468])).

tff(c_416,plain,(
    ! [B_50] :
      ( r1_xboole_0('#skF_4',B_50)
      | r2_hidden('#skF_3',B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_40])).

tff(c_605,plain,(
    ! [B_118] :
      ( r1_tarski('#skF_4',B_118)
      | ~ r2_hidden('#skF_3',B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_38])).

tff(c_631,plain,(
    ! [B_50] :
      ( r1_tarski('#skF_4',B_50)
      | r1_xboole_0('#skF_4',B_50) ) ),
    inference(resolution,[status(thm)],[c_416,c_605])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_475,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_466,c_18])).

tff(c_486,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_2])).

tff(c_503,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,k3_xboole_0(A_106,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_506,plain,(
    ! [C_108] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_108,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_503])).

tff(c_703,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_712,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_631,c_703])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_712])).

tff(c_717,plain,(
    ! [C_108] : ~ r2_hidden(C_108,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_509,plain,(
    ! [C_108] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_108,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_503])).

tff(c_668,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_669,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_1'(A_121,B_122),k3_xboole_0(A_121,B_122))
      | r1_xboole_0(A_121,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_681,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_4'),'#skF_5')
    | r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_669])).

tff(c_698,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_668,c_681])).

tff(c_720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_717,c_698])).

tff(c_723,plain,(
    ! [C_124] : ~ r2_hidden(C_124,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_735,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_723])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:32:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.50  
% 2.96/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.96/1.50  
% 2.96/1.50  %Foreground sorts:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Background operators:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Foreground operators:
% 2.96/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.96/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.96/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.50  
% 2.96/1.52  tff(f_103, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.96/1.52  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.96/1.52  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.96/1.52  tff(f_83, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.96/1.52  tff(f_65, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.96/1.52  tff(f_88, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.96/1.52  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.96/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.96/1.52  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.96/1.52  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.96/1.52  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.96/1.52  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_48, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.96/1.52  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.96/1.52  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.96/1.52  tff(c_38, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.52  tff(c_50, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.96/1.52  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.52  tff(c_57, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_20])).
% 2.96/1.52  tff(c_242, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.96/1.52  tff(c_255, plain, (k1_tarski('#skF_3')='#skF_4' | ~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_57, c_242])).
% 2.96/1.52  tff(c_263, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_255])).
% 2.96/1.52  tff(c_267, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_263])).
% 2.96/1.52  tff(c_40, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.96/1.52  tff(c_106, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.52  tff(c_120, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_57, c_106])).
% 2.96/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.52  tff(c_268, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.52  tff(c_336, plain, (![B_95, A_96, C_97]: (~r1_xboole_0(B_95, A_96) | ~r2_hidden(C_97, k3_xboole_0(A_96, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_268])).
% 2.96/1.52  tff(c_345, plain, (![C_97]: (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | ~r2_hidden(C_97, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_336])).
% 2.96/1.52  tff(c_366, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_345])).
% 2.96/1.52  tff(c_369, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_366])).
% 2.96/1.52  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_369])).
% 2.96/1.52  tff(c_376, plain, (![C_101]: (~r2_hidden(C_101, '#skF_4'))), inference(splitRight, [status(thm)], [c_345])).
% 2.96/1.52  tff(c_380, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_376])).
% 2.96/1.52  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_380])).
% 2.96/1.52  tff(c_385, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_255])).
% 2.96/1.52  tff(c_389, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_385, c_50])).
% 2.96/1.52  tff(c_16, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.52  tff(c_456, plain, (![A_105]: (r1_tarski(A_105, '#skF_4') | ~r1_tarski(A_105, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_389, c_16])).
% 2.96/1.52  tff(c_466, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_14, c_456])).
% 2.96/1.52  tff(c_10, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.96/1.52  tff(c_468, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_466, c_10])).
% 2.96/1.52  tff(c_474, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_468])).
% 2.96/1.52  tff(c_416, plain, (![B_50]: (r1_xboole_0('#skF_4', B_50) | r2_hidden('#skF_3', B_50))), inference(superposition, [status(thm), theory('equality')], [c_385, c_40])).
% 2.96/1.52  tff(c_605, plain, (![B_118]: (r1_tarski('#skF_4', B_118) | ~r2_hidden('#skF_3', B_118))), inference(superposition, [status(thm), theory('equality')], [c_385, c_38])).
% 2.96/1.52  tff(c_631, plain, (![B_50]: (r1_tarski('#skF_4', B_50) | r1_xboole_0('#skF_4', B_50))), inference(resolution, [status(thm)], [c_416, c_605])).
% 2.96/1.52  tff(c_18, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.52  tff(c_475, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_466, c_18])).
% 2.96/1.52  tff(c_486, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_475, c_2])).
% 2.96/1.52  tff(c_503, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, k3_xboole_0(A_106, B_107)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.52  tff(c_506, plain, (![C_108]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_108, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_486, c_503])).
% 2.96/1.52  tff(c_703, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_506])).
% 2.96/1.52  tff(c_712, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_631, c_703])).
% 2.96/1.52  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_712])).
% 2.96/1.52  tff(c_717, plain, (![C_108]: (~r2_hidden(C_108, '#skF_5'))), inference(splitRight, [status(thm)], [c_506])).
% 2.96/1.52  tff(c_509, plain, (![C_108]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_108, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_503])).
% 2.96/1.52  tff(c_668, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_509])).
% 2.96/1.52  tff(c_669, plain, (![A_121, B_122]: (r2_hidden('#skF_1'(A_121, B_122), k3_xboole_0(A_121, B_122)) | r1_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.52  tff(c_681, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_4'), '#skF_5') | r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_475, c_669])).
% 2.96/1.52  tff(c_698, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_668, c_681])).
% 2.96/1.52  tff(c_720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_717, c_698])).
% 2.96/1.52  tff(c_723, plain, (![C_124]: (~r2_hidden(C_124, '#skF_5'))), inference(splitRight, [status(thm)], [c_509])).
% 2.96/1.52  tff(c_735, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8, c_723])).
% 2.96/1.52  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_735])).
% 2.96/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.52  
% 2.96/1.52  Inference rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Ref     : 0
% 2.96/1.52  #Sup     : 164
% 2.96/1.52  #Fact    : 0
% 2.96/1.52  #Define  : 0
% 2.96/1.52  #Split   : 5
% 2.96/1.52  #Chain   : 0
% 2.96/1.52  #Close   : 0
% 2.96/1.52  
% 2.96/1.52  Ordering : KBO
% 2.96/1.52  
% 2.96/1.52  Simplification rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Subsume      : 10
% 2.96/1.52  #Demod        : 42
% 2.96/1.52  #Tautology    : 76
% 2.96/1.52  #SimpNegUnit  : 8
% 2.96/1.52  #BackRed      : 4
% 2.96/1.52  
% 2.96/1.52  #Partial instantiations: 0
% 2.96/1.52  #Strategies tried      : 1
% 2.96/1.52  
% 2.96/1.52  Timing (in seconds)
% 2.96/1.52  ----------------------
% 2.96/1.52  Preprocessing        : 0.34
% 2.96/1.52  Parsing              : 0.19
% 2.96/1.52  CNF conversion       : 0.02
% 2.96/1.52  Main loop            : 0.34
% 2.96/1.52  Inferencing          : 0.13
% 2.96/1.52  Reduction            : 0.11
% 2.96/1.52  Demodulation         : 0.08
% 2.96/1.52  BG Simplification    : 0.02
% 2.96/1.52  Subsumption          : 0.06
% 2.96/1.52  Abstraction          : 0.02
% 2.96/1.52  MUC search           : 0.00
% 2.96/1.52  Cooper               : 0.00
% 2.96/1.52  Total                : 0.72
% 2.96/1.52  Index Insertion      : 0.00
% 2.96/1.52  Index Deletion       : 0.00
% 2.96/1.52  Index Matching       : 0.00
% 2.96/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
