%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:09 EST 2020

% Result     : Theorem 8.36s
% Output     : CNFRefutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :   74 (  90 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 136 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_628,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_660,plain,(
    ! [A_82,B_83] : r1_tarski(k3_xboole_0(A_82,B_83),A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_20])).

tff(c_24,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_136,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_3088,plain,(
    ! [A_167,B_168,C_169] :
      ( ~ r1_xboole_0(A_167,k3_xboole_0(B_168,C_169))
      | ~ r1_tarski(A_167,C_169)
      | r1_xboole_0(A_167,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3155,plain,(
    ! [A_167] :
      ( ~ r1_xboole_0(A_167,k1_xboole_0)
      | ~ r1_tarski(A_167,'#skF_3')
      | r1_xboole_0(A_167,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_3088])).

tff(c_3233,plain,(
    ! [A_172] :
      ( ~ r1_tarski(A_172,'#skF_3')
      | r1_xboole_0(A_172,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3155])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3462,plain,(
    ! [A_186] :
      ( k3_xboole_0(A_186,'#skF_4') = k1_xboole_0
      | ~ r1_tarski(A_186,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3233,c_4])).

tff(c_3586,plain,(
    ! [B_188] : k3_xboole_0(k3_xboole_0('#skF_3',B_188),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_660,c_3462])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3630,plain,(
    ! [B_188] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',B_188)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3586,c_2])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [B_47,A_48] :
      ( r1_xboole_0(B_47,A_48)
      | ~ r1_xboole_0(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_103])).

tff(c_3338,plain,(
    ! [A_178,C_179,B_180] :
      ( ~ r1_xboole_0(A_178,C_179)
      | ~ r1_xboole_0(A_178,B_180)
      | r1_xboole_0(A_178,k2_xboole_0(B_180,C_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7454,plain,(
    ! [B_257,C_258,A_259] :
      ( r1_xboole_0(k2_xboole_0(B_257,C_258),A_259)
      | ~ r1_xboole_0(A_259,C_258)
      | ~ r1_xboole_0(A_259,B_257) ) ),
    inference(resolution,[status(thm)],[c_3338,c_8])).

tff(c_50,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7483,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_7454,c_50])).

tff(c_7494,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_7483])).

tff(c_7531,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_7494])).

tff(c_48,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,k1_tarski(B_38)) = A_37
      | r2_hidden(B_38,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_333,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(A_66,B_67)
      | k4_xboole_0(A_66,B_67) != A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1582,plain,(
    ! [A_133,B_134] :
      ( k3_xboole_0(A_133,B_134) = k1_xboole_0
      | k4_xboole_0(A_133,B_134) != A_133 ) ),
    inference(resolution,[status(thm)],[c_333,c_4])).

tff(c_11831,plain,(
    ! [A_321,B_322] :
      ( k3_xboole_0(A_321,k1_tarski(B_322)) = k1_xboole_0
      | r2_hidden(B_322,A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1582])).

tff(c_56,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_57,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_161,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_168,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_57,c_161])).

tff(c_11962,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11831,c_168])).

tff(c_12059,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_7531,c_11962])).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2521,plain,(
    ! [A_150,B_151,C_152] :
      ( ~ r1_xboole_0(A_150,B_151)
      | ~ r2_hidden(C_152,B_151)
      | ~ r2_hidden(C_152,A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5499,plain,(
    ! [C_226,B_227,A_228] :
      ( ~ r2_hidden(C_226,B_227)
      | ~ r2_hidden(C_226,A_228)
      | k3_xboole_0(A_228,B_227) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_2521])).

tff(c_5511,plain,(
    ! [A_228] :
      ( ~ r2_hidden('#skF_5',A_228)
      | k3_xboole_0(A_228,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_5499])).

tff(c_12081,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12059,c_5511])).

tff(c_12106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_2,c_12081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.36/2.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.36/2.97  
% 8.36/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.36/2.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.36/2.97  
% 8.36/2.97  %Foreground sorts:
% 8.36/2.97  
% 8.36/2.97  
% 8.36/2.97  %Background operators:
% 8.36/2.97  
% 8.36/2.97  
% 8.36/2.97  %Foreground operators:
% 8.36/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.36/2.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.36/2.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.36/2.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.36/2.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.36/2.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.36/2.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.36/2.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.36/2.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.36/2.97  tff('#skF_5', type, '#skF_5': $i).
% 8.36/2.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.36/2.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.36/2.97  tff('#skF_2', type, '#skF_2': $i).
% 8.36/2.97  tff('#skF_3', type, '#skF_3': $i).
% 8.36/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.36/2.97  tff('#skF_4', type, '#skF_4': $i).
% 8.36/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.36/2.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.36/2.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.36/2.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.36/2.97  
% 8.66/2.98  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.66/2.98  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.66/2.98  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.66/2.98  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.66/2.98  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.66/2.98  tff(f_89, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 8.66/2.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.66/2.98  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.66/2.98  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.66/2.98  tff(f_106, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.66/2.98  tff(f_95, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.66/2.98  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.66/2.98  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.66/2.98  tff(c_628, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.66/2.98  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.66/2.98  tff(c_660, plain, (![A_82, B_83]: (r1_tarski(k3_xboole_0(A_82, B_83), A_82))), inference(superposition, [status(thm), theory('equality')], [c_628, c_20])).
% 8.66/2.98  tff(c_24, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.66/2.98  tff(c_52, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.66/2.98  tff(c_136, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.98  tff(c_159, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_136])).
% 8.66/2.98  tff(c_3088, plain, (![A_167, B_168, C_169]: (~r1_xboole_0(A_167, k3_xboole_0(B_168, C_169)) | ~r1_tarski(A_167, C_169) | r1_xboole_0(A_167, B_168))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.66/2.98  tff(c_3155, plain, (![A_167]: (~r1_xboole_0(A_167, k1_xboole_0) | ~r1_tarski(A_167, '#skF_3') | r1_xboole_0(A_167, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_3088])).
% 8.66/2.98  tff(c_3233, plain, (![A_172]: (~r1_tarski(A_172, '#skF_3') | r1_xboole_0(A_172, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3155])).
% 8.66/2.98  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.98  tff(c_3462, plain, (![A_186]: (k3_xboole_0(A_186, '#skF_4')=k1_xboole_0 | ~r1_tarski(A_186, '#skF_3'))), inference(resolution, [status(thm)], [c_3233, c_4])).
% 8.66/2.98  tff(c_3586, plain, (![B_188]: (k3_xboole_0(k3_xboole_0('#skF_3', B_188), '#skF_4')=k1_xboole_0)), inference(resolution, [status(thm)], [c_660, c_3462])).
% 8.66/2.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.66/2.98  tff(c_3630, plain, (![B_188]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', B_188))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3586, c_2])).
% 8.66/2.98  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.98  tff(c_103, plain, (![B_47, A_48]: (r1_xboole_0(B_47, A_48) | ~r1_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.66/2.98  tff(c_111, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_103])).
% 8.66/2.98  tff(c_3338, plain, (![A_178, C_179, B_180]: (~r1_xboole_0(A_178, C_179) | ~r1_xboole_0(A_178, B_180) | r1_xboole_0(A_178, k2_xboole_0(B_180, C_179)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.66/2.98  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.66/2.98  tff(c_7454, plain, (![B_257, C_258, A_259]: (r1_xboole_0(k2_xboole_0(B_257, C_258), A_259) | ~r1_xboole_0(A_259, C_258) | ~r1_xboole_0(A_259, B_257))), inference(resolution, [status(thm)], [c_3338, c_8])).
% 8.66/2.98  tff(c_50, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.66/2.98  tff(c_7483, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_7454, c_50])).
% 8.66/2.98  tff(c_7494, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_7483])).
% 8.66/2.98  tff(c_7531, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_7494])).
% 8.66/2.98  tff(c_48, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k1_tarski(B_38))=A_37 | r2_hidden(B_38, A_37))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.66/2.98  tff(c_333, plain, (![A_66, B_67]: (r1_xboole_0(A_66, B_67) | k4_xboole_0(A_66, B_67)!=A_66)), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.66/2.98  tff(c_1582, plain, (![A_133, B_134]: (k3_xboole_0(A_133, B_134)=k1_xboole_0 | k4_xboole_0(A_133, B_134)!=A_133)), inference(resolution, [status(thm)], [c_333, c_4])).
% 8.66/2.98  tff(c_11831, plain, (![A_321, B_322]: (k3_xboole_0(A_321, k1_tarski(B_322))=k1_xboole_0 | r2_hidden(B_322, A_321))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1582])).
% 8.66/2.98  tff(c_56, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.66/2.98  tff(c_57, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 8.66/2.98  tff(c_161, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.66/2.98  tff(c_168, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_57, c_161])).
% 8.66/2.98  tff(c_11962, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11831, c_168])).
% 8.66/2.98  tff(c_12059, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_7531, c_11962])).
% 8.66/2.98  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.66/2.98  tff(c_2521, plain, (![A_150, B_151, C_152]: (~r1_xboole_0(A_150, B_151) | ~r2_hidden(C_152, B_151) | ~r2_hidden(C_152, A_150))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.66/2.98  tff(c_5499, plain, (![C_226, B_227, A_228]: (~r2_hidden(C_226, B_227) | ~r2_hidden(C_226, A_228) | k3_xboole_0(A_228, B_227)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2521])).
% 8.66/2.98  tff(c_5511, plain, (![A_228]: (~r2_hidden('#skF_5', A_228) | k3_xboole_0(A_228, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_5499])).
% 8.66/2.98  tff(c_12081, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12059, c_5511])).
% 8.66/2.98  tff(c_12106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3630, c_2, c_12081])).
% 8.66/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.66/2.98  
% 8.66/2.98  Inference rules
% 8.66/2.98  ----------------------
% 8.66/2.98  #Ref     : 1
% 8.66/2.98  #Sup     : 2978
% 8.66/2.98  #Fact    : 0
% 8.66/2.98  #Define  : 0
% 8.66/2.98  #Split   : 4
% 8.66/2.98  #Chain   : 0
% 8.66/2.98  #Close   : 0
% 8.66/2.98  
% 8.66/2.98  Ordering : KBO
% 8.66/2.98  
% 8.66/2.98  Simplification rules
% 8.66/2.98  ----------------------
% 8.66/2.98  #Subsume      : 505
% 8.66/2.98  #Demod        : 1877
% 8.66/2.98  #Tautology    : 1744
% 8.66/2.98  #SimpNegUnit  : 55
% 8.66/2.98  #BackRed      : 1
% 8.66/2.98  
% 8.66/2.98  #Partial instantiations: 0
% 8.66/2.98  #Strategies tried      : 1
% 8.66/2.98  
% 8.66/2.98  Timing (in seconds)
% 8.66/2.98  ----------------------
% 8.66/2.99  Preprocessing        : 0.43
% 8.66/2.99  Parsing              : 0.25
% 8.66/2.99  CNF conversion       : 0.03
% 8.66/2.99  Main loop            : 1.74
% 8.66/2.99  Inferencing          : 0.45
% 8.66/2.99  Reduction            : 0.80
% 8.66/2.99  Demodulation         : 0.63
% 8.66/2.99  BG Simplification    : 0.05
% 8.66/2.99  Subsumption          : 0.33
% 8.66/2.99  Abstraction          : 0.07
% 8.66/2.99  MUC search           : 0.00
% 8.66/2.99  Cooper               : 0.00
% 8.66/2.99  Total                : 2.20
% 8.66/2.99  Index Insertion      : 0.00
% 8.66/2.99  Index Deletion       : 0.00
% 8.66/2.99  Index Matching       : 0.00
% 8.66/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
