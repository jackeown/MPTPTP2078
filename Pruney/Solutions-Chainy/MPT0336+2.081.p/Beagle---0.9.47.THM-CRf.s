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
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 6.46s
% Output     : CNFRefutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 168 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 223 expanded)
%              Number of equality atoms :   28 (  91 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_340,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_18] : r1_xboole_0(k1_xboole_0,A_18) ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_167,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = A_48
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_188,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_167])).

tff(c_377,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_188])).

tff(c_403,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_377])).

tff(c_372,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_340])).

tff(c_505,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_372])).

tff(c_651,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,k1_tarski(B_82)) = A_81
      | r2_hidden(B_82,A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_664,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,A_81) = k3_xboole_0(A_81,k1_tarski(B_82))
      | r2_hidden(B_82,A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_18])).

tff(c_4155,plain,(
    ! [A_163,B_164] :
      ( k3_xboole_0(A_163,k1_tarski(B_164)) = k1_xboole_0
      | r2_hidden(B_164,A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_664])).

tff(c_954,plain,(
    ! [A_100,B_101,C_102] : k3_xboole_0(k3_xboole_0(A_100,B_101),C_102) = k3_xboole_0(A_100,k3_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2845,plain,(
    ! [B_151,A_152,C_153] : k3_xboole_0(k3_xboole_0(B_151,A_152),C_153) = k3_xboole_0(A_152,k3_xboole_0(B_151,C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_954])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_51,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_222,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_226,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_222])).

tff(c_2964,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',k1_tarski('#skF_5'))) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2845,c_226])).

tff(c_4174,plain,
    ( k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4155,c_2964])).

tff(c_4312,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_4174])).

tff(c_4340,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4312])).

tff(c_46,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_700,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_729,plain,(
    ! [C_88] :
      ( ~ r2_hidden(C_88,'#skF_3')
      | ~ r2_hidden(C_88,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_700])).

tff(c_4343,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4340,c_729])).

tff(c_4347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4343])).

tff(c_4348,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4312])).

tff(c_120,plain,(
    ! [A_41,B_42] : r1_xboole_0(k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)),B_42) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_257,plain,(
    ! [B_57,A_58] : r1_xboole_0(B_57,k4_xboole_0(A_58,k3_xboole_0(A_58,B_57))) ),
    inference(resolution,[status(thm)],[c_120,c_4])).

tff(c_268,plain,(
    ! [B_2,A_1] : r1_xboole_0(B_2,k4_xboole_0(A_1,k3_xboole_0(B_2,A_1))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_257])).

tff(c_4399,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_2',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4348,c_268])).

tff(c_4426,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4399])).

tff(c_109,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_1274,plain,(
    ! [A_108,C_109,B_110] :
      ( ~ r1_xboole_0(A_108,C_109)
      | ~ r1_xboole_0(A_108,B_110)
      | r1_xboole_0(A_108,k2_xboole_0(B_110,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7309,plain,(
    ! [B_219,C_220,A_221] :
      ( r1_xboole_0(k2_xboole_0(B_219,C_220),A_221)
      | ~ r1_xboole_0(A_221,C_220)
      | ~ r1_xboole_0(A_221,B_219) ) ),
    inference(resolution,[status(thm)],[c_1274,c_4])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7331,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_7309,c_44])).

tff(c_7344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4426,c_109,c_7331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.46/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.38  
% 6.46/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.46/2.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.46/2.38  
% 6.46/2.38  %Foreground sorts:
% 6.46/2.38  
% 6.46/2.38  
% 6.46/2.38  %Background operators:
% 6.46/2.38  
% 6.46/2.38  
% 6.46/2.38  %Foreground operators:
% 6.46/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.46/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.46/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.46/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.46/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.46/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.46/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.46/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.46/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.46/2.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.46/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.46/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.46/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.46/2.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.46/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.46/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.46/2.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.46/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.46/2.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.46/2.38  
% 6.78/2.41  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.78/2.41  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.78/2.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.78/2.41  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.78/2.41  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.78/2.41  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.78/2.41  tff(f_81, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.78/2.41  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.78/2.41  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.78/2.41  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.78/2.41  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.78/2.41  tff(f_83, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 6.78/2.41  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.78/2.41  tff(c_16, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.78/2.41  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.78/2.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.78/2.41  tff(c_340, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.78/2.41  tff(c_20, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.78/2.41  tff(c_104, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.78/2.41  tff(c_110, plain, (![A_18]: (r1_xboole_0(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_20, c_104])).
% 6.78/2.41  tff(c_167, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=A_48 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.78/2.41  tff(c_188, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_167])).
% 6.78/2.41  tff(c_377, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_340, c_188])).
% 6.78/2.41  tff(c_403, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_377])).
% 6.78/2.41  tff(c_372, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_340])).
% 6.78/2.41  tff(c_505, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_403, c_372])).
% 6.78/2.41  tff(c_651, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k1_tarski(B_82))=A_81 | r2_hidden(B_82, A_81))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.78/2.41  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.78/2.41  tff(c_664, plain, (![A_81, B_82]: (k4_xboole_0(A_81, A_81)=k3_xboole_0(A_81, k1_tarski(B_82)) | r2_hidden(B_82, A_81))), inference(superposition, [status(thm), theory('equality')], [c_651, c_18])).
% 6.78/2.41  tff(c_4155, plain, (![A_163, B_164]: (k3_xboole_0(A_163, k1_tarski(B_164))=k1_xboole_0 | r2_hidden(B_164, A_163))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_664])).
% 6.78/2.41  tff(c_954, plain, (![A_100, B_101, C_102]: (k3_xboole_0(k3_xboole_0(A_100, B_101), C_102)=k3_xboole_0(A_100, k3_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.78/2.41  tff(c_2845, plain, (![B_151, A_152, C_153]: (k3_xboole_0(k3_xboole_0(B_151, A_152), C_153)=k3_xboole_0(A_152, k3_xboole_0(B_151, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_954])).
% 6.78/2.41  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.78/2.41  tff(c_51, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 6.78/2.41  tff(c_222, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.78/2.41  tff(c_226, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_51, c_222])).
% 6.78/2.41  tff(c_2964, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', k1_tarski('#skF_5')))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2845, c_226])).
% 6.78/2.41  tff(c_4174, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4155, c_2964])).
% 6.78/2.41  tff(c_4312, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_4174])).
% 6.78/2.41  tff(c_4340, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_4312])).
% 6.78/2.41  tff(c_46, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.78/2.41  tff(c_700, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.78/2.41  tff(c_729, plain, (![C_88]: (~r2_hidden(C_88, '#skF_3') | ~r2_hidden(C_88, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_700])).
% 6.78/2.41  tff(c_4343, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4340, c_729])).
% 6.78/2.41  tff(c_4347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4343])).
% 6.78/2.41  tff(c_4348, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4312])).
% 6.78/2.41  tff(c_120, plain, (![A_41, B_42]: (r1_xboole_0(k4_xboole_0(A_41, k3_xboole_0(A_41, B_42)), B_42))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.78/2.41  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.78/2.41  tff(c_257, plain, (![B_57, A_58]: (r1_xboole_0(B_57, k4_xboole_0(A_58, k3_xboole_0(A_58, B_57))))), inference(resolution, [status(thm)], [c_120, c_4])).
% 6.78/2.41  tff(c_268, plain, (![B_2, A_1]: (r1_xboole_0(B_2, k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_257])).
% 6.78/2.41  tff(c_4399, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_2', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4348, c_268])).
% 6.78/2.41  tff(c_4426, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4399])).
% 6.78/2.41  tff(c_109, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_104])).
% 6.78/2.41  tff(c_1274, plain, (![A_108, C_109, B_110]: (~r1_xboole_0(A_108, C_109) | ~r1_xboole_0(A_108, B_110) | r1_xboole_0(A_108, k2_xboole_0(B_110, C_109)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.78/2.41  tff(c_7309, plain, (![B_219, C_220, A_221]: (r1_xboole_0(k2_xboole_0(B_219, C_220), A_221) | ~r1_xboole_0(A_221, C_220) | ~r1_xboole_0(A_221, B_219))), inference(resolution, [status(thm)], [c_1274, c_4])).
% 6.78/2.41  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.78/2.41  tff(c_7331, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_7309, c_44])).
% 6.78/2.41  tff(c_7344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4426, c_109, c_7331])).
% 6.78/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.78/2.41  
% 6.78/2.41  Inference rules
% 6.78/2.41  ----------------------
% 6.78/2.41  #Ref     : 0
% 6.78/2.41  #Sup     : 1798
% 6.78/2.41  #Fact    : 0
% 6.78/2.41  #Define  : 0
% 6.78/2.41  #Split   : 2
% 6.78/2.41  #Chain   : 0
% 6.78/2.41  #Close   : 0
% 6.78/2.41  
% 6.78/2.41  Ordering : KBO
% 6.78/2.41  
% 6.78/2.41  Simplification rules
% 6.78/2.41  ----------------------
% 6.78/2.41  #Subsume      : 48
% 6.78/2.41  #Demod        : 1611
% 6.78/2.41  #Tautology    : 1149
% 6.78/2.41  #SimpNegUnit  : 6
% 6.78/2.41  #BackRed      : 13
% 6.78/2.41  
% 6.78/2.41  #Partial instantiations: 0
% 6.78/2.41  #Strategies tried      : 1
% 6.78/2.41  
% 6.78/2.41  Timing (in seconds)
% 6.78/2.41  ----------------------
% 6.78/2.41  Preprocessing        : 0.33
% 6.78/2.41  Parsing              : 0.17
% 6.78/2.41  CNF conversion       : 0.02
% 6.78/2.41  Main loop            : 1.31
% 6.78/2.41  Inferencing          : 0.37
% 6.78/2.41  Reduction            : 0.61
% 6.78/2.41  Demodulation         : 0.51
% 6.78/2.41  BG Simplification    : 0.04
% 6.78/2.41  Subsumption          : 0.19
% 6.78/2.41  Abstraction          : 0.05
% 6.78/2.41  MUC search           : 0.00
% 6.78/2.41  Cooper               : 0.00
% 6.78/2.41  Total                : 1.68
% 6.78/2.42  Index Insertion      : 0.00
% 6.78/2.42  Index Deletion       : 0.00
% 6.78/2.42  Index Matching       : 0.00
% 6.78/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
