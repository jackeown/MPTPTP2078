%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:25 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 116 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_95,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,(
    ! [B_71,A_70] : r2_hidden(B_71,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_16])).

tff(c_116,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,k3_tarski(B_50))
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_204,plain,(
    ! [A_95,A_96,B_97] :
      ( r1_tarski(A_95,k2_xboole_0(A_96,B_97))
      | ~ r2_hidden(A_95,k2_tarski(A_96,B_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_50])).

tff(c_211,plain,(
    ! [B_71,A_70] : r1_tarski(B_71,k2_xboole_0(A_70,B_71)) ),
    inference(resolution,[status(thm)],[c_104,c_204])).

tff(c_54,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_zfmisc_1(A_53),k1_zfmisc_1(B_54))
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_152,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(k3_xboole_0(A_82,C_83),B_84)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [B_2,A_1,B_84] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_84)
      | ~ r1_tarski(A_1,B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_224,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(k5_xboole_0(A_104,C_105),B_106)
      | ~ r1_tarski(C_105,B_106)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_298,plain,(
    ! [A_128,B_129,B_130] :
      ( r1_tarski(k4_xboole_0(A_128,B_129),B_130)
      | ~ r1_tarski(k3_xboole_0(A_128,B_129),B_130)
      | ~ r1_tarski(A_128,B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_224])).

tff(c_12,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_233,plain,(
    ! [A_13,B_14,B_106] :
      ( r1_tarski(k2_xboole_0(A_13,B_14),B_106)
      | ~ r1_tarski(k4_xboole_0(B_14,A_13),B_106)
      | ~ r1_tarski(A_13,B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_224])).

tff(c_314,plain,(
    ! [B_140,A_141,B_142] :
      ( r1_tarski(k2_xboole_0(B_140,A_141),B_142)
      | ~ r1_tarski(B_140,B_142)
      | ~ r1_tarski(k3_xboole_0(A_141,B_140),B_142)
      | ~ r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_298,c_233])).

tff(c_353,plain,(
    ! [A_150,B_151,B_152] :
      ( r1_tarski(k2_xboole_0(A_150,B_151),B_152)
      | ~ r1_tarski(B_151,B_152)
      | ~ r1_tarski(A_150,B_152) ) ),
    inference(resolution,[status(thm)],[c_155,c_314])).

tff(c_56,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'),k1_zfmisc_1('#skF_4')),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_357,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_353,c_56])).

tff(c_358,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_361,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_358])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_361])).

tff(c_366,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_370,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_366])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:43:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.18/1.29  
% 2.18/1.29  %Foreground sorts:
% 2.18/1.29  
% 2.18/1.29  
% 2.18/1.29  %Background operators:
% 2.18/1.29  
% 2.18/1.29  
% 2.18/1.29  %Foreground operators:
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.18/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.18/1.29  
% 2.18/1.30  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.18/1.30  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.18/1.30  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.18/1.30  tff(f_74, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.18/1.30  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.18/1.30  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.18/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.18/1.30  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.18/1.30  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.18/1.30  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.18/1.30  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.18/1.30  tff(f_83, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 2.18/1.30  tff(c_95, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.30  tff(c_16, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.30  tff(c_104, plain, (![B_71, A_70]: (r2_hidden(B_71, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_16])).
% 2.18/1.30  tff(c_116, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.18/1.30  tff(c_50, plain, (![A_49, B_50]: (r1_tarski(A_49, k3_tarski(B_50)) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.30  tff(c_204, plain, (![A_95, A_96, B_97]: (r1_tarski(A_95, k2_xboole_0(A_96, B_97)) | ~r2_hidden(A_95, k2_tarski(A_96, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_50])).
% 2.18/1.30  tff(c_211, plain, (![B_71, A_70]: (r1_tarski(B_71, k2_xboole_0(A_70, B_71)))), inference(resolution, [status(thm)], [c_104, c_204])).
% 2.18/1.30  tff(c_54, plain, (![A_53, B_54]: (r1_tarski(k1_zfmisc_1(A_53), k1_zfmisc_1(B_54)) | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.30  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.30  tff(c_152, plain, (![A_82, C_83, B_84]: (r1_tarski(k3_xboole_0(A_82, C_83), B_84) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.30  tff(c_155, plain, (![B_2, A_1, B_84]: (r1_tarski(k3_xboole_0(B_2, A_1), B_84) | ~r1_tarski(A_1, B_84))), inference(superposition, [status(thm), theory('equality')], [c_2, c_152])).
% 2.18/1.30  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.30  tff(c_224, plain, (![A_104, C_105, B_106]: (r1_tarski(k5_xboole_0(A_104, C_105), B_106) | ~r1_tarski(C_105, B_106) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.30  tff(c_298, plain, (![A_128, B_129, B_130]: (r1_tarski(k4_xboole_0(A_128, B_129), B_130) | ~r1_tarski(k3_xboole_0(A_128, B_129), B_130) | ~r1_tarski(A_128, B_130))), inference(superposition, [status(thm), theory('equality')], [c_4, c_224])).
% 2.18/1.30  tff(c_12, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.30  tff(c_233, plain, (![A_13, B_14, B_106]: (r1_tarski(k2_xboole_0(A_13, B_14), B_106) | ~r1_tarski(k4_xboole_0(B_14, A_13), B_106) | ~r1_tarski(A_13, B_106))), inference(superposition, [status(thm), theory('equality')], [c_12, c_224])).
% 2.18/1.30  tff(c_314, plain, (![B_140, A_141, B_142]: (r1_tarski(k2_xboole_0(B_140, A_141), B_142) | ~r1_tarski(B_140, B_142) | ~r1_tarski(k3_xboole_0(A_141, B_140), B_142) | ~r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_298, c_233])).
% 2.18/1.30  tff(c_353, plain, (![A_150, B_151, B_152]: (r1_tarski(k2_xboole_0(A_150, B_151), B_152) | ~r1_tarski(B_151, B_152) | ~r1_tarski(A_150, B_152))), inference(resolution, [status(thm)], [c_155, c_314])).
% 2.18/1.30  tff(c_56, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'), k1_zfmisc_1('#skF_4')), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.30  tff(c_357, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4'))) | ~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_353, c_56])).
% 2.18/1.30  tff(c_358, plain, (~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_357])).
% 2.18/1.30  tff(c_361, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_358])).
% 2.18/1.30  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_361])).
% 2.18/1.30  tff(c_366, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_357])).
% 2.18/1.30  tff(c_370, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_366])).
% 2.18/1.30  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_370])).
% 2.18/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  Inference rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Ref     : 0
% 2.18/1.30  #Sup     : 69
% 2.18/1.30  #Fact    : 0
% 2.18/1.30  #Define  : 0
% 2.18/1.30  #Split   : 1
% 2.18/1.30  #Chain   : 0
% 2.18/1.30  #Close   : 0
% 2.18/1.30  
% 2.18/1.30  Ordering : KBO
% 2.18/1.30  
% 2.18/1.30  Simplification rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Subsume      : 5
% 2.18/1.30  #Demod        : 8
% 2.18/1.30  #Tautology    : 40
% 2.18/1.30  #SimpNegUnit  : 0
% 2.18/1.30  #BackRed      : 0
% 2.18/1.30  
% 2.18/1.30  #Partial instantiations: 0
% 2.18/1.30  #Strategies tried      : 1
% 2.18/1.30  
% 2.18/1.30  Timing (in seconds)
% 2.18/1.30  ----------------------
% 2.49/1.31  Preprocessing        : 0.32
% 2.49/1.31  Parsing              : 0.17
% 2.49/1.31  CNF conversion       : 0.02
% 2.49/1.31  Main loop            : 0.22
% 2.49/1.31  Inferencing          : 0.08
% 2.49/1.31  Reduction            : 0.07
% 2.49/1.31  Demodulation         : 0.05
% 2.49/1.31  BG Simplification    : 0.02
% 2.49/1.31  Subsumption          : 0.04
% 2.49/1.31  Abstraction          : 0.01
% 2.49/1.31  MUC search           : 0.00
% 2.49/1.31  Cooper               : 0.00
% 2.49/1.31  Total                : 0.57
% 2.49/1.31  Index Insertion      : 0.00
% 2.49/1.31  Index Deletion       : 0.00
% 2.49/1.31  Index Matching       : 0.00
% 2.49/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
