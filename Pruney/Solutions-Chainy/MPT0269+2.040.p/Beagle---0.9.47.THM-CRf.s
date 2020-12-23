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
% DateTime   : Thu Dec  3 09:52:49 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 235 expanded)
%              Number of leaves         :   40 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :   89 ( 248 expanded)
%              Number of equality atoms :   47 ( 204 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_96,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k2_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_378,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2102,plain,(
    ! [A_171,B_172] : k5_xboole_0(A_171,k5_xboole_0(B_172,k2_xboole_0(A_171,B_172))) = k3_xboole_0(A_171,B_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_378])).

tff(c_52,plain,(
    ! [A_56] : k3_tarski(k1_tarski(A_56)) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_153,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_162,plain,(
    ! [A_22] : k3_tarski(k1_tarski(A_22)) = k2_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_153])).

tff(c_165,plain,(
    ! [A_22] : k2_xboole_0(A_22,A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_162])).

tff(c_8,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_289,plain,(
    ! [A_105,B_106] : k5_xboole_0(k5_xboole_0(A_105,B_106),k2_xboole_0(A_105,B_106)) = k3_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_313,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_19,A_19)) = k3_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_289])).

tff(c_317,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_8,c_313])).

tff(c_435,plain,(
    ! [A_19,C_111] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_378])).

tff(c_448,plain,(
    ! [A_19,C_111] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_435])).

tff(c_2117,plain,(
    ! [B_172,A_171] : k5_xboole_0(B_172,k2_xboole_0(A_171,B_172)) = k5_xboole_0(A_171,k3_xboole_0(A_171,B_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2102,c_448])).

tff(c_2184,plain,(
    ! [B_173,A_174] : k5_xboole_0(B_173,k2_xboole_0(A_174,B_173)) = k4_xboole_0(A_174,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2117])).

tff(c_2299,plain,(
    ! [B_177,A_178] : k5_xboole_0(B_177,k4_xboole_0(A_178,B_177)) = k2_xboole_0(A_178,B_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_2184,c_448])).

tff(c_2359,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2299])).

tff(c_2371,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2359])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2435,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2371,c_22])).

tff(c_48,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_250,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_xboole_0(A_95,C_96)
      | ~ r1_xboole_0(B_97,C_96)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_255,plain,(
    ! [A_95,B_53,A_52] :
      ( r1_xboole_0(A_95,B_53)
      | ~ r1_tarski(A_95,k1_tarski(A_52))
      | r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_48,c_250])).

tff(c_2464,plain,(
    ! [B_179] :
      ( r1_xboole_0('#skF_1',B_179)
      | r2_hidden('#skF_2',B_179) ) ),
    inference(resolution,[status(thm)],[c_2435,c_255])).

tff(c_46,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_191,plain,(
    ! [A_85,B_86] :
      ( r2_xboole_0(A_85,B_86)
      | B_86 = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_228,plain,(
    ! [B_90,A_91] :
      ( ~ r1_tarski(B_90,A_91)
      | B_90 = A_91
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_240,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),A_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_228])).

tff(c_2432,plain,
    ( k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2371,c_240])).

tff(c_2441,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2432])).

tff(c_2442,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2441])).

tff(c_2447,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2442])).

tff(c_2468,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2464,c_2447])).

tff(c_20,plain,(
    ! [A_13] :
      ( ~ r1_xboole_0(A_13,A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2473,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2468,c_20])).

tff(c_2478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.65  
% 3.90/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.66  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.90/1.66  
% 3.90/1.66  %Foreground sorts:
% 3.90/1.66  
% 3.90/1.66  
% 3.90/1.66  %Background operators:
% 3.90/1.66  
% 3.90/1.66  
% 3.90/1.66  %Foreground operators:
% 3.90/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.90/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.90/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.90/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.90/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.90/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.90/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.90/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.90/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.90/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.90/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.66  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.90/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.90/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.90/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.66  
% 3.90/1.67  tff(f_106, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.90/1.67  tff(f_38, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.90/1.67  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.90/1.67  tff(f_69, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.90/1.67  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.90/1.67  tff(f_96, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.90/1.67  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.90/1.67  tff(f_94, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.90/1.67  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.90/1.67  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.90/1.67  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.90/1.67  tff(f_92, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.90/1.67  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.90/1.67  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.90/1.67  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.90/1.67  tff(f_43, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.90/1.67  tff(f_61, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.90/1.67  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.90/1.67  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.90/1.67  tff(c_58, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.90/1.67  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.90/1.67  tff(c_28, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k2_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.90/1.67  tff(c_378, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.90/1.67  tff(c_2102, plain, (![A_171, B_172]: (k5_xboole_0(A_171, k5_xboole_0(B_172, k2_xboole_0(A_171, B_172)))=k3_xboole_0(A_171, B_172))), inference(superposition, [status(thm), theory('equality')], [c_28, c_378])).
% 3.90/1.67  tff(c_52, plain, (![A_56]: (k3_tarski(k1_tarski(A_56))=A_56)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.90/1.67  tff(c_30, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.67  tff(c_153, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.90/1.67  tff(c_162, plain, (![A_22]: (k3_tarski(k1_tarski(A_22))=k2_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_30, c_153])).
% 3.90/1.67  tff(c_165, plain, (![A_22]: (k2_xboole_0(A_22, A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_162])).
% 3.90/1.67  tff(c_8, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.90/1.67  tff(c_26, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.90/1.67  tff(c_289, plain, (![A_105, B_106]: (k5_xboole_0(k5_xboole_0(A_105, B_106), k2_xboole_0(A_105, B_106))=k3_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.90/1.67  tff(c_313, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_19, A_19))=k3_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_26, c_289])).
% 3.90/1.67  tff(c_317, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_8, c_313])).
% 3.90/1.67  tff(c_435, plain, (![A_19, C_111]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_26, c_378])).
% 3.90/1.67  tff(c_448, plain, (![A_19, C_111]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_317, c_435])).
% 3.90/1.67  tff(c_2117, plain, (![B_172, A_171]: (k5_xboole_0(B_172, k2_xboole_0(A_171, B_172))=k5_xboole_0(A_171, k3_xboole_0(A_171, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_2102, c_448])).
% 3.90/1.67  tff(c_2184, plain, (![B_173, A_174]: (k5_xboole_0(B_173, k2_xboole_0(A_174, B_173))=k4_xboole_0(A_174, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2117])).
% 3.90/1.67  tff(c_2299, plain, (![B_177, A_178]: (k5_xboole_0(B_177, k4_xboole_0(A_178, B_177))=k2_xboole_0(A_178, B_177))), inference(superposition, [status(thm), theory('equality')], [c_2184, c_448])).
% 3.90/1.67  tff(c_2359, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2299])).
% 3.90/1.67  tff(c_2371, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2359])).
% 3.90/1.67  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.90/1.67  tff(c_2435, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2371, c_22])).
% 3.90/1.67  tff(c_48, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.90/1.67  tff(c_250, plain, (![A_95, C_96, B_97]: (r1_xboole_0(A_95, C_96) | ~r1_xboole_0(B_97, C_96) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.90/1.67  tff(c_255, plain, (![A_95, B_53, A_52]: (r1_xboole_0(A_95, B_53) | ~r1_tarski(A_95, k1_tarski(A_52)) | r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_48, c_250])).
% 3.90/1.67  tff(c_2464, plain, (![B_179]: (r1_xboole_0('#skF_1', B_179) | r2_hidden('#skF_2', B_179))), inference(resolution, [status(thm)], [c_2435, c_255])).
% 3.90/1.67  tff(c_46, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.90/1.67  tff(c_54, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.90/1.67  tff(c_191, plain, (![A_85, B_86]: (r2_xboole_0(A_85, B_86) | B_86=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.90/1.67  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.90/1.67  tff(c_228, plain, (![B_90, A_91]: (~r1_tarski(B_90, A_91) | B_90=A_91 | ~r1_tarski(A_91, B_90))), inference(resolution, [status(thm)], [c_191, c_14])).
% 3.90/1.67  tff(c_240, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(k2_xboole_0(A_14, B_15), A_14))), inference(resolution, [status(thm)], [c_22, c_228])).
% 3.90/1.67  tff(c_2432, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2371, c_240])).
% 3.90/1.67  tff(c_2441, plain, (k1_tarski('#skF_2')='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2371, c_2432])).
% 3.90/1.67  tff(c_2442, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_2441])).
% 3.90/1.67  tff(c_2447, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_2442])).
% 3.90/1.67  tff(c_2468, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2464, c_2447])).
% 3.90/1.67  tff(c_20, plain, (![A_13]: (~r1_xboole_0(A_13, A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.90/1.67  tff(c_2473, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2468, c_20])).
% 3.90/1.67  tff(c_2478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2473])).
% 3.90/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.67  
% 3.90/1.67  Inference rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Ref     : 0
% 3.90/1.67  #Sup     : 594
% 3.90/1.67  #Fact    : 0
% 3.90/1.67  #Define  : 0
% 3.90/1.67  #Split   : 0
% 3.90/1.67  #Chain   : 0
% 3.90/1.67  #Close   : 0
% 3.90/1.68  
% 3.90/1.68  Ordering : KBO
% 3.90/1.68  
% 3.90/1.68  Simplification rules
% 3.90/1.68  ----------------------
% 3.90/1.68  #Subsume      : 7
% 3.90/1.68  #Demod        : 382
% 3.90/1.68  #Tautology    : 390
% 3.90/1.68  #SimpNegUnit  : 3
% 3.90/1.68  #BackRed      : 3
% 3.90/1.68  
% 3.90/1.68  #Partial instantiations: 0
% 3.90/1.68  #Strategies tried      : 1
% 3.90/1.68  
% 3.90/1.68  Timing (in seconds)
% 3.90/1.68  ----------------------
% 3.90/1.68  Preprocessing        : 0.33
% 3.90/1.68  Parsing              : 0.18
% 3.90/1.68  CNF conversion       : 0.02
% 3.90/1.68  Main loop            : 0.58
% 3.90/1.68  Inferencing          : 0.21
% 3.90/1.68  Reduction            : 0.22
% 3.90/1.68  Demodulation         : 0.17
% 3.90/1.68  BG Simplification    : 0.03
% 3.90/1.68  Subsumption          : 0.08
% 3.90/1.68  Abstraction          : 0.03
% 3.90/1.68  MUC search           : 0.00
% 3.90/1.68  Cooper               : 0.00
% 3.90/1.68  Total                : 0.95
% 3.90/1.68  Index Insertion      : 0.00
% 3.90/1.68  Index Deletion       : 0.00
% 3.90/1.68  Index Matching       : 0.00
% 3.90/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
