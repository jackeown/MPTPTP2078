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
% DateTime   : Thu Dec  3 09:50:15 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 150 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 272 expanded)
%              Number of equality atoms :   65 ( 236 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_56,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_80,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_60,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_97,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_91,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_111,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_28])).

tff(c_341,plain,(
    ! [B_103,A_104] :
      ( k1_tarski(B_103) = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,k1_tarski(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_348,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_111,c_341])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_91,c_348])).

tff(c_361,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_362,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_24,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_365,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_362,c_24])).

tff(c_576,plain,(
    ! [A_136,B_137,C_138] :
      ( ~ r1_xboole_0(A_136,B_137)
      | ~ r2_hidden(C_138,B_137)
      | ~ r2_hidden(C_138,A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_580,plain,(
    ! [C_139] : ~ r2_hidden(C_139,'#skF_4') ),
    inference(resolution,[status(thm)],[c_365,c_576])).

tff(c_608,plain,(
    ! [B_141] : r1_tarski('#skF_4',B_141) ),
    inference(resolution,[status(thm)],[c_8,c_580])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_612,plain,(
    ! [B_141] : k2_xboole_0('#skF_4',B_141) = B_141 ),
    inference(resolution,[status(thm)],[c_608,c_20])).

tff(c_643,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_64])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_643])).

tff(c_646,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_647,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_682,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_647,c_62])).

tff(c_32,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1073,plain,(
    ! [A_192,B_193] : k5_xboole_0(k5_xboole_0(A_192,B_193),k2_xboole_0(A_192,B_193)) = k3_xboole_0(A_192,B_193) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1118,plain,(
    ! [A_8] : k5_xboole_0(k5_xboole_0(A_8,A_8),A_8) = k3_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1073])).

tff(c_1125,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12,c_1118])).

tff(c_1262,plain,(
    ! [A_197,B_198,C_199] : k5_xboole_0(k5_xboole_0(A_197,B_198),C_199) = k5_xboole_0(A_197,k5_xboole_0(B_198,C_199)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1337,plain,(
    ! [A_27,C_199] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_199)) = k5_xboole_0(k1_xboole_0,C_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1262])).

tff(c_1352,plain,(
    ! [A_27,C_199] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_199)) = C_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1125,c_1337])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_655,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_64])).

tff(c_1115,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_1073])).

tff(c_1181,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1115])).

tff(c_1510,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1181])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_878,plain,(
    ! [B_174,A_175] :
      ( k1_tarski(B_174) = A_175
      | k1_xboole_0 = A_175
      | ~ r1_tarski(A_175,k1_tarski(B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_889,plain,(
    ! [A_175] :
      ( k1_tarski('#skF_3') = A_175
      | k1_xboole_0 = A_175
      | ~ r1_tarski(A_175,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_878])).

tff(c_899,plain,(
    ! [A_176] :
      ( A_176 = '#skF_4'
      | k1_xboole_0 = A_176
      | ~ r1_tarski(A_176,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_889])).

tff(c_915,plain,(
    ! [B_20] :
      ( k3_xboole_0('#skF_4',B_20) = '#skF_4'
      | k3_xboole_0('#skF_4',B_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_899])).

tff(c_1515,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_915])).

tff(c_1527,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1515])).

tff(c_1529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_682,c_1527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.43  
% 3.13/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.13/1.43  
% 3.13/1.43  %Foreground sorts:
% 3.13/1.43  
% 3.13/1.43  
% 3.13/1.43  %Background operators:
% 3.13/1.43  
% 3.13/1.43  
% 3.13/1.43  %Foreground operators:
% 3.13/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.13/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.13/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.13/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.13/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.43  
% 3.13/1.45  tff(f_123, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.13/1.45  tff(f_76, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.13/1.45  tff(f_102, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.13/1.45  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.13/1.45  tff(f_74, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.13/1.45  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.13/1.45  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.13/1.45  tff(f_80, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.13/1.45  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.13/1.45  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.13/1.45  tff(f_82, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.13/1.45  tff(f_78, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.13/1.45  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.13/1.45  tff(f_62, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.13/1.45  tff(c_60, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.13/1.45  tff(c_97, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 3.13/1.45  tff(c_58, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.13/1.45  tff(c_91, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 3.13/1.45  tff(c_64, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.13/1.45  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.13/1.45  tff(c_111, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_28])).
% 3.13/1.45  tff(c_341, plain, (![B_103, A_104]: (k1_tarski(B_103)=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, k1_tarski(B_103)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.13/1.45  tff(c_348, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_111, c_341])).
% 3.13/1.45  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_91, c_348])).
% 3.13/1.45  tff(c_361, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 3.13/1.45  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.13/1.45  tff(c_362, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 3.13/1.45  tff(c_24, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.13/1.45  tff(c_365, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_362, c_24])).
% 3.13/1.45  tff(c_576, plain, (![A_136, B_137, C_138]: (~r1_xboole_0(A_136, B_137) | ~r2_hidden(C_138, B_137) | ~r2_hidden(C_138, A_136))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.45  tff(c_580, plain, (![C_139]: (~r2_hidden(C_139, '#skF_4'))), inference(resolution, [status(thm)], [c_365, c_576])).
% 3.13/1.45  tff(c_608, plain, (![B_141]: (r1_tarski('#skF_4', B_141))), inference(resolution, [status(thm)], [c_8, c_580])).
% 3.13/1.45  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.45  tff(c_612, plain, (![B_141]: (k2_xboole_0('#skF_4', B_141)=B_141)), inference(resolution, [status(thm)], [c_608, c_20])).
% 3.13/1.45  tff(c_643, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_612, c_64])).
% 3.13/1.45  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_643])).
% 3.13/1.45  tff(c_646, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 3.13/1.45  tff(c_647, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 3.13/1.45  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.13/1.45  tff(c_682, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_647, c_62])).
% 3.13/1.45  tff(c_32, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.13/1.45  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.45  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.13/1.45  tff(c_1073, plain, (![A_192, B_193]: (k5_xboole_0(k5_xboole_0(A_192, B_193), k2_xboole_0(A_192, B_193))=k3_xboole_0(A_192, B_193))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.45  tff(c_1118, plain, (![A_8]: (k5_xboole_0(k5_xboole_0(A_8, A_8), A_8)=k3_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1073])).
% 3.13/1.45  tff(c_1125, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12, c_1118])).
% 3.13/1.45  tff(c_1262, plain, (![A_197, B_198, C_199]: (k5_xboole_0(k5_xboole_0(A_197, B_198), C_199)=k5_xboole_0(A_197, k5_xboole_0(B_198, C_199)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.13/1.45  tff(c_1337, plain, (![A_27, C_199]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_199))=k5_xboole_0(k1_xboole_0, C_199))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1262])).
% 3.13/1.45  tff(c_1352, plain, (![A_27, C_199]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_199))=C_199)), inference(demodulation, [status(thm), theory('equality')], [c_1125, c_1337])).
% 3.13/1.45  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.45  tff(c_655, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_64])).
% 3.13/1.45  tff(c_1115, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_655, c_1073])).
% 3.13/1.45  tff(c_1181, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2, c_1115])).
% 3.13/1.45  tff(c_1510, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1181])).
% 3.13/1.45  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.45  tff(c_878, plain, (![B_174, A_175]: (k1_tarski(B_174)=A_175 | k1_xboole_0=A_175 | ~r1_tarski(A_175, k1_tarski(B_174)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.13/1.45  tff(c_889, plain, (![A_175]: (k1_tarski('#skF_3')=A_175 | k1_xboole_0=A_175 | ~r1_tarski(A_175, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_647, c_878])).
% 3.13/1.45  tff(c_899, plain, (![A_176]: (A_176='#skF_4' | k1_xboole_0=A_176 | ~r1_tarski(A_176, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_889])).
% 3.13/1.45  tff(c_915, plain, (![B_20]: (k3_xboole_0('#skF_4', B_20)='#skF_4' | k3_xboole_0('#skF_4', B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_899])).
% 3.13/1.45  tff(c_1515, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1510, c_915])).
% 3.13/1.45  tff(c_1527, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1515])).
% 3.13/1.45  tff(c_1529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_682, c_1527])).
% 3.13/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.45  
% 3.13/1.45  Inference rules
% 3.13/1.45  ----------------------
% 3.13/1.45  #Ref     : 0
% 3.13/1.45  #Sup     : 340
% 3.13/1.45  #Fact    : 1
% 3.13/1.45  #Define  : 0
% 3.13/1.45  #Split   : 3
% 3.13/1.45  #Chain   : 0
% 3.13/1.45  #Close   : 0
% 3.13/1.45  
% 3.13/1.45  Ordering : KBO
% 3.13/1.45  
% 3.13/1.45  Simplification rules
% 3.13/1.45  ----------------------
% 3.13/1.45  #Subsume      : 9
% 3.13/1.45  #Demod        : 156
% 3.13/1.45  #Tautology    : 243
% 3.13/1.45  #SimpNegUnit  : 8
% 3.13/1.45  #BackRed      : 5
% 3.13/1.45  
% 3.13/1.45  #Partial instantiations: 0
% 3.13/1.45  #Strategies tried      : 1
% 3.13/1.45  
% 3.13/1.45  Timing (in seconds)
% 3.13/1.45  ----------------------
% 3.13/1.45  Preprocessing        : 0.36
% 3.13/1.45  Parsing              : 0.20
% 3.13/1.45  CNF conversion       : 0.02
% 3.13/1.45  Main loop            : 0.39
% 3.13/1.45  Inferencing          : 0.15
% 3.13/1.45  Reduction            : 0.14
% 3.13/1.45  Demodulation         : 0.11
% 3.13/1.45  BG Simplification    : 0.02
% 3.13/1.45  Subsumption          : 0.05
% 3.13/1.45  Abstraction          : 0.02
% 3.13/1.45  MUC search           : 0.00
% 3.13/1.45  Cooper               : 0.00
% 3.13/1.45  Total                : 0.78
% 3.13/1.45  Index Insertion      : 0.00
% 3.13/1.45  Index Deletion       : 0.00
% 3.13/1.45  Index Matching       : 0.00
% 3.13/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
