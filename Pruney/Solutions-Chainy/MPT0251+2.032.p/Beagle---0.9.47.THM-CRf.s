%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:50 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 104 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 154 expanded)
%              Number of equality atoms :   43 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1037,plain,(
    ! [A_144,B_145,C_146] :
      ( ~ r2_hidden('#skF_2'(A_144,B_145,C_146),B_145)
      | r2_hidden('#skF_3'(A_144,B_145,C_146),C_146)
      | k4_xboole_0(A_144,B_145) = C_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1046,plain,(
    ! [A_147,C_148] :
      ( r2_hidden('#skF_3'(A_147,A_147,C_148),C_148)
      | k4_xboole_0(A_147,A_147) = C_148 ) ),
    inference(resolution,[status(thm)],[c_24,c_1037])).

tff(c_54,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_432,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_531,plain,(
    ! [A_82] :
      ( k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_432])).

tff(c_544,plain,(
    ! [A_34] :
      ( k1_tarski(A_34) = k1_xboole_0
      | ~ r2_hidden(A_34,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_54,c_531])).

tff(c_1077,plain,(
    ! [A_149] :
      ( k1_tarski('#skF_3'(A_149,A_149,k1_xboole_0)) = k1_xboole_0
      | k4_xboole_0(A_149,A_149) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1046,c_544])).

tff(c_52,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | ~ r1_tarski(k1_tarski(A_34),B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1106,plain,(
    ! [A_149,B_35] :
      ( r2_hidden('#skF_3'(A_149,A_149,k1_xboole_0),B_35)
      | ~ r1_tarski(k1_xboole_0,B_35)
      | k4_xboole_0(A_149,A_149) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_52])).

tff(c_1118,plain,(
    ! [A_149,B_35] :
      ( r2_hidden('#skF_3'(A_149,A_149,k1_xboole_0),B_35)
      | k4_xboole_0(A_149,A_149) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1106])).

tff(c_1121,plain,(
    ! [A_150,B_151] :
      ( r2_hidden('#skF_3'(A_150,A_150,k1_xboole_0),B_151)
      | k4_xboole_0(A_150,A_150) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1106])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1161,plain,(
    ! [A_155,B_156] :
      ( ~ r2_hidden('#skF_3'(A_155,A_155,k1_xboole_0),B_156)
      | k4_xboole_0(A_155,A_155) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1121,c_10])).

tff(c_1182,plain,(
    ! [A_149] : k4_xboole_0(A_149,A_149) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1118,c_1161])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_124,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_132,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_325,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_334,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_325])).

tff(c_194,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tarski(A_53),B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_663,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(k1_tarski(A_103),B_104) = k1_tarski(A_103)
      | ~ r2_hidden(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_194,c_36])).

tff(c_32,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_669,plain,(
    ! [A_103,B_104] :
      ( k5_xboole_0(k1_tarski(A_103),k1_tarski(A_103)) = k4_xboole_0(k1_tarski(A_103),B_104)
      | ~ r2_hidden(A_103,B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_32])).

tff(c_682,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(k1_tarski(A_103),k1_tarski(A_103)) = k4_xboole_0(k1_tarski(A_103),B_104)
      | ~ r2_hidden(A_103,B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_669])).

tff(c_2112,plain,(
    ! [A_210,B_211] :
      ( k4_xboole_0(k1_tarski(A_210),B_211) = k1_xboole_0
      | ~ r2_hidden(A_210,B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_682])).

tff(c_40,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2163,plain,(
    ! [B_211,A_210] :
      ( k2_xboole_0(B_211,k1_tarski(A_210)) = k2_xboole_0(B_211,k1_xboole_0)
      | ~ r2_hidden(A_210,B_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2112,c_40])).

tff(c_2255,plain,(
    ! [B_214,A_215] :
      ( k2_xboole_0(B_214,k1_tarski(A_215)) = B_214
      | ~ r2_hidden(A_215,B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2163])).

tff(c_42,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_133,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_211,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_133])).

tff(c_56,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_217,plain,(
    ! [B_61,A_60] : k2_xboole_0(B_61,A_60) = k2_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_56])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_237,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_58])).

tff(c_2269,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2255,c_237])).

tff(c_2302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.59  
% 3.62/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.59  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.62/1.59  
% 3.62/1.59  %Foreground sorts:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Background operators:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Foreground operators:
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.62/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.62/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.62/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.62/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.62/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.62/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.62/1.59  
% 3.62/1.60  tff(f_81, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.62/1.60  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.62/1.60  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.62/1.60  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.62/1.60  tff(f_74, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.62/1.60  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.62/1.60  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.62/1.60  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.62/1.60  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.62/1.60  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.62/1.60  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.62/1.60  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.62/1.60  tff(c_34, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.60  tff(c_38, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.62/1.60  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.62/1.60  tff(c_1037, plain, (![A_144, B_145, C_146]: (~r2_hidden('#skF_2'(A_144, B_145, C_146), B_145) | r2_hidden('#skF_3'(A_144, B_145, C_146), C_146) | k4_xboole_0(A_144, B_145)=C_146)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.62/1.60  tff(c_1046, plain, (![A_147, C_148]: (r2_hidden('#skF_3'(A_147, A_147, C_148), C_148) | k4_xboole_0(A_147, A_147)=C_148)), inference(resolution, [status(thm)], [c_24, c_1037])).
% 3.62/1.60  tff(c_54, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.62/1.60  tff(c_432, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.60  tff(c_531, plain, (![A_82]: (k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_432])).
% 3.62/1.60  tff(c_544, plain, (![A_34]: (k1_tarski(A_34)=k1_xboole_0 | ~r2_hidden(A_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_54, c_531])).
% 3.62/1.60  tff(c_1077, plain, (![A_149]: (k1_tarski('#skF_3'(A_149, A_149, k1_xboole_0))=k1_xboole_0 | k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1046, c_544])).
% 3.62/1.60  tff(c_52, plain, (![A_34, B_35]: (r2_hidden(A_34, B_35) | ~r1_tarski(k1_tarski(A_34), B_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.62/1.60  tff(c_1106, plain, (![A_149, B_35]: (r2_hidden('#skF_3'(A_149, A_149, k1_xboole_0), B_35) | ~r1_tarski(k1_xboole_0, B_35) | k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1077, c_52])).
% 3.62/1.60  tff(c_1118, plain, (![A_149, B_35]: (r2_hidden('#skF_3'(A_149, A_149, k1_xboole_0), B_35) | k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1106])).
% 3.62/1.60  tff(c_1121, plain, (![A_150, B_151]: (r2_hidden('#skF_3'(A_150, A_150, k1_xboole_0), B_151) | k4_xboole_0(A_150, A_150)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1106])).
% 3.62/1.60  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.62/1.60  tff(c_1161, plain, (![A_155, B_156]: (~r2_hidden('#skF_3'(A_155, A_155, k1_xboole_0), B_156) | k4_xboole_0(A_155, A_155)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1121, c_10])).
% 3.62/1.60  tff(c_1182, plain, (![A_149]: (k4_xboole_0(A_149, A_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1118, c_1161])).
% 3.62/1.60  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.60  tff(c_124, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.62/1.60  tff(c_132, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_124])).
% 3.62/1.60  tff(c_325, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.62/1.60  tff(c_334, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_132, c_325])).
% 3.62/1.60  tff(c_194, plain, (![A_53, B_54]: (r1_tarski(k1_tarski(A_53), B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.62/1.60  tff(c_36, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.62/1.60  tff(c_663, plain, (![A_103, B_104]: (k3_xboole_0(k1_tarski(A_103), B_104)=k1_tarski(A_103) | ~r2_hidden(A_103, B_104))), inference(resolution, [status(thm)], [c_194, c_36])).
% 3.62/1.60  tff(c_32, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.62/1.60  tff(c_669, plain, (![A_103, B_104]: (k5_xboole_0(k1_tarski(A_103), k1_tarski(A_103))=k4_xboole_0(k1_tarski(A_103), B_104) | ~r2_hidden(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_663, c_32])).
% 3.62/1.60  tff(c_682, plain, (![A_103, B_104]: (k4_xboole_0(k1_tarski(A_103), k1_tarski(A_103))=k4_xboole_0(k1_tarski(A_103), B_104) | ~r2_hidden(A_103, B_104))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_669])).
% 3.62/1.60  tff(c_2112, plain, (![A_210, B_211]: (k4_xboole_0(k1_tarski(A_210), B_211)=k1_xboole_0 | ~r2_hidden(A_210, B_211))), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_682])).
% 3.62/1.60  tff(c_40, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.62/1.60  tff(c_2163, plain, (![B_211, A_210]: (k2_xboole_0(B_211, k1_tarski(A_210))=k2_xboole_0(B_211, k1_xboole_0) | ~r2_hidden(A_210, B_211))), inference(superposition, [status(thm), theory('equality')], [c_2112, c_40])).
% 3.62/1.60  tff(c_2255, plain, (![B_214, A_215]: (k2_xboole_0(B_214, k1_tarski(A_215))=B_214 | ~r2_hidden(A_215, B_214))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2163])).
% 3.62/1.60  tff(c_42, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.60  tff(c_133, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.60  tff(c_211, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(B_61, A_60))), inference(superposition, [status(thm), theory('equality')], [c_42, c_133])).
% 3.62/1.60  tff(c_56, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.60  tff(c_217, plain, (![B_61, A_60]: (k2_xboole_0(B_61, A_60)=k2_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_211, c_56])).
% 3.62/1.60  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.62/1.60  tff(c_237, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_58])).
% 3.62/1.60  tff(c_2269, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2255, c_237])).
% 3.62/1.60  tff(c_2302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2269])).
% 3.62/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.60  
% 3.62/1.60  Inference rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Ref     : 0
% 3.62/1.60  #Sup     : 513
% 3.62/1.60  #Fact    : 0
% 3.62/1.60  #Define  : 0
% 3.62/1.60  #Split   : 3
% 3.62/1.60  #Chain   : 0
% 3.62/1.60  #Close   : 0
% 3.62/1.60  
% 3.62/1.60  Ordering : KBO
% 3.62/1.60  
% 3.62/1.60  Simplification rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Subsume      : 141
% 3.62/1.60  #Demod        : 198
% 3.62/1.60  #Tautology    : 228
% 3.62/1.60  #SimpNegUnit  : 3
% 3.62/1.60  #BackRed      : 5
% 3.62/1.60  
% 3.62/1.60  #Partial instantiations: 0
% 3.62/1.60  #Strategies tried      : 1
% 3.62/1.60  
% 3.62/1.60  Timing (in seconds)
% 3.62/1.60  ----------------------
% 3.62/1.61  Preprocessing        : 0.32
% 3.62/1.61  Parsing              : 0.17
% 3.62/1.61  CNF conversion       : 0.02
% 3.62/1.61  Main loop            : 0.55
% 3.62/1.61  Inferencing          : 0.19
% 3.62/1.61  Reduction            : 0.17
% 3.62/1.61  Demodulation         : 0.13
% 3.62/1.61  BG Simplification    : 0.03
% 3.62/1.61  Subsumption          : 0.12
% 3.62/1.61  Abstraction          : 0.03
% 3.62/1.61  MUC search           : 0.00
% 3.62/1.61  Cooper               : 0.00
% 3.62/1.61  Total                : 0.89
% 3.62/1.61  Index Insertion      : 0.00
% 3.62/1.61  Index Deletion       : 0.00
% 3.62/1.61  Index Matching       : 0.00
% 3.62/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
