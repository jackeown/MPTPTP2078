%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:49 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 125 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :   76 ( 132 expanded)
%              Number of equality atoms :   43 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_124,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_227,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(B_67,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_124])).

tff(c_44,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_254,plain,(
    ! [B_68,A_69] : k2_xboole_0(B_68,A_69) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_44])).

tff(c_270,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_22])).

tff(c_310,plain,(
    ! [A_72] : k2_xboole_0(k1_xboole_0,A_72) = A_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_22])).

tff(c_26,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_317,plain,(
    ! [B_18] : k4_xboole_0(B_18,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_26])).

tff(c_348,plain,(
    ! [B_18] : k4_xboole_0(B_18,k1_xboole_0) = B_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_317])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_191,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_2'(A_59,B_60),A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_196,plain,(
    ! [A_61,B_62] :
      ( ~ v1_xboole_0(A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_191,c_2])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_206,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_196,c_24])).

tff(c_209,plain,(
    ! [B_64] : k3_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_206])).

tff(c_581,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_618,plain,(
    ! [B_88] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_581])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_172,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(resolution,[status(thm)],[c_18,c_164])).

tff(c_593,plain,(
    ! [B_11] : k5_xboole_0(B_11,B_11) = k4_xboole_0(B_11,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_581])).

tff(c_624,plain,(
    ! [B_88] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_593])).

tff(c_643,plain,(
    ! [B_88] : k4_xboole_0(k1_xboole_0,B_88) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_624])).

tff(c_375,plain,(
    ! [A_74,B_75] : k4_xboole_0(k2_xboole_0(A_74,B_75),B_75) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_395,plain,(
    ! [A_69] : k4_xboole_0(k1_xboole_0,A_69) = k4_xboole_0(A_69,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_375])).

tff(c_650,plain,(
    ! [A_69] : k4_xboole_0(A_69,A_69) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_395])).

tff(c_704,plain,(
    ! [B_11] : k5_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_593])).

tff(c_42,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tarski(A_33),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1764,plain,(
    ! [A_139,B_140] :
      ( k3_xboole_0(k1_tarski(A_139),B_140) = k1_tarski(A_139)
      | ~ r2_hidden(A_139,B_140) ) ),
    inference(resolution,[status(thm)],[c_42,c_164])).

tff(c_20,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1770,plain,(
    ! [A_139,B_140] :
      ( k5_xboole_0(k1_tarski(A_139),k1_tarski(A_139)) = k4_xboole_0(k1_tarski(A_139),B_140)
      | ~ r2_hidden(A_139,B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_20])).

tff(c_1791,plain,(
    ! [A_141,B_142] :
      ( k4_xboole_0(k1_tarski(A_141),B_142) = k1_xboole_0
      | ~ r2_hidden(A_141,B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_1770])).

tff(c_1819,plain,(
    ! [B_142,A_141] :
      ( k2_xboole_0(B_142,k1_tarski(A_141)) = k2_xboole_0(B_142,k1_xboole_0)
      | ~ r2_hidden(A_141,B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1791,c_26])).

tff(c_1881,plain,(
    ! [B_144,A_145] :
      ( k2_xboole_0(B_144,k1_tarski(A_145)) = B_144
      | ~ r2_hidden(A_145,B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1819])).

tff(c_233,plain,(
    ! [B_67,A_66] : k2_xboole_0(B_67,A_66) = k2_xboole_0(A_66,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_44])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_253,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_46])).

tff(c_1939,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_253])).

tff(c_2000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.57  
% 3.34/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.58  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.34/1.58  
% 3.34/1.58  %Foreground sorts:
% 3.34/1.58  
% 3.34/1.58  
% 3.34/1.58  %Background operators:
% 3.34/1.58  
% 3.34/1.58  
% 3.34/1.58  %Foreground operators:
% 3.34/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.34/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.34/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.58  
% 3.34/1.59  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.34/1.59  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.34/1.59  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.34/1.59  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.34/1.59  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.34/1.59  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.34/1.59  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.34/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.34/1.59  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.34/1.59  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.59  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.34/1.59  tff(f_57, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.34/1.59  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.34/1.59  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.59  tff(c_22, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.34/1.59  tff(c_30, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.59  tff(c_124, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.34/1.59  tff(c_227, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(B_67, A_66))), inference(superposition, [status(thm), theory('equality')], [c_30, c_124])).
% 3.34/1.59  tff(c_44, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.34/1.59  tff(c_254, plain, (![B_68, A_69]: (k2_xboole_0(B_68, A_69)=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_227, c_44])).
% 3.34/1.59  tff(c_270, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_254, c_22])).
% 3.34/1.59  tff(c_310, plain, (![A_72]: (k2_xboole_0(k1_xboole_0, A_72)=A_72)), inference(superposition, [status(thm), theory('equality')], [c_254, c_22])).
% 3.34/1.59  tff(c_26, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.34/1.59  tff(c_317, plain, (![B_18]: (k4_xboole_0(B_18, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_18))), inference(superposition, [status(thm), theory('equality')], [c_310, c_26])).
% 3.34/1.59  tff(c_348, plain, (![B_18]: (k4_xboole_0(B_18, k1_xboole_0)=B_18)), inference(demodulation, [status(thm), theory('equality')], [c_270, c_317])).
% 3.34/1.59  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.59  tff(c_191, plain, (![A_59, B_60]: (r2_hidden('#skF_2'(A_59, B_60), A_59) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.59  tff(c_196, plain, (![A_61, B_62]: (~v1_xboole_0(A_61) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_191, c_2])).
% 3.34/1.59  tff(c_24, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.34/1.59  tff(c_206, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_196, c_24])).
% 3.34/1.59  tff(c_209, plain, (![B_64]: (k3_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_206])).
% 3.34/1.59  tff(c_581, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.59  tff(c_618, plain, (![B_88]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_88))), inference(superposition, [status(thm), theory('equality')], [c_209, c_581])).
% 3.34/1.59  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.59  tff(c_164, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.34/1.59  tff(c_172, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(resolution, [status(thm)], [c_18, c_164])).
% 3.34/1.59  tff(c_593, plain, (![B_11]: (k5_xboole_0(B_11, B_11)=k4_xboole_0(B_11, B_11))), inference(superposition, [status(thm), theory('equality')], [c_172, c_581])).
% 3.34/1.59  tff(c_624, plain, (![B_88]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_88))), inference(superposition, [status(thm), theory('equality')], [c_618, c_593])).
% 3.34/1.59  tff(c_643, plain, (![B_88]: (k4_xboole_0(k1_xboole_0, B_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_348, c_624])).
% 3.34/1.59  tff(c_375, plain, (![A_74, B_75]: (k4_xboole_0(k2_xboole_0(A_74, B_75), B_75)=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.34/1.59  tff(c_395, plain, (![A_69]: (k4_xboole_0(k1_xboole_0, A_69)=k4_xboole_0(A_69, A_69))), inference(superposition, [status(thm), theory('equality')], [c_270, c_375])).
% 3.34/1.59  tff(c_650, plain, (![A_69]: (k4_xboole_0(A_69, A_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_643, c_395])).
% 3.34/1.59  tff(c_704, plain, (![B_11]: (k5_xboole_0(B_11, B_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_650, c_593])).
% 3.34/1.59  tff(c_42, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.59  tff(c_1764, plain, (![A_139, B_140]: (k3_xboole_0(k1_tarski(A_139), B_140)=k1_tarski(A_139) | ~r2_hidden(A_139, B_140))), inference(resolution, [status(thm)], [c_42, c_164])).
% 3.34/1.59  tff(c_20, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.59  tff(c_1770, plain, (![A_139, B_140]: (k5_xboole_0(k1_tarski(A_139), k1_tarski(A_139))=k4_xboole_0(k1_tarski(A_139), B_140) | ~r2_hidden(A_139, B_140))), inference(superposition, [status(thm), theory('equality')], [c_1764, c_20])).
% 3.34/1.59  tff(c_1791, plain, (![A_141, B_142]: (k4_xboole_0(k1_tarski(A_141), B_142)=k1_xboole_0 | ~r2_hidden(A_141, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_1770])).
% 3.34/1.59  tff(c_1819, plain, (![B_142, A_141]: (k2_xboole_0(B_142, k1_tarski(A_141))=k2_xboole_0(B_142, k1_xboole_0) | ~r2_hidden(A_141, B_142))), inference(superposition, [status(thm), theory('equality')], [c_1791, c_26])).
% 3.34/1.59  tff(c_1881, plain, (![B_144, A_145]: (k2_xboole_0(B_144, k1_tarski(A_145))=B_144 | ~r2_hidden(A_145, B_144))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1819])).
% 3.34/1.59  tff(c_233, plain, (![B_67, A_66]: (k2_xboole_0(B_67, A_66)=k2_xboole_0(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_227, c_44])).
% 3.34/1.59  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.59  tff(c_253, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_233, c_46])).
% 3.34/1.59  tff(c_1939, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1881, c_253])).
% 3.34/1.59  tff(c_2000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1939])).
% 3.34/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.59  
% 3.34/1.59  Inference rules
% 3.34/1.59  ----------------------
% 3.34/1.59  #Ref     : 0
% 3.34/1.59  #Sup     : 462
% 3.34/1.59  #Fact    : 0
% 3.34/1.59  #Define  : 0
% 3.34/1.59  #Split   : 1
% 3.34/1.59  #Chain   : 0
% 3.34/1.59  #Close   : 0
% 3.34/1.59  
% 3.34/1.59  Ordering : KBO
% 3.34/1.59  
% 3.34/1.59  Simplification rules
% 3.34/1.59  ----------------------
% 3.34/1.59  #Subsume      : 26
% 3.34/1.59  #Demod        : 422
% 3.34/1.59  #Tautology    : 357
% 3.34/1.59  #SimpNegUnit  : 1
% 3.34/1.59  #BackRed      : 7
% 3.34/1.59  
% 3.34/1.59  #Partial instantiations: 0
% 3.34/1.59  #Strategies tried      : 1
% 3.34/1.59  
% 3.34/1.59  Timing (in seconds)
% 3.34/1.59  ----------------------
% 3.34/1.59  Preprocessing        : 0.33
% 3.34/1.59  Parsing              : 0.18
% 3.34/1.60  CNF conversion       : 0.02
% 3.34/1.60  Main loop            : 0.47
% 3.34/1.60  Inferencing          : 0.17
% 3.34/1.60  Reduction            : 0.19
% 3.34/1.60  Demodulation         : 0.15
% 3.34/1.60  BG Simplification    : 0.02
% 3.34/1.60  Subsumption          : 0.07
% 3.34/1.60  Abstraction          : 0.03
% 3.34/1.60  MUC search           : 0.00
% 3.34/1.60  Cooper               : 0.00
% 3.34/1.60  Total                : 0.83
% 3.34/1.60  Index Insertion      : 0.00
% 3.34/1.60  Index Deletion       : 0.00
% 3.34/1.60  Index Matching       : 0.00
% 3.34/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
