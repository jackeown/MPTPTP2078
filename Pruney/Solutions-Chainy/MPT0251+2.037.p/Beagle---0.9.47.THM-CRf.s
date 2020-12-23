%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 10.52s
% Output     : CNFRefutation 10.52s
% Verified   : 
% Statistics : Number of formulae       :   67 (  70 expanded)
%              Number of leaves         :   36 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 (  87 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_86,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_770,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_tarski(k2_tarski(A_128,B_129),C_130)
      | ~ r2_hidden(B_129,C_130)
      | ~ r2_hidden(A_128,C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_794,plain,(
    ! [A_29,C_130] :
      ( r1_tarski(k1_tarski(A_29),C_130)
      | ~ r2_hidden(A_29,C_130)
      | ~ r2_hidden(A_29,C_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_770])).

tff(c_1230,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_hidden('#skF_2'(A_172,B_173,C_174),A_172)
      | r2_hidden('#skF_3'(A_172,B_173,C_174),C_174)
      | k4_xboole_0(A_172,B_173) = C_174 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5899,plain,(
    ! [A_426,B_427,C_428,B_429] :
      ( r2_hidden('#skF_2'(A_426,B_427,C_428),B_429)
      | ~ r1_tarski(A_426,B_429)
      | r2_hidden('#skF_3'(A_426,B_427,C_428),C_428)
      | k4_xboole_0(A_426,B_427) = C_428 ) ),
    inference(resolution,[status(thm)],[c_1230,c_2])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22851,plain,(
    ! [A_868,B_869,C_870] :
      ( ~ r1_tarski(A_868,B_869)
      | r2_hidden('#skF_3'(A_868,B_869,C_870),C_870)
      | k4_xboole_0(A_868,B_869) = C_870 ) ),
    inference(resolution,[status(thm)],[c_5899,c_22])).

tff(c_44,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [B_18] : r1_tarski(B_18,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_121,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    ! [B_18] : k3_xboole_0(B_18,B_18) = B_18 ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_428,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,k3_xboole_0(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_458,plain,(
    ! [B_99,C_100] :
      ( ~ r1_xboole_0(B_99,B_99)
      | ~ r2_hidden(C_100,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_428])).

tff(c_462,plain,(
    ! [C_100] : ~ r2_hidden(C_100,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_458])).

tff(c_22930,plain,(
    ! [A_871,B_872] :
      ( ~ r1_tarski(A_871,B_872)
      | k4_xboole_0(A_871,B_872) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22851,c_462])).

tff(c_22986,plain,(
    ! [A_873,C_874] :
      ( k4_xboole_0(k1_tarski(A_873),C_874) = k1_xboole_0
      | ~ r2_hidden(A_873,C_874) ) ),
    inference(resolution,[status(thm)],[c_794,c_22930])).

tff(c_42,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_23434,plain,(
    ! [C_874,A_873] :
      ( k2_xboole_0(C_874,k1_tarski(A_873)) = k2_xboole_0(C_874,k1_xboole_0)
      | ~ r2_hidden(A_873,C_874) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22986,c_42])).

tff(c_23619,plain,(
    ! [C_875,A_876] :
      ( k2_xboole_0(C_875,k1_tarski(A_876)) = C_875
      | ~ r2_hidden(A_876,C_875) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_23434])).

tff(c_46,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_135,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_179,plain,(
    ! [B_58,A_59] : k3_tarski(k2_tarski(B_58,A_59)) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_135])).

tff(c_56,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_185,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_56])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_205,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_64])).

tff(c_23649,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_23619,c_205])).

tff(c_23706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.52/4.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.52/4.19  
% 10.52/4.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.52/4.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.52/4.20  
% 10.52/4.20  %Foreground sorts:
% 10.52/4.20  
% 10.52/4.20  
% 10.52/4.20  %Background operators:
% 10.52/4.20  
% 10.52/4.20  
% 10.52/4.20  %Foreground operators:
% 10.52/4.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.52/4.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.52/4.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.52/4.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.52/4.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.52/4.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.52/4.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.52/4.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.52/4.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.52/4.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.52/4.20  tff('#skF_5', type, '#skF_5': $i).
% 10.52/4.20  tff('#skF_6', type, '#skF_6': $i).
% 10.52/4.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.52/4.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.52/4.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.52/4.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.52/4.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.52/4.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.52/4.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.52/4.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.52/4.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.52/4.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.52/4.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.52/4.20  
% 10.52/4.21  tff(f_97, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 10.52/4.21  tff(f_66, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.52/4.21  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.52/4.21  tff(f_92, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.52/4.21  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.52/4.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.52/4.21  tff(f_74, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.52/4.21  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.52/4.21  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.52/4.21  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.52/4.21  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.52/4.21  tff(f_76, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.52/4.21  tff(f_86, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.52/4.21  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.52/4.21  tff(c_38, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.52/4.21  tff(c_48, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.52/4.21  tff(c_770, plain, (![A_128, B_129, C_130]: (r1_tarski(k2_tarski(A_128, B_129), C_130) | ~r2_hidden(B_129, C_130) | ~r2_hidden(A_128, C_130))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.52/4.21  tff(c_794, plain, (![A_29, C_130]: (r1_tarski(k1_tarski(A_29), C_130) | ~r2_hidden(A_29, C_130) | ~r2_hidden(A_29, C_130))), inference(superposition, [status(thm), theory('equality')], [c_48, c_770])).
% 10.52/4.21  tff(c_1230, plain, (![A_172, B_173, C_174]: (r2_hidden('#skF_2'(A_172, B_173, C_174), A_172) | r2_hidden('#skF_3'(A_172, B_173, C_174), C_174) | k4_xboole_0(A_172, B_173)=C_174)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.52/4.21  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.52/4.21  tff(c_5899, plain, (![A_426, B_427, C_428, B_429]: (r2_hidden('#skF_2'(A_426, B_427, C_428), B_429) | ~r1_tarski(A_426, B_429) | r2_hidden('#skF_3'(A_426, B_427, C_428), C_428) | k4_xboole_0(A_426, B_427)=C_428)), inference(resolution, [status(thm)], [c_1230, c_2])).
% 10.52/4.21  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.52/4.21  tff(c_22851, plain, (![A_868, B_869, C_870]: (~r1_tarski(A_868, B_869) | r2_hidden('#skF_3'(A_868, B_869, C_870), C_870) | k4_xboole_0(A_868, B_869)=C_870)), inference(resolution, [status(thm)], [c_5899, c_22])).
% 10.52/4.21  tff(c_44, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.52/4.21  tff(c_34, plain, (![B_18]: (r1_tarski(B_18, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.52/4.21  tff(c_121, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.52/4.21  tff(c_125, plain, (![B_18]: (k3_xboole_0(B_18, B_18)=B_18)), inference(resolution, [status(thm)], [c_34, c_121])).
% 10.52/4.21  tff(c_428, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, k3_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.52/4.21  tff(c_458, plain, (![B_99, C_100]: (~r1_xboole_0(B_99, B_99) | ~r2_hidden(C_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_125, c_428])).
% 10.52/4.21  tff(c_462, plain, (![C_100]: (~r2_hidden(C_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_458])).
% 10.52/4.21  tff(c_22930, plain, (![A_871, B_872]: (~r1_tarski(A_871, B_872) | k4_xboole_0(A_871, B_872)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22851, c_462])).
% 10.52/4.21  tff(c_22986, plain, (![A_873, C_874]: (k4_xboole_0(k1_tarski(A_873), C_874)=k1_xboole_0 | ~r2_hidden(A_873, C_874))), inference(resolution, [status(thm)], [c_794, c_22930])).
% 10.52/4.21  tff(c_42, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.52/4.21  tff(c_23434, plain, (![C_874, A_873]: (k2_xboole_0(C_874, k1_tarski(A_873))=k2_xboole_0(C_874, k1_xboole_0) | ~r2_hidden(A_873, C_874))), inference(superposition, [status(thm), theory('equality')], [c_22986, c_42])).
% 10.52/4.21  tff(c_23619, plain, (![C_875, A_876]: (k2_xboole_0(C_875, k1_tarski(A_876))=C_875 | ~r2_hidden(A_876, C_875))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_23434])).
% 10.52/4.21  tff(c_46, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.52/4.21  tff(c_135, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.52/4.21  tff(c_179, plain, (![B_58, A_59]: (k3_tarski(k2_tarski(B_58, A_59))=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_46, c_135])).
% 10.52/4.21  tff(c_56, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.52/4.21  tff(c_185, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_179, c_56])).
% 10.52/4.21  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.52/4.21  tff(c_205, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_64])).
% 10.52/4.21  tff(c_23649, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_23619, c_205])).
% 10.52/4.21  tff(c_23706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_23649])).
% 10.52/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.52/4.21  
% 10.52/4.21  Inference rules
% 10.52/4.21  ----------------------
% 10.52/4.21  #Ref     : 0
% 10.52/4.21  #Sup     : 6186
% 10.52/4.21  #Fact    : 0
% 10.52/4.21  #Define  : 0
% 10.52/4.21  #Split   : 7
% 10.52/4.21  #Chain   : 0
% 10.52/4.21  #Close   : 0
% 10.52/4.21  
% 10.52/4.21  Ordering : KBO
% 10.52/4.21  
% 10.52/4.21  Simplification rules
% 10.52/4.21  ----------------------
% 10.52/4.21  #Subsume      : 3304
% 10.52/4.21  #Demod        : 2714
% 10.52/4.21  #Tautology    : 1314
% 10.52/4.21  #SimpNegUnit  : 126
% 10.52/4.21  #BackRed      : 6
% 10.52/4.21  
% 10.52/4.21  #Partial instantiations: 0
% 10.52/4.21  #Strategies tried      : 1
% 10.52/4.21  
% 10.52/4.21  Timing (in seconds)
% 10.52/4.21  ----------------------
% 10.52/4.21  Preprocessing        : 0.34
% 10.52/4.21  Parsing              : 0.18
% 10.52/4.21  CNF conversion       : 0.03
% 10.52/4.21  Main loop            : 3.11
% 10.52/4.21  Inferencing          : 0.77
% 10.52/4.21  Reduction            : 1.00
% 10.52/4.21  Demodulation         : 0.74
% 10.52/4.21  BG Simplification    : 0.07
% 10.52/4.21  Subsumption          : 1.10
% 10.52/4.21  Abstraction          : 0.12
% 10.52/4.21  MUC search           : 0.00
% 10.52/4.21  Cooper               : 0.00
% 10.52/4.21  Total                : 3.48
% 10.52/4.21  Index Insertion      : 0.00
% 10.52/4.21  Index Deletion       : 0.00
% 10.52/4.21  Index Matching       : 0.00
% 10.52/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
