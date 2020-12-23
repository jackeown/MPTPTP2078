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
% DateTime   : Thu Dec  3 09:50:38 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :   67 (  78 expanded)
%              Number of leaves         :   36 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  76 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_78,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_162,plain,(
    ! [A_76,B_77] : k1_enumset1(A_76,A_76,B_77) = k2_tarski(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [E_28,A_22,C_24] : r2_hidden(E_28,k1_enumset1(A_22,E_28,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_180,plain,(
    ! [A_78,B_79] : r2_hidden(A_78,k2_tarski(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_42])).

tff(c_183,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_180])).

tff(c_32,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_241,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_250,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_334,plain,(
    ! [A_111,B_112,C_113] : k5_xboole_0(k5_xboole_0(A_111,B_112),C_113) = k5_xboole_0(A_111,k5_xboole_0(B_112,C_113)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2911,plain,(
    ! [A_205,B_206,C_207] : k5_xboole_0(A_205,k5_xboole_0(k3_xboole_0(A_205,B_206),C_207)) = k5_xboole_0(k4_xboole_0(A_205,B_206),C_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_334])).

tff(c_3863,plain,(
    ! [A_220,A_221,B_222] : k5_xboole_0(A_220,k5_xboole_0(A_221,k3_xboole_0(A_220,B_222))) = k5_xboole_0(k4_xboole_0(A_220,B_222),A_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2911])).

tff(c_4031,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_3863])).

tff(c_4076,plain,(
    ! [B_223,A_224] : k5_xboole_0(k4_xboole_0(B_223,A_224),A_224) = k2_xboole_0(B_223,A_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4031])).

tff(c_4235,plain,(
    ! [A_229,B_230] : k5_xboole_0(A_229,k4_xboole_0(B_230,A_229)) = k2_xboole_0(B_230,A_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_4076,c_4])).

tff(c_4308,plain,(
    ! [B_230,A_229] : k2_xboole_0(B_230,A_229) = k2_xboole_0(A_229,B_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_4235,c_36])).

tff(c_80,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_256,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_266,plain,
    ( k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_256])).

tff(c_321,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_4339,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4308,c_321])).

tff(c_4343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4339])).

tff(c_4344,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4369,plain,(
    ! [D_231] :
      ( ~ r2_hidden(D_231,k1_tarski('#skF_5'))
      | r2_hidden(D_231,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4344,c_10])).

tff(c_4373,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_183,c_4369])).

tff(c_4377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.96/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.83  
% 6.96/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.84  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.96/2.84  
% 6.96/2.84  %Foreground sorts:
% 6.96/2.84  
% 6.96/2.84  
% 6.96/2.84  %Background operators:
% 6.96/2.84  
% 6.96/2.84  
% 6.96/2.84  %Foreground operators:
% 6.96/2.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.96/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.96/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.96/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.96/2.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.96/2.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.96/2.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.96/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.96/2.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.96/2.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.96/2.84  tff('#skF_5', type, '#skF_5': $i).
% 6.96/2.84  tff('#skF_6', type, '#skF_6': $i).
% 6.96/2.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.96/2.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.96/2.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.84  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.96/2.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.96/2.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.96/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.96/2.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.96/2.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.96/2.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.96/2.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.84  
% 6.96/2.85  tff(f_88, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 6.96/2.85  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.96/2.85  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.96/2.85  tff(f_67, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.96/2.85  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.96/2.85  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.96/2.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.96/2.85  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.96/2.85  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.96/2.85  tff(f_50, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.96/2.85  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.96/2.85  tff(f_38, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.96/2.85  tff(c_78, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.96/2.85  tff(c_62, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.96/2.85  tff(c_162, plain, (![A_76, B_77]: (k1_enumset1(A_76, A_76, B_77)=k2_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.96/2.85  tff(c_42, plain, (![E_28, A_22, C_24]: (r2_hidden(E_28, k1_enumset1(A_22, E_28, C_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.96/2.85  tff(c_180, plain, (![A_78, B_79]: (r2_hidden(A_78, k2_tarski(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_42])).
% 6.96/2.85  tff(c_183, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_180])).
% 6.96/2.85  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.96/2.85  tff(c_36, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.96/2.85  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.96/2.85  tff(c_241, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.96/2.85  tff(c_250, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_241])).
% 6.96/2.85  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.96/2.85  tff(c_30, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.96/2.85  tff(c_334, plain, (![A_111, B_112, C_113]: (k5_xboole_0(k5_xboole_0(A_111, B_112), C_113)=k5_xboole_0(A_111, k5_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.96/2.85  tff(c_2911, plain, (![A_205, B_206, C_207]: (k5_xboole_0(A_205, k5_xboole_0(k3_xboole_0(A_205, B_206), C_207))=k5_xboole_0(k4_xboole_0(A_205, B_206), C_207))), inference(superposition, [status(thm), theory('equality')], [c_30, c_334])).
% 6.96/2.85  tff(c_3863, plain, (![A_220, A_221, B_222]: (k5_xboole_0(A_220, k5_xboole_0(A_221, k3_xboole_0(A_220, B_222)))=k5_xboole_0(k4_xboole_0(A_220, B_222), A_221))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2911])).
% 6.96/2.85  tff(c_4031, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_3863])).
% 6.96/2.85  tff(c_4076, plain, (![B_223, A_224]: (k5_xboole_0(k4_xboole_0(B_223, A_224), A_224)=k2_xboole_0(B_223, A_224))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4031])).
% 6.96/2.85  tff(c_4235, plain, (![A_229, B_230]: (k5_xboole_0(A_229, k4_xboole_0(B_230, A_229))=k2_xboole_0(B_230, A_229))), inference(superposition, [status(thm), theory('equality')], [c_4076, c_4])).
% 6.96/2.85  tff(c_4308, plain, (![B_230, A_229]: (k2_xboole_0(B_230, A_229)=k2_xboole_0(A_229, B_230))), inference(superposition, [status(thm), theory('equality')], [c_4235, c_36])).
% 6.96/2.85  tff(c_80, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.96/2.85  tff(c_256, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.96/2.85  tff(c_266, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_256])).
% 6.96/2.85  tff(c_321, plain, (~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_266])).
% 6.96/2.85  tff(c_4339, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4308, c_321])).
% 6.96/2.85  tff(c_4343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_4339])).
% 6.96/2.85  tff(c_4344, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_266])).
% 6.96/2.85  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.96/2.85  tff(c_4369, plain, (![D_231]: (~r2_hidden(D_231, k1_tarski('#skF_5')) | r2_hidden(D_231, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4344, c_10])).
% 6.96/2.85  tff(c_4373, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_183, c_4369])).
% 6.96/2.85  tff(c_4377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4373])).
% 6.96/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.85  
% 6.96/2.85  Inference rules
% 6.96/2.85  ----------------------
% 6.96/2.85  #Ref     : 0
% 6.96/2.85  #Sup     : 1074
% 6.96/2.85  #Fact    : 6
% 6.96/2.85  #Define  : 0
% 6.96/2.85  #Split   : 1
% 6.96/2.85  #Chain   : 0
% 6.96/2.85  #Close   : 0
% 6.96/2.85  
% 6.96/2.85  Ordering : KBO
% 6.96/2.85  
% 6.96/2.85  Simplification rules
% 6.96/2.85  ----------------------
% 6.96/2.85  #Subsume      : 170
% 6.96/2.85  #Demod        : 548
% 6.96/2.85  #Tautology    : 197
% 6.96/2.85  #SimpNegUnit  : 1
% 6.96/2.85  #BackRed      : 3
% 6.96/2.85  
% 6.96/2.85  #Partial instantiations: 0
% 6.96/2.85  #Strategies tried      : 1
% 6.96/2.85  
% 6.96/2.85  Timing (in seconds)
% 6.96/2.85  ----------------------
% 7.11/2.85  Preprocessing        : 0.39
% 7.11/2.85  Parsing              : 0.19
% 7.11/2.85  CNF conversion       : 0.03
% 7.11/2.85  Main loop            : 1.60
% 7.11/2.85  Inferencing          : 0.38
% 7.11/2.85  Reduction            : 0.90
% 7.11/2.85  Demodulation         : 0.82
% 7.11/2.85  BG Simplification    : 0.07
% 7.11/2.85  Subsumption          : 0.19
% 7.11/2.85  Abstraction          : 0.08
% 7.11/2.85  MUC search           : 0.00
% 7.11/2.85  Cooper               : 0.00
% 7.11/2.85  Total                : 2.02
% 7.11/2.85  Index Insertion      : 0.00
% 7.11/2.85  Index Deletion       : 0.00
% 7.11/2.85  Index Matching       : 0.00
% 7.11/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
