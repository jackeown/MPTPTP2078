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
% DateTime   : Thu Dec  3 09:52:48 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 194 expanded)
%              Number of leaves         :   35 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :   76 ( 205 expanded)
%              Number of equality atoms :   40 ( 167 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_380,plain,(
    ! [A_93,B_94,C_95] : k5_xboole_0(k5_xboole_0(A_93,B_94),C_95) = k5_xboole_0(A_93,k5_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k2_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1311,plain,(
    ! [A_128,B_129] : k5_xboole_0(A_128,k5_xboole_0(B_129,k2_xboole_0(A_128,B_129))) = k3_xboole_0(A_128,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_28])).

tff(c_26,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_263,plain,(
    ! [A_88,B_89] : k5_xboole_0(k5_xboole_0(A_88,B_89),k2_xboole_0(A_88,B_89)) = k3_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_281,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_263])).

tff(c_290,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4,c_281])).

tff(c_441,plain,(
    ! [A_19,C_95] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_95)) = k5_xboole_0(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_380])).

tff(c_459,plain,(
    ! [A_19,C_95] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_95)) = C_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_441])).

tff(c_1326,plain,(
    ! [B_129,A_128] : k5_xboole_0(B_129,k2_xboole_0(A_128,B_129)) = k5_xboole_0(A_128,k3_xboole_0(A_128,B_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_459])).

tff(c_1393,plain,(
    ! [B_130,A_131] : k5_xboole_0(B_130,k2_xboole_0(A_131,B_130)) = k4_xboole_0(A_131,B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1326])).

tff(c_1517,plain,(
    ! [B_136,A_137] : k5_xboole_0(B_136,k4_xboole_0(A_137,B_136)) = k2_xboole_0(A_137,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_1393,c_459])).

tff(c_1577,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1517])).

tff(c_1587,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1577])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1603,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_22])).

tff(c_46,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_228,plain,(
    ! [A_80,C_81,B_82] :
      ( r1_xboole_0(A_80,C_81)
      | ~ r1_xboole_0(B_82,C_81)
      | ~ r1_tarski(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1622,plain,(
    ! [A_138,B_139,A_140] :
      ( r1_xboole_0(A_138,B_139)
      | ~ r1_tarski(A_138,k1_tarski(A_140))
      | r2_hidden(A_140,B_139) ) ),
    inference(resolution,[status(thm)],[c_46,c_228])).

tff(c_1634,plain,(
    ! [B_141] :
      ( r1_xboole_0('#skF_1',B_141)
      | r2_hidden('#skF_2',B_141) ) ),
    inference(resolution,[status(thm)],[c_1603,c_1622])).

tff(c_44,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_206,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_214,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),A_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_206])).

tff(c_1600,plain,
    ( k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_214])).

tff(c_1608,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1600])).

tff(c_1609,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1608])).

tff(c_1614,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1609])).

tff(c_1638,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1634,c_1614])).

tff(c_20,plain,(
    ! [A_13] :
      ( ~ r1_xboole_0(A_13,A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1643,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1638,c_20])).

tff(c_1648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.54  
% 3.42/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.42/1.54  
% 3.42/1.54  %Foreground sorts:
% 3.42/1.54  
% 3.42/1.54  
% 3.42/1.54  %Background operators:
% 3.42/1.54  
% 3.42/1.54  
% 3.42/1.54  %Foreground operators:
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.42/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.42/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.54  
% 3.42/1.55  tff(f_98, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.42/1.55  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.42/1.55  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.42/1.55  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.42/1.55  tff(f_65, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.42/1.55  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.42/1.55  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.42/1.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.42/1.55  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.42/1.55  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.42/1.55  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.42/1.55  tff(f_81, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.42/1.55  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.55  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.42/1.55  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.55  tff(c_14, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.55  tff(c_54, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.55  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.55  tff(c_380, plain, (![A_93, B_94, C_95]: (k5_xboole_0(k5_xboole_0(A_93, B_94), C_95)=k5_xboole_0(A_93, k5_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.42/1.55  tff(c_28, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k2_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.55  tff(c_1311, plain, (![A_128, B_129]: (k5_xboole_0(A_128, k5_xboole_0(B_129, k2_xboole_0(A_128, B_129)))=k3_xboole_0(A_128, B_129))), inference(superposition, [status(thm), theory('equality')], [c_380, c_28])).
% 3.42/1.55  tff(c_26, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.55  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.55  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.55  tff(c_263, plain, (![A_88, B_89]: (k5_xboole_0(k5_xboole_0(A_88, B_89), k2_xboole_0(A_88, B_89))=k3_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.55  tff(c_281, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_263])).
% 3.42/1.55  tff(c_290, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4, c_281])).
% 3.42/1.55  tff(c_441, plain, (![A_19, C_95]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_95))=k5_xboole_0(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_26, c_380])).
% 3.42/1.55  tff(c_459, plain, (![A_19, C_95]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_95))=C_95)), inference(demodulation, [status(thm), theory('equality')], [c_290, c_441])).
% 3.42/1.55  tff(c_1326, plain, (![B_129, A_128]: (k5_xboole_0(B_129, k2_xboole_0(A_128, B_129))=k5_xboole_0(A_128, k3_xboole_0(A_128, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_1311, c_459])).
% 3.42/1.55  tff(c_1393, plain, (![B_130, A_131]: (k5_xboole_0(B_130, k2_xboole_0(A_131, B_130))=k4_xboole_0(A_131, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1326])).
% 3.42/1.55  tff(c_1517, plain, (![B_136, A_137]: (k5_xboole_0(B_136, k4_xboole_0(A_137, B_136))=k2_xboole_0(A_137, B_136))), inference(superposition, [status(thm), theory('equality')], [c_1393, c_459])).
% 3.42/1.55  tff(c_1577, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1517])).
% 3.42/1.55  tff(c_1587, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1577])).
% 3.42/1.55  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.55  tff(c_1603, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1587, c_22])).
% 3.42/1.55  tff(c_46, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.42/1.55  tff(c_228, plain, (![A_80, C_81, B_82]: (r1_xboole_0(A_80, C_81) | ~r1_xboole_0(B_82, C_81) | ~r1_tarski(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.55  tff(c_1622, plain, (![A_138, B_139, A_140]: (r1_xboole_0(A_138, B_139) | ~r1_tarski(A_138, k1_tarski(A_140)) | r2_hidden(A_140, B_139))), inference(resolution, [status(thm)], [c_46, c_228])).
% 3.42/1.55  tff(c_1634, plain, (![B_141]: (r1_xboole_0('#skF_1', B_141) | r2_hidden('#skF_2', B_141))), inference(resolution, [status(thm)], [c_1603, c_1622])).
% 3.42/1.55  tff(c_44, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.42/1.55  tff(c_50, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.55  tff(c_206, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.55  tff(c_214, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(k2_xboole_0(A_14, B_15), A_14))), inference(resolution, [status(thm)], [c_22, c_206])).
% 3.42/1.55  tff(c_1600, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1587, c_214])).
% 3.42/1.55  tff(c_1608, plain, (k1_tarski('#skF_2')='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1600])).
% 3.42/1.55  tff(c_1609, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_1608])).
% 3.42/1.55  tff(c_1614, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_1609])).
% 3.42/1.55  tff(c_1638, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1634, c_1614])).
% 3.42/1.55  tff(c_20, plain, (![A_13]: (~r1_xboole_0(A_13, A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.55  tff(c_1643, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1638, c_20])).
% 3.42/1.55  tff(c_1648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1643])).
% 3.42/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  Inference rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Ref     : 0
% 3.42/1.55  #Sup     : 392
% 3.42/1.55  #Fact    : 0
% 3.42/1.55  #Define  : 0
% 3.42/1.55  #Split   : 0
% 3.42/1.56  #Chain   : 0
% 3.42/1.56  #Close   : 0
% 3.42/1.56  
% 3.42/1.56  Ordering : KBO
% 3.42/1.56  
% 3.42/1.56  Simplification rules
% 3.42/1.56  ----------------------
% 3.42/1.56  #Subsume      : 7
% 3.42/1.56  #Demod        : 221
% 3.42/1.56  #Tautology    : 240
% 3.42/1.56  #SimpNegUnit  : 3
% 3.42/1.56  #BackRed      : 2
% 3.42/1.56  
% 3.42/1.56  #Partial instantiations: 0
% 3.42/1.56  #Strategies tried      : 1
% 3.42/1.56  
% 3.42/1.56  Timing (in seconds)
% 3.42/1.56  ----------------------
% 3.42/1.56  Preprocessing        : 0.33
% 3.42/1.56  Parsing              : 0.18
% 3.42/1.56  CNF conversion       : 0.02
% 3.42/1.56  Main loop            : 0.45
% 3.42/1.56  Inferencing          : 0.17
% 3.42/1.56  Reduction            : 0.17
% 3.42/1.56  Demodulation         : 0.13
% 3.42/1.56  BG Simplification    : 0.02
% 3.42/1.56  Subsumption          : 0.07
% 3.42/1.56  Abstraction          : 0.02
% 3.42/1.56  MUC search           : 0.00
% 3.42/1.56  Cooper               : 0.00
% 3.42/1.56  Total                : 0.82
% 3.42/1.56  Index Insertion      : 0.00
% 3.42/1.56  Index Deletion       : 0.00
% 3.42/1.56  Index Matching       : 0.00
% 3.42/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
