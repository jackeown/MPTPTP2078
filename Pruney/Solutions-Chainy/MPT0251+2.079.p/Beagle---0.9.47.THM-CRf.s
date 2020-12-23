%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:57 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 104 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :   69 ( 108 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_367,plain,(
    ! [A_78,B_79] : k4_xboole_0(k2_xboole_0(A_78,B_79),B_79) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_376,plain,(
    ! [B_79,A_78] : k2_xboole_0(B_79,k4_xboole_0(A_78,B_79)) = k2_xboole_0(B_79,k2_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_34])).

tff(c_698,plain,(
    ! [B_92,A_93] : k2_xboole_0(B_92,k2_xboole_0(A_93,B_92)) = k2_xboole_0(B_92,A_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_376])).

tff(c_795,plain,(
    ! [B_98,A_99] : k2_xboole_0(B_98,k2_xboole_0(B_98,A_99)) = k2_xboole_0(B_98,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_698])).

tff(c_849,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) = k2_xboole_0(k3_xboole_0(A_23,B_24),A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_795])).

tff(c_896,plain,(
    ! [A_102,B_103] : k2_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_849])).

tff(c_91,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_30])).

tff(c_932,plain,(
    ! [B_104] : k3_xboole_0(k1_xboole_0,B_104) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_107])).

tff(c_28,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_965,plain,(
    ! [B_105] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_28])).

tff(c_26,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_187,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_191,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_26,c_187])).

tff(c_293,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_302,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k4_xboole_0(B_12,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_293])).

tff(c_980,plain,(
    ! [B_105] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_302])).

tff(c_995,plain,(
    ! [B_105] : k4_xboole_0(k1_xboole_0,B_105) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_980])).

tff(c_398,plain,(
    ! [A_45] : k4_xboole_0(k1_xboole_0,A_45) = k4_xboole_0(A_45,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_367])).

tff(c_1001,plain,(
    ! [A_45] : k4_xboole_0(A_45,A_45) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_398])).

tff(c_1044,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_302])).

tff(c_42,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1240,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_tarski(k2_tarski(A_123,B_124),C_125)
      | ~ r2_hidden(B_124,C_125)
      | ~ r2_hidden(A_123,C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1380,plain,(
    ! [A_137,C_138] :
      ( r1_tarski(k1_tarski(A_137),C_138)
      | ~ r2_hidden(A_137,C_138)
      | ~ r2_hidden(A_137,C_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1240])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1412,plain,(
    ! [A_140,C_141] :
      ( k3_xboole_0(k1_tarski(A_140),C_141) = k1_tarski(A_140)
      | ~ r2_hidden(A_140,C_141) ) ),
    inference(resolution,[status(thm)],[c_1380,c_32])).

tff(c_1431,plain,(
    ! [A_140,C_141] :
      ( k5_xboole_0(k1_tarski(A_140),k1_tarski(A_140)) = k4_xboole_0(k1_tarski(A_140),C_141)
      | ~ r2_hidden(A_140,C_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1412,c_28])).

tff(c_1456,plain,(
    ! [A_144,C_145] :
      ( k4_xboole_0(k1_tarski(A_144),C_145) = k1_xboole_0
      | ~ r2_hidden(A_144,C_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_1431])).

tff(c_1472,plain,(
    ! [C_145,A_144] :
      ( k2_xboole_0(C_145,k1_tarski(A_144)) = k2_xboole_0(C_145,k1_xboole_0)
      | ~ r2_hidden(A_144,C_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_34])).

tff(c_1499,plain,(
    ! [C_146,A_147] :
      ( k2_xboole_0(C_146,k1_tarski(A_147)) = C_146
      | ~ r2_hidden(A_147,C_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1472])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_62,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_1535,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1499,c_62])).

tff(c_1570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.55  
% 3.23/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.55  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.55  
% 3.23/1.55  %Foreground sorts:
% 3.23/1.55  
% 3.23/1.55  
% 3.23/1.55  %Background operators:
% 3.23/1.55  
% 3.23/1.55  
% 3.23/1.55  %Foreground operators:
% 3.23/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.23/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.55  
% 3.23/1.56  tff(f_84, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.23/1.56  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.23/1.56  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.23/1.56  tff(f_63, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.23/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.23/1.56  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.23/1.56  tff(f_61, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.23/1.56  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.56  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.56  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.56  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.23/1.56  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.23/1.56  tff(c_60, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.56  tff(c_30, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.56  tff(c_36, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.56  tff(c_40, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.23/1.56  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.56  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.56  tff(c_367, plain, (![A_78, B_79]: (k4_xboole_0(k2_xboole_0(A_78, B_79), B_79)=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.56  tff(c_376, plain, (![B_79, A_78]: (k2_xboole_0(B_79, k4_xboole_0(A_78, B_79))=k2_xboole_0(B_79, k2_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_367, c_34])).
% 3.23/1.56  tff(c_698, plain, (![B_92, A_93]: (k2_xboole_0(B_92, k2_xboole_0(A_93, B_92))=k2_xboole_0(B_92, A_93))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_376])).
% 3.23/1.56  tff(c_795, plain, (![B_98, A_99]: (k2_xboole_0(B_98, k2_xboole_0(B_98, A_99))=k2_xboole_0(B_98, A_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_698])).
% 3.23/1.56  tff(c_849, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24))=k2_xboole_0(k3_xboole_0(A_23, B_24), A_23))), inference(superposition, [status(thm), theory('equality')], [c_40, c_795])).
% 3.23/1.56  tff(c_896, plain, (![A_102, B_103]: (k2_xboole_0(A_102, k3_xboole_0(A_102, B_103))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_849])).
% 3.23/1.56  tff(c_91, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.56  tff(c_107, plain, (![A_45]: (k2_xboole_0(k1_xboole_0, A_45)=A_45)), inference(superposition, [status(thm), theory('equality')], [c_91, c_30])).
% 3.23/1.56  tff(c_932, plain, (![B_104]: (k3_xboole_0(k1_xboole_0, B_104)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_896, c_107])).
% 3.23/1.56  tff(c_28, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.56  tff(c_965, plain, (![B_105]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_105))), inference(superposition, [status(thm), theory('equality')], [c_932, c_28])).
% 3.23/1.56  tff(c_26, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.56  tff(c_187, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.56  tff(c_191, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_26, c_187])).
% 3.23/1.56  tff(c_293, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.56  tff(c_302, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k4_xboole_0(B_12, B_12))), inference(superposition, [status(thm), theory('equality')], [c_191, c_293])).
% 3.23/1.56  tff(c_980, plain, (![B_105]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_105))), inference(superposition, [status(thm), theory('equality')], [c_965, c_302])).
% 3.23/1.56  tff(c_995, plain, (![B_105]: (k4_xboole_0(k1_xboole_0, B_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_980])).
% 3.23/1.56  tff(c_398, plain, (![A_45]: (k4_xboole_0(k1_xboole_0, A_45)=k4_xboole_0(A_45, A_45))), inference(superposition, [status(thm), theory('equality')], [c_107, c_367])).
% 3.23/1.56  tff(c_1001, plain, (![A_45]: (k4_xboole_0(A_45, A_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_995, c_398])).
% 3.23/1.56  tff(c_1044, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_302])).
% 3.23/1.56  tff(c_42, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.56  tff(c_1240, plain, (![A_123, B_124, C_125]: (r1_tarski(k2_tarski(A_123, B_124), C_125) | ~r2_hidden(B_124, C_125) | ~r2_hidden(A_123, C_125))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.56  tff(c_1380, plain, (![A_137, C_138]: (r1_tarski(k1_tarski(A_137), C_138) | ~r2_hidden(A_137, C_138) | ~r2_hidden(A_137, C_138))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1240])).
% 3.23/1.56  tff(c_32, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.56  tff(c_1412, plain, (![A_140, C_141]: (k3_xboole_0(k1_tarski(A_140), C_141)=k1_tarski(A_140) | ~r2_hidden(A_140, C_141))), inference(resolution, [status(thm)], [c_1380, c_32])).
% 3.23/1.56  tff(c_1431, plain, (![A_140, C_141]: (k5_xboole_0(k1_tarski(A_140), k1_tarski(A_140))=k4_xboole_0(k1_tarski(A_140), C_141) | ~r2_hidden(A_140, C_141))), inference(superposition, [status(thm), theory('equality')], [c_1412, c_28])).
% 3.23/1.56  tff(c_1456, plain, (![A_144, C_145]: (k4_xboole_0(k1_tarski(A_144), C_145)=k1_xboole_0 | ~r2_hidden(A_144, C_145))), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_1431])).
% 3.23/1.56  tff(c_1472, plain, (![C_145, A_144]: (k2_xboole_0(C_145, k1_tarski(A_144))=k2_xboole_0(C_145, k1_xboole_0) | ~r2_hidden(A_144, C_145))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_34])).
% 3.23/1.56  tff(c_1499, plain, (![C_146, A_147]: (k2_xboole_0(C_146, k1_tarski(A_147))=C_146 | ~r2_hidden(A_147, C_146))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1472])).
% 3.23/1.56  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.56  tff(c_62, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 3.23/1.56  tff(c_1535, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1499, c_62])).
% 3.23/1.56  tff(c_1570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1535])).
% 3.23/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.56  
% 3.23/1.56  Inference rules
% 3.23/1.56  ----------------------
% 3.23/1.56  #Ref     : 0
% 3.23/1.56  #Sup     : 352
% 3.23/1.56  #Fact    : 0
% 3.23/1.56  #Define  : 0
% 3.23/1.56  #Split   : 1
% 3.23/1.56  #Chain   : 0
% 3.23/1.56  #Close   : 0
% 3.23/1.56  
% 3.23/1.56  Ordering : KBO
% 3.23/1.56  
% 3.23/1.56  Simplification rules
% 3.23/1.56  ----------------------
% 3.23/1.56  #Subsume      : 21
% 3.23/1.56  #Demod        : 258
% 3.23/1.56  #Tautology    : 262
% 3.23/1.56  #SimpNegUnit  : 0
% 3.23/1.56  #BackRed      : 6
% 3.23/1.56  
% 3.23/1.56  #Partial instantiations: 0
% 3.23/1.56  #Strategies tried      : 1
% 3.23/1.56  
% 3.23/1.56  Timing (in seconds)
% 3.23/1.56  ----------------------
% 3.23/1.57  Preprocessing        : 0.35
% 3.23/1.57  Parsing              : 0.18
% 3.23/1.57  CNF conversion       : 0.02
% 3.23/1.57  Main loop            : 0.41
% 3.23/1.57  Inferencing          : 0.15
% 3.23/1.57  Reduction            : 0.15
% 3.23/1.57  Demodulation         : 0.12
% 3.23/1.57  BG Simplification    : 0.02
% 3.23/1.57  Subsumption          : 0.07
% 3.23/1.57  Abstraction          : 0.02
% 3.23/1.57  MUC search           : 0.00
% 3.23/1.57  Cooper               : 0.00
% 3.23/1.57  Total                : 0.79
% 3.23/1.57  Index Insertion      : 0.00
% 3.23/1.57  Index Deletion       : 0.00
% 3.23/1.57  Index Matching       : 0.00
% 3.23/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
