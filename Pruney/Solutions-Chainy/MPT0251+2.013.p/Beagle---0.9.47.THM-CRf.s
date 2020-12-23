%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:47 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 159 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :   77 ( 165 expanded)
%              Number of equality atoms :   51 ( 127 expanded)
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

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_62,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,(
    ! [B_65,A_66] : k3_tarski(k2_tarski(B_65,A_66)) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_150])).

tff(c_52,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_348,plain,(
    ! [B_67,A_68] : k2_xboole_0(B_67,A_68) = k2_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_52])).

tff(c_30,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_364,plain,(
    ! [A_68] : k2_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_30])).

tff(c_395,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_30])).

tff(c_36,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_408,plain,(
    ! [B_20] : k4_xboole_0(B_20,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_36])).

tff(c_435,plain,(
    ! [B_20] : k4_xboole_0(B_20,k1_xboole_0) = B_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_408])).

tff(c_34,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_194,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_203,plain,(
    ! [A_57] : k3_xboole_0(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [A_57] : k3_xboole_0(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_486,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_495,plain,(
    ! [A_57] : k5_xboole_0(A_57,k1_xboole_0) = k4_xboole_0(A_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_486])).

tff(c_510,plain,(
    ! [A_57] : k5_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_495])).

tff(c_201,plain,(
    ! [A_18] : k3_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_501,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_486])).

tff(c_551,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_501])).

tff(c_606,plain,(
    ! [A_93,B_94] : k4_xboole_0(k2_xboole_0(A_93,B_94),B_94) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_626,plain,(
    ! [A_68] : k4_xboole_0(k1_xboole_0,A_68) = k4_xboole_0(A_68,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_606])).

tff(c_647,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_626])).

tff(c_26,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_202,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_498,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k4_xboole_0(B_12,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_486])).

tff(c_649,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_498])).

tff(c_44,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1241,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(k2_tarski(A_126,B_127),C_128)
      | ~ r2_hidden(B_127,C_128)
      | ~ r2_hidden(A_126,C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2811,plain,(
    ! [A_175,C_176] :
      ( r1_tarski(k1_tarski(A_175),C_176)
      | ~ r2_hidden(A_175,C_176)
      | ~ r2_hidden(A_175,C_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1241])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2843,plain,(
    ! [A_178,C_179] :
      ( k3_xboole_0(k1_tarski(A_178),C_179) = k1_tarski(A_178)
      | ~ r2_hidden(A_178,C_179) ) ),
    inference(resolution,[status(thm)],[c_2811,c_32])).

tff(c_28,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2852,plain,(
    ! [A_178,C_179] :
      ( k5_xboole_0(k1_tarski(A_178),k1_tarski(A_178)) = k4_xboole_0(k1_tarski(A_178),C_179)
      | ~ r2_hidden(A_178,C_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_28])).

tff(c_2895,plain,(
    ! [A_180,C_181] :
      ( k4_xboole_0(k1_tarski(A_180),C_181) = k1_xboole_0
      | ~ r2_hidden(A_180,C_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_2852])).

tff(c_40,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2921,plain,(
    ! [C_181,A_180] :
      ( k2_xboole_0(C_181,k1_tarski(A_180)) = k5_xboole_0(C_181,k1_xboole_0)
      | ~ r2_hidden(A_180,C_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2895,c_40])).

tff(c_2989,plain,(
    ! [C_184,A_185] :
      ( k2_xboole_0(C_184,k1_tarski(A_185)) = C_184
      | ~ r2_hidden(A_185,C_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_2921])).

tff(c_327,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_52])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_347,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_60])).

tff(c_3067,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2989,c_347])).

tff(c_3138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.92  
% 3.92/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.92  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.92  
% 3.92/1.92  %Foreground sorts:
% 3.92/1.92  
% 3.92/1.92  
% 3.92/1.92  %Background operators:
% 3.92/1.92  
% 3.92/1.92  
% 3.92/1.92  %Foreground operators:
% 3.92/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.92/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.92/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.92/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.92/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.92/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.92/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.92/1.92  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.92  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.92/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.92/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.92/1.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.92/1.92  
% 3.92/1.94  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.92/1.94  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.92/1.94  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.92/1.94  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.92/1.94  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.92/1.94  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.92/1.94  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.92/1.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.92/1.94  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.92/1.94  tff(f_61, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.92/1.94  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.92/1.94  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.92/1.94  tff(f_81, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.92/1.94  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.92/1.94  tff(c_62, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.92/1.94  tff(c_42, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.92/1.94  tff(c_150, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.92/1.94  tff(c_321, plain, (![B_65, A_66]: (k3_tarski(k2_tarski(B_65, A_66))=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_42, c_150])).
% 3.92/1.94  tff(c_52, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.92/1.94  tff(c_348, plain, (![B_67, A_68]: (k2_xboole_0(B_67, A_68)=k2_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_321, c_52])).
% 3.92/1.94  tff(c_30, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.92/1.94  tff(c_364, plain, (![A_68]: (k2_xboole_0(k1_xboole_0, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_348, c_30])).
% 3.92/1.94  tff(c_395, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_348, c_30])).
% 3.92/1.94  tff(c_36, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.92/1.94  tff(c_408, plain, (![B_20]: (k4_xboole_0(B_20, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_20))), inference(superposition, [status(thm), theory('equality')], [c_395, c_36])).
% 3.92/1.94  tff(c_435, plain, (![B_20]: (k4_xboole_0(B_20, k1_xboole_0)=B_20)), inference(demodulation, [status(thm), theory('equality')], [c_364, c_408])).
% 3.92/1.94  tff(c_34, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.92/1.94  tff(c_194, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.92/1.94  tff(c_203, plain, (![A_57]: (k3_xboole_0(k1_xboole_0, A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_194])).
% 3.92/1.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.92/1.94  tff(c_208, plain, (![A_57]: (k3_xboole_0(A_57, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 3.92/1.94  tff(c_486, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.94  tff(c_495, plain, (![A_57]: (k5_xboole_0(A_57, k1_xboole_0)=k4_xboole_0(A_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_486])).
% 3.92/1.94  tff(c_510, plain, (![A_57]: (k5_xboole_0(A_57, k1_xboole_0)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_435, c_495])).
% 3.92/1.94  tff(c_201, plain, (![A_18]: (k3_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_194])).
% 3.92/1.94  tff(c_501, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_18))), inference(superposition, [status(thm), theory('equality')], [c_201, c_486])).
% 3.92/1.94  tff(c_551, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_510, c_501])).
% 3.92/1.94  tff(c_606, plain, (![A_93, B_94]: (k4_xboole_0(k2_xboole_0(A_93, B_94), B_94)=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.92/1.94  tff(c_626, plain, (![A_68]: (k4_xboole_0(k1_xboole_0, A_68)=k4_xboole_0(A_68, A_68))), inference(superposition, [status(thm), theory('equality')], [c_364, c_606])).
% 3.92/1.94  tff(c_647, plain, (![A_68]: (k4_xboole_0(A_68, A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_551, c_626])).
% 3.92/1.94  tff(c_26, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.92/1.94  tff(c_202, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_26, c_194])).
% 3.92/1.94  tff(c_498, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k4_xboole_0(B_12, B_12))), inference(superposition, [status(thm), theory('equality')], [c_202, c_486])).
% 3.92/1.94  tff(c_649, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_647, c_498])).
% 3.92/1.94  tff(c_44, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.92/1.94  tff(c_1241, plain, (![A_126, B_127, C_128]: (r1_tarski(k2_tarski(A_126, B_127), C_128) | ~r2_hidden(B_127, C_128) | ~r2_hidden(A_126, C_128))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.92/1.94  tff(c_2811, plain, (![A_175, C_176]: (r1_tarski(k1_tarski(A_175), C_176) | ~r2_hidden(A_175, C_176) | ~r2_hidden(A_175, C_176))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1241])).
% 3.92/1.94  tff(c_32, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.92/1.94  tff(c_2843, plain, (![A_178, C_179]: (k3_xboole_0(k1_tarski(A_178), C_179)=k1_tarski(A_178) | ~r2_hidden(A_178, C_179))), inference(resolution, [status(thm)], [c_2811, c_32])).
% 3.92/1.94  tff(c_28, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.94  tff(c_2852, plain, (![A_178, C_179]: (k5_xboole_0(k1_tarski(A_178), k1_tarski(A_178))=k4_xboole_0(k1_tarski(A_178), C_179) | ~r2_hidden(A_178, C_179))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_28])).
% 3.92/1.94  tff(c_2895, plain, (![A_180, C_181]: (k4_xboole_0(k1_tarski(A_180), C_181)=k1_xboole_0 | ~r2_hidden(A_180, C_181))), inference(demodulation, [status(thm), theory('equality')], [c_649, c_2852])).
% 3.92/1.94  tff(c_40, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.94  tff(c_2921, plain, (![C_181, A_180]: (k2_xboole_0(C_181, k1_tarski(A_180))=k5_xboole_0(C_181, k1_xboole_0) | ~r2_hidden(A_180, C_181))), inference(superposition, [status(thm), theory('equality')], [c_2895, c_40])).
% 3.92/1.94  tff(c_2989, plain, (![C_184, A_185]: (k2_xboole_0(C_184, k1_tarski(A_185))=C_184 | ~r2_hidden(A_185, C_184))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_2921])).
% 3.92/1.94  tff(c_327, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_321, c_52])).
% 3.92/1.94  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.92/1.94  tff(c_347, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_327, c_60])).
% 3.92/1.94  tff(c_3067, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2989, c_347])).
% 3.92/1.94  tff(c_3138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_3067])).
% 3.92/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.94  
% 3.92/1.94  Inference rules
% 3.92/1.94  ----------------------
% 3.92/1.94  #Ref     : 0
% 3.92/1.94  #Sup     : 744
% 3.92/1.94  #Fact    : 0
% 3.92/1.94  #Define  : 0
% 3.92/1.94  #Split   : 1
% 3.92/1.94  #Chain   : 0
% 3.92/1.94  #Close   : 0
% 3.92/1.94  
% 3.92/1.94  Ordering : KBO
% 3.92/1.94  
% 3.92/1.94  Simplification rules
% 3.92/1.94  ----------------------
% 3.92/1.94  #Subsume      : 60
% 3.92/1.94  #Demod        : 737
% 3.92/1.94  #Tautology    : 541
% 3.92/1.94  #SimpNegUnit  : 0
% 3.92/1.94  #BackRed      : 3
% 3.92/1.94  
% 3.92/1.94  #Partial instantiations: 0
% 3.92/1.94  #Strategies tried      : 1
% 3.92/1.94  
% 3.92/1.94  Timing (in seconds)
% 3.92/1.94  ----------------------
% 3.92/1.94  Preprocessing        : 0.41
% 3.92/1.94  Parsing              : 0.22
% 3.92/1.94  CNF conversion       : 0.02
% 3.92/1.94  Main loop            : 0.62
% 3.92/1.94  Inferencing          : 0.20
% 3.92/1.94  Reduction            : 0.27
% 3.92/1.94  Demodulation         : 0.23
% 3.92/1.94  BG Simplification    : 0.03
% 3.92/1.94  Subsumption          : 0.09
% 3.92/1.94  Abstraction          : 0.03
% 3.92/1.94  MUC search           : 0.00
% 3.92/1.94  Cooper               : 0.00
% 3.92/1.94  Total                : 1.08
% 3.92/1.94  Index Insertion      : 0.00
% 3.92/1.94  Index Deletion       : 0.00
% 3.92/1.94  Index Matching       : 0.00
% 3.92/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
