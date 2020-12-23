%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:58 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 143 expanded)
%              Number of leaves         :   30 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :   73 ( 148 expanded)
%              Number of equality atoms :   46 ( 112 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [A_40] : r1_tarski(k1_xboole_0,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_20])).

tff(c_232,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_250,plain,(
    ! [A_40] : k3_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_232])).

tff(c_822,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_39] : k2_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_533,plain,(
    ! [A_77,B_78] : k2_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_560,plain,(
    ! [B_78] : k4_xboole_0(B_78,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_91])).

tff(c_584,plain,(
    ! [B_78] : k4_xboole_0(B_78,k1_xboole_0) = B_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_560])).

tff(c_762,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_771,plain,(
    ! [B_78] : k5_xboole_0(k1_xboole_0,B_78) = k2_xboole_0(k1_xboole_0,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_762])).

tff(c_783,plain,(
    ! [B_78] : k5_xboole_0(k1_xboole_0,B_78) = B_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_771])).

tff(c_829,plain,(
    ! [B_89] : k4_xboole_0(k1_xboole_0,B_89) = k3_xboole_0(k1_xboole_0,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_783])).

tff(c_855,plain,(
    ! [B_90] : k4_xboole_0(k1_xboole_0,B_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_829])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_860,plain,(
    ! [B_90] : k5_xboole_0(B_90,k1_xboole_0) = k2_xboole_0(B_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_22])).

tff(c_879,plain,(
    ! [B_90] : k5_xboole_0(B_90,k1_xboole_0) = B_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_860])).

tff(c_850,plain,(
    ! [B_89] : k4_xboole_0(k1_xboole_0,B_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_829])).

tff(c_416,plain,(
    ! [A_65,B_66] : k4_xboole_0(k2_xboole_0(A_65,B_66),B_66) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_428,plain,(
    ! [A_39] : k4_xboole_0(k1_xboole_0,A_39) = k4_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_416])).

tff(c_854,plain,(
    ! [A_39] : k4_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_428])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_252,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_232])).

tff(c_848,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_822])).

tff(c_976,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_848])).

tff(c_24,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1008,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_tarski(k2_tarski(A_102,B_103),C_104)
      | ~ r2_hidden(B_103,C_104)
      | ~ r2_hidden(A_102,C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2258,plain,(
    ! [A_146,C_147] :
      ( r1_tarski(k1_tarski(A_146),C_147)
      | ~ r2_hidden(A_146,C_147)
      | ~ r2_hidden(A_146,C_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1008])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3884,plain,(
    ! [A_172,C_173] :
      ( k3_xboole_0(k1_tarski(A_172),C_173) = k1_tarski(A_172)
      | ~ r2_hidden(A_172,C_173) ) ),
    inference(resolution,[status(thm)],[c_2258,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3890,plain,(
    ! [A_172,C_173] :
      ( k5_xboole_0(k1_tarski(A_172),k1_tarski(A_172)) = k4_xboole_0(k1_tarski(A_172),C_173)
      | ~ r2_hidden(A_172,C_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3884,c_10])).

tff(c_3939,plain,(
    ! [A_174,C_175] :
      ( k4_xboole_0(k1_tarski(A_174),C_175) = k1_xboole_0
      | ~ r2_hidden(A_174,C_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_3890])).

tff(c_3978,plain,(
    ! [C_175,A_174] :
      ( k2_xboole_0(C_175,k1_tarski(A_174)) = k5_xboole_0(C_175,k1_xboole_0)
      | ~ r2_hidden(A_174,C_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3939,c_22])).

tff(c_4034,plain,(
    ! [C_176,A_177] :
      ( k2_xboole_0(C_176,k1_tarski(A_177)) = C_176
      | ~ r2_hidden(A_177,C_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_3978])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_4173,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4034,c_44])).

tff(c_4251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:13:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.80  
% 4.14/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.80  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.14/1.80  
% 4.14/1.80  %Foreground sorts:
% 4.14/1.80  
% 4.14/1.80  
% 4.14/1.80  %Background operators:
% 4.14/1.80  
% 4.14/1.80  
% 4.14/1.80  %Foreground operators:
% 4.14/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.14/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.14/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.14/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.14/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.14/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.14/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.14/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.14/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.14/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.14/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.14/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.14/1.80  
% 4.14/1.82  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.14/1.82  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.14/1.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.14/1.82  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.14/1.82  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.14/1.82  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.14/1.82  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.14/1.82  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.14/1.82  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.14/1.82  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.14/1.82  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.14/1.82  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.14/1.82  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.14/1.82  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.14/1.82  tff(c_69, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.14/1.82  tff(c_122, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_69, c_12])).
% 4.14/1.82  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.14/1.82  tff(c_134, plain, (![A_40]: (r1_tarski(k1_xboole_0, A_40))), inference(superposition, [status(thm), theory('equality')], [c_122, c_20])).
% 4.14/1.82  tff(c_232, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.14/1.82  tff(c_250, plain, (![A_40]: (k3_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_232])).
% 4.14/1.82  tff(c_822, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.14/1.82  tff(c_91, plain, (![A_39]: (k2_xboole_0(k1_xboole_0, A_39)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_69, c_12])).
% 4.14/1.82  tff(c_533, plain, (![A_77, B_78]: (k2_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.14/1.82  tff(c_560, plain, (![B_78]: (k4_xboole_0(B_78, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_78))), inference(superposition, [status(thm), theory('equality')], [c_533, c_91])).
% 4.14/1.82  tff(c_584, plain, (![B_78]: (k4_xboole_0(B_78, k1_xboole_0)=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_560])).
% 4.14/1.82  tff(c_762, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.82  tff(c_771, plain, (![B_78]: (k5_xboole_0(k1_xboole_0, B_78)=k2_xboole_0(k1_xboole_0, B_78))), inference(superposition, [status(thm), theory('equality')], [c_584, c_762])).
% 4.14/1.82  tff(c_783, plain, (![B_78]: (k5_xboole_0(k1_xboole_0, B_78)=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_771])).
% 4.14/1.82  tff(c_829, plain, (![B_89]: (k4_xboole_0(k1_xboole_0, B_89)=k3_xboole_0(k1_xboole_0, B_89))), inference(superposition, [status(thm), theory('equality')], [c_822, c_783])).
% 4.14/1.82  tff(c_855, plain, (![B_90]: (k4_xboole_0(k1_xboole_0, B_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_829])).
% 4.14/1.82  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.82  tff(c_860, plain, (![B_90]: (k5_xboole_0(B_90, k1_xboole_0)=k2_xboole_0(B_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_855, c_22])).
% 4.14/1.82  tff(c_879, plain, (![B_90]: (k5_xboole_0(B_90, k1_xboole_0)=B_90)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_860])).
% 4.14/1.82  tff(c_850, plain, (![B_89]: (k4_xboole_0(k1_xboole_0, B_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_829])).
% 4.14/1.82  tff(c_416, plain, (![A_65, B_66]: (k4_xboole_0(k2_xboole_0(A_65, B_66), B_66)=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.14/1.82  tff(c_428, plain, (![A_39]: (k4_xboole_0(k1_xboole_0, A_39)=k4_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_91, c_416])).
% 4.14/1.82  tff(c_854, plain, (![A_39]: (k4_xboole_0(A_39, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_850, c_428])).
% 4.14/1.82  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.14/1.82  tff(c_252, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_232])).
% 4.14/1.82  tff(c_848, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_252, c_822])).
% 4.14/1.82  tff(c_976, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_854, c_848])).
% 4.14/1.82  tff(c_24, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.14/1.82  tff(c_1008, plain, (![A_102, B_103, C_104]: (r1_tarski(k2_tarski(A_102, B_103), C_104) | ~r2_hidden(B_103, C_104) | ~r2_hidden(A_102, C_104))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.14/1.82  tff(c_2258, plain, (![A_146, C_147]: (r1_tarski(k1_tarski(A_146), C_147) | ~r2_hidden(A_146, C_147) | ~r2_hidden(A_146, C_147))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1008])).
% 4.14/1.82  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.14/1.82  tff(c_3884, plain, (![A_172, C_173]: (k3_xboole_0(k1_tarski(A_172), C_173)=k1_tarski(A_172) | ~r2_hidden(A_172, C_173))), inference(resolution, [status(thm)], [c_2258, c_14])).
% 4.14/1.82  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.14/1.82  tff(c_3890, plain, (![A_172, C_173]: (k5_xboole_0(k1_tarski(A_172), k1_tarski(A_172))=k4_xboole_0(k1_tarski(A_172), C_173) | ~r2_hidden(A_172, C_173))), inference(superposition, [status(thm), theory('equality')], [c_3884, c_10])).
% 4.14/1.82  tff(c_3939, plain, (![A_174, C_175]: (k4_xboole_0(k1_tarski(A_174), C_175)=k1_xboole_0 | ~r2_hidden(A_174, C_175))), inference(demodulation, [status(thm), theory('equality')], [c_976, c_3890])).
% 4.14/1.82  tff(c_3978, plain, (![C_175, A_174]: (k2_xboole_0(C_175, k1_tarski(A_174))=k5_xboole_0(C_175, k1_xboole_0) | ~r2_hidden(A_174, C_175))), inference(superposition, [status(thm), theory('equality')], [c_3939, c_22])).
% 4.14/1.82  tff(c_4034, plain, (![C_176, A_177]: (k2_xboole_0(C_176, k1_tarski(A_177))=C_176 | ~r2_hidden(A_177, C_176))), inference(demodulation, [status(thm), theory('equality')], [c_879, c_3978])).
% 4.14/1.82  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.14/1.82  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.14/1.82  tff(c_44, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 4.14/1.82  tff(c_4173, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4034, c_44])).
% 4.14/1.82  tff(c_4251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_4173])).
% 4.14/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.82  
% 4.14/1.82  Inference rules
% 4.14/1.82  ----------------------
% 4.14/1.82  #Ref     : 0
% 4.14/1.82  #Sup     : 986
% 4.14/1.82  #Fact    : 0
% 4.14/1.82  #Define  : 0
% 4.14/1.82  #Split   : 0
% 4.14/1.82  #Chain   : 0
% 4.14/1.82  #Close   : 0
% 4.14/1.82  
% 4.14/1.82  Ordering : KBO
% 4.14/1.82  
% 4.14/1.82  Simplification rules
% 4.14/1.82  ----------------------
% 4.14/1.82  #Subsume      : 66
% 4.14/1.82  #Demod        : 1195
% 4.14/1.82  #Tautology    : 754
% 4.14/1.82  #SimpNegUnit  : 0
% 4.14/1.82  #BackRed      : 6
% 4.14/1.82  
% 4.14/1.82  #Partial instantiations: 0
% 4.14/1.82  #Strategies tried      : 1
% 4.14/1.82  
% 4.14/1.82  Timing (in seconds)
% 4.14/1.82  ----------------------
% 4.14/1.82  Preprocessing        : 0.31
% 4.14/1.82  Parsing              : 0.17
% 4.14/1.82  CNF conversion       : 0.02
% 4.14/1.82  Main loop            : 0.71
% 4.14/1.82  Inferencing          : 0.22
% 4.14/1.82  Reduction            : 0.34
% 4.14/1.82  Demodulation         : 0.29
% 4.14/1.82  BG Simplification    : 0.02
% 4.14/1.82  Subsumption          : 0.09
% 4.14/1.82  Abstraction          : 0.04
% 4.14/1.82  MUC search           : 0.00
% 4.14/1.82  Cooper               : 0.00
% 4.14/1.82  Total                : 1.04
% 4.14/1.82  Index Insertion      : 0.00
% 4.14/1.82  Index Deletion       : 0.00
% 4.14/1.82  Index Matching       : 0.00
% 4.14/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
