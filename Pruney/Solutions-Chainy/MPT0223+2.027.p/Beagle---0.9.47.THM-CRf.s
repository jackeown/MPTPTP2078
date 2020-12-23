%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:20 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 105 expanded)
%              Number of leaves         :   43 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 (  96 expanded)
%              Number of equality atoms :   54 (  78 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_91,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_89,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_78,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_68,plain,(
    ! [A_45,B_46,C_47] : k2_enumset1(A_45,A_45,B_46,C_47) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2133,plain,(
    ! [A_184,B_185,C_186,D_187] : k2_xboole_0(k1_enumset1(A_184,B_185,C_186),k1_tarski(D_187)) = k2_enumset1(A_184,B_185,C_186,D_187) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2177,plain,(
    ! [A_43,B_44,D_187] : k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(D_187)) = k2_enumset1(A_43,A_43,B_44,D_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2133])).

tff(c_4046,plain,(
    ! [A_314,B_315,D_316] : k2_xboole_0(k2_tarski(A_314,B_315),k1_tarski(D_316)) = k1_enumset1(A_314,B_315,D_316) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2177])).

tff(c_4090,plain,(
    ! [A_42,D_316] : k2_xboole_0(k1_tarski(A_42),k1_tarski(D_316)) = k1_enumset1(A_42,A_42,D_316) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4046])).

tff(c_4107,plain,(
    ! [A_317,D_318] : k2_xboole_0(k1_tarski(A_317),k1_tarski(D_318)) = k2_tarski(A_317,D_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4090])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_235,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_256,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_259,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_256])).

tff(c_80,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_253,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_235])).

tff(c_420,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_253])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_434,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,k3_xboole_0(A_112,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_464,plain,(
    ! [A_118,B_119] :
      ( ~ r1_xboole_0(A_118,B_119)
      | k3_xboole_0(A_118,B_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_434])).

tff(c_539,plain,(
    ! [A_123,B_124] : k3_xboole_0(k4_xboole_0(A_123,B_124),B_124) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_464])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_647,plain,(
    ! [B_129,A_130] : k3_xboole_0(B_129,k4_xboole_0(A_130,B_129)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_2])).

tff(c_669,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_647])).

tff(c_748,plain,(
    ! [A_135,B_136] : k5_xboole_0(k5_xboole_0(A_135,B_136),k3_xboole_0(A_135,B_136)) = k2_xboole_0(A_135,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_763,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_748])).

tff(c_804,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_763])).

tff(c_14,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_424,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k2_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_14])).

tff(c_2512,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_424])).

tff(c_4126,plain,(
    k2_tarski('#skF_8','#skF_7') = k1_tarski('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4107,c_2512])).

tff(c_185,plain,(
    ! [A_95,B_96] : k1_enumset1(A_95,A_95,B_96) = k2_tarski(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [E_29,A_23,B_24] : r2_hidden(E_29,k1_enumset1(A_23,B_24,E_29)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_197,plain,(
    ! [B_96,A_95] : r2_hidden(B_96,k2_tarski(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_26])).

tff(c_4204,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4126,c_197])).

tff(c_48,plain,(
    ! [C_34,A_30] :
      ( C_34 = A_30
      | ~ r2_hidden(C_34,k1_tarski(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4224,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4204,c_48])).

tff(c_4228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.08  
% 5.19/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.09  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 5.19/2.09  
% 5.19/2.09  %Foreground sorts:
% 5.19/2.09  
% 5.19/2.09  
% 5.19/2.09  %Background operators:
% 5.19/2.09  
% 5.19/2.09  
% 5.19/2.09  %Foreground operators:
% 5.19/2.09  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.19/2.09  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.19/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.19/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.19/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.19/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.19/2.09  tff('#skF_7', type, '#skF_7': $i).
% 5.19/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.19/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.19/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.19/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.19/2.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.19/2.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.09  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.19/2.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.09  tff('#skF_8', type, '#skF_8': $i).
% 5.19/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.19/2.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.19/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.19/2.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.19/2.09  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.19/2.09  
% 5.27/2.10  tff(f_108, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 5.27/2.10  tff(f_93, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.27/2.10  tff(f_91, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.27/2.10  tff(f_95, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.27/2.10  tff(f_89, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.27/2.10  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.27/2.10  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.27/2.10  tff(f_53, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.27/2.10  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.27/2.10  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.27/2.10  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.27/2.10  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.27/2.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.27/2.10  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.27/2.10  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.27/2.10  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.27/2.10  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.27/2.10  tff(c_78, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.27/2.10  tff(c_66, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.27/2.10  tff(c_64, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.27/2.10  tff(c_68, plain, (![A_45, B_46, C_47]: (k2_enumset1(A_45, A_45, B_46, C_47)=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.27/2.10  tff(c_2133, plain, (![A_184, B_185, C_186, D_187]: (k2_xboole_0(k1_enumset1(A_184, B_185, C_186), k1_tarski(D_187))=k2_enumset1(A_184, B_185, C_186, D_187))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.27/2.10  tff(c_2177, plain, (![A_43, B_44, D_187]: (k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(D_187))=k2_enumset1(A_43, A_43, B_44, D_187))), inference(superposition, [status(thm), theory('equality')], [c_66, c_2133])).
% 5.27/2.10  tff(c_4046, plain, (![A_314, B_315, D_316]: (k2_xboole_0(k2_tarski(A_314, B_315), k1_tarski(D_316))=k1_enumset1(A_314, B_315, D_316))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2177])).
% 5.27/2.10  tff(c_4090, plain, (![A_42, D_316]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(D_316))=k1_enumset1(A_42, A_42, D_316))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4046])).
% 5.27/2.10  tff(c_4107, plain, (![A_317, D_318]: (k2_xboole_0(k1_tarski(A_317), k1_tarski(D_318))=k2_tarski(A_317, D_318))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4090])).
% 5.27/2.10  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.27/2.10  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.27/2.10  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.27/2.10  tff(c_235, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.27/2.10  tff(c_256, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k5_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_235])).
% 5.27/2.10  tff(c_259, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_256])).
% 5.27/2.10  tff(c_80, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.27/2.10  tff(c_253, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_235])).
% 5.27/2.10  tff(c_420, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_259, c_253])).
% 5.27/2.10  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.27/2.10  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.27/2.10  tff(c_434, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, k3_xboole_0(A_112, B_113)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.27/2.10  tff(c_464, plain, (![A_118, B_119]: (~r1_xboole_0(A_118, B_119) | k3_xboole_0(A_118, B_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_434])).
% 5.27/2.10  tff(c_539, plain, (![A_123, B_124]: (k3_xboole_0(k4_xboole_0(A_123, B_124), B_124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_464])).
% 5.27/2.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.27/2.10  tff(c_647, plain, (![B_129, A_130]: (k3_xboole_0(B_129, k4_xboole_0(A_130, B_129))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_539, c_2])).
% 5.27/2.10  tff(c_669, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_420, c_647])).
% 5.27/2.10  tff(c_748, plain, (![A_135, B_136]: (k5_xboole_0(k5_xboole_0(A_135, B_136), k3_xboole_0(A_135, B_136))=k2_xboole_0(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.27/2.10  tff(c_763, plain, (k5_xboole_0(k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_669, c_748])).
% 5.27/2.10  tff(c_804, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_763])).
% 5.27/2.10  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.27/2.10  tff(c_424, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k2_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_420, c_14])).
% 5.27/2.10  tff(c_2512, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_804, c_424])).
% 5.27/2.10  tff(c_4126, plain, (k2_tarski('#skF_8', '#skF_7')=k1_tarski('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4107, c_2512])).
% 5.27/2.10  tff(c_185, plain, (![A_95, B_96]: (k1_enumset1(A_95, A_95, B_96)=k2_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.27/2.10  tff(c_26, plain, (![E_29, A_23, B_24]: (r2_hidden(E_29, k1_enumset1(A_23, B_24, E_29)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.27/2.10  tff(c_197, plain, (![B_96, A_95]: (r2_hidden(B_96, k2_tarski(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_26])).
% 5.27/2.10  tff(c_4204, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4126, c_197])).
% 5.27/2.10  tff(c_48, plain, (![C_34, A_30]: (C_34=A_30 | ~r2_hidden(C_34, k1_tarski(A_30)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.27/2.10  tff(c_4224, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_4204, c_48])).
% 5.27/2.10  tff(c_4228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4224])).
% 5.27/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/2.10  
% 5.27/2.10  Inference rules
% 5.27/2.10  ----------------------
% 5.27/2.10  #Ref     : 0
% 5.27/2.10  #Sup     : 1059
% 5.27/2.10  #Fact    : 0
% 5.27/2.10  #Define  : 0
% 5.27/2.10  #Split   : 3
% 5.27/2.10  #Chain   : 0
% 5.27/2.10  #Close   : 0
% 5.27/2.10  
% 5.27/2.10  Ordering : KBO
% 5.27/2.10  
% 5.27/2.10  Simplification rules
% 5.27/2.10  ----------------------
% 5.27/2.10  #Subsume      : 72
% 5.27/2.10  #Demod        : 867
% 5.27/2.10  #Tautology    : 778
% 5.27/2.10  #SimpNegUnit  : 36
% 5.27/2.10  #BackRed      : 5
% 5.27/2.10  
% 5.27/2.10  #Partial instantiations: 0
% 5.27/2.10  #Strategies tried      : 1
% 5.27/2.10  
% 5.27/2.10  Timing (in seconds)
% 5.27/2.10  ----------------------
% 5.27/2.10  Preprocessing        : 0.42
% 5.27/2.10  Parsing              : 0.20
% 5.27/2.10  CNF conversion       : 0.04
% 5.27/2.10  Main loop            : 0.89
% 5.27/2.10  Inferencing          : 0.28
% 5.27/2.10  Reduction            : 0.37
% 5.27/2.10  Demodulation         : 0.29
% 5.27/2.10  BG Simplification    : 0.04
% 5.27/2.10  Subsumption          : 0.14
% 5.27/2.10  Abstraction          : 0.04
% 5.27/2.10  MUC search           : 0.00
% 5.27/2.10  Cooper               : 0.00
% 5.27/2.10  Total                : 1.34
% 5.27/2.10  Index Insertion      : 0.00
% 5.27/2.10  Index Deletion       : 0.00
% 5.27/2.10  Index Matching       : 0.00
% 5.27/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
