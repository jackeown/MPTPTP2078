%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:47 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 133 expanded)
%              Number of leaves         :   41 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 177 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_67,axiom,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_93,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_76,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | r2_hidden('#skF_1'(A_7),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [B_6,A_5] : k3_xboole_0(B_6,A_5) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    ! [A_29] : r1_tarski(k1_xboole_0,A_29) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_234,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_245,plain,(
    ! [A_67] : k3_xboole_0(k1_xboole_0,A_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_234])).

tff(c_259,plain,(
    ! [B_6] : k3_xboole_0(B_6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_245])).

tff(c_444,plain,(
    ! [D_92,A_93,B_94] :
      ( r2_hidden(D_92,A_93)
      | ~ r2_hidden(D_92,k3_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_536,plain,(
    ! [D_98,B_99] :
      ( r2_hidden(D_98,B_99)
      | ~ r2_hidden(D_98,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_444])).

tff(c_544,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_1'(k1_xboole_0),B_99)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_536])).

tff(c_766,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_359,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_4'(A_79,B_80),A_79)
      | r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [B_10,A_7] :
      ( ~ r2_hidden(B_10,A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_367,plain,(
    ! [A_81,B_82] :
      ( ~ v1_xboole_0(A_81)
      | r1_xboole_0(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_359,c_8])).

tff(c_54,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = A_34
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_371,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = A_81
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_367,c_54])).

tff(c_791,plain,(
    ! [B_82] : k4_xboole_0(k1_xboole_0,B_82) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_766,c_371])).

tff(c_149,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_44])).

tff(c_470,plain,(
    ! [A_95,B_96] : k4_xboole_0(k2_xboole_0(A_95,B_96),B_96) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_496,plain,(
    ! [A_63] : k4_xboole_0(k1_xboole_0,A_63) = k4_xboole_0(A_63,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_470])).

tff(c_793,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_496])).

tff(c_40,plain,(
    ! [B_23] : r1_tarski(B_23,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_242,plain,(
    ! [B_23] : k3_xboole_0(B_23,B_23) = B_23 ),
    inference(resolution,[status(thm)],[c_40,c_234])).

tff(c_862,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = k4_xboole_0(A_134,B_135) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_874,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k4_xboole_0(B_23,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_862])).

tff(c_887,plain,(
    ! [B_23] : k5_xboole_0(B_23,B_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_874])).

tff(c_58,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1338,plain,(
    ! [A_169,B_170,C_171] :
      ( r1_tarski(k2_tarski(A_169,B_170),C_171)
      | ~ r2_hidden(B_170,C_171)
      | ~ r2_hidden(A_169,C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3184,plain,(
    ! [A_248,C_249] :
      ( r1_tarski(k1_tarski(A_248),C_249)
      | ~ r2_hidden(A_248,C_249)
      | ~ r2_hidden(A_248,C_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1338])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3371,plain,(
    ! [A_254,C_255] :
      ( k3_xboole_0(k1_tarski(A_254),C_255) = k1_tarski(A_254)
      | ~ r2_hidden(A_254,C_255) ) ),
    inference(resolution,[status(thm)],[c_3184,c_46])).

tff(c_42,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3391,plain,(
    ! [A_254,C_255] :
      ( k5_xboole_0(k1_tarski(A_254),k1_tarski(A_254)) = k4_xboole_0(k1_tarski(A_254),C_255)
      | ~ r2_hidden(A_254,C_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3371,c_42])).

tff(c_3442,plain,(
    ! [A_256,C_257] :
      ( k4_xboole_0(k1_tarski(A_256),C_257) = k1_xboole_0
      | ~ r2_hidden(A_256,C_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_3391])).

tff(c_50,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3487,plain,(
    ! [C_257,A_256] :
      ( k2_xboole_0(C_257,k1_tarski(A_256)) = k2_xboole_0(C_257,k1_xboole_0)
      | ~ r2_hidden(A_256,C_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3442,c_50])).

tff(c_4317,plain,(
    ! [C_302,A_303] :
      ( k2_xboole_0(C_302,k1_tarski(A_303)) = C_302
      | ~ r2_hidden(A_303,C_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3487])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_78,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_4405,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4317,c_78])).

tff(c_4467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4405])).

tff(c_4492,plain,(
    ! [B_306] : r2_hidden('#skF_1'(k1_xboole_0),B_306) ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_4521,plain,(
    ! [B_306] : ~ v1_xboole_0(B_306) ),
    inference(resolution,[status(thm)],[c_4492,c_8])).

tff(c_109,plain,(
    ! [B_58,A_59] :
      ( ~ r2_hidden(B_58,A_59)
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_114,plain,(
    ! [A_7] :
      ( ~ r2_hidden(A_7,'#skF_1'(A_7))
      | v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_4519,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4492,c_114])).

tff(c_4525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4521,c_4519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.93/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.93/2.02  
% 4.93/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.93/2.03  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.93/2.03  
% 4.93/2.03  %Foreground sorts:
% 4.93/2.03  
% 4.93/2.03  
% 4.93/2.03  %Background operators:
% 4.93/2.03  
% 4.93/2.03  
% 4.93/2.03  %Foreground operators:
% 4.93/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.93/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.93/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.93/2.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.93/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.93/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.93/2.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.93/2.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.93/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.93/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.93/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.93/2.03  tff('#skF_5', type, '#skF_5': $i).
% 4.93/2.03  tff('#skF_6', type, '#skF_6': $i).
% 4.93/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.93/2.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.93/2.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.93/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.93/2.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.93/2.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.93/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.93/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.93/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.93/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.93/2.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.93/2.03  
% 4.93/2.04  tff(f_112, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.93/2.04  tff(f_77, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.93/2.04  tff(f_40, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.93/2.04  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.93/2.04  tff(f_83, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.93/2.04  tff(f_81, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.93/2.04  tff(f_49, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.93/2.04  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.93/2.04  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.93/2.04  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.93/2.04  tff(f_87, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.93/2.04  tff(f_73, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.93/2.04  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.93/2.04  tff(f_93, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.93/2.04  tff(f_107, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.93/2.04  tff(f_85, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.93/2.04  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 4.93/2.04  tff(c_76, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.93/2.04  tff(c_44, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.93/2.04  tff(c_10, plain, (![A_7]: (v1_xboole_0(A_7) | r2_hidden('#skF_1'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.04  tff(c_6, plain, (![B_6, A_5]: (k3_xboole_0(B_6, A_5)=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.93/2.04  tff(c_48, plain, (![A_29]: (r1_tarski(k1_xboole_0, A_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.93/2.04  tff(c_234, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.93/2.04  tff(c_245, plain, (![A_67]: (k3_xboole_0(k1_xboole_0, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_234])).
% 4.93/2.04  tff(c_259, plain, (![B_6]: (k3_xboole_0(B_6, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_245])).
% 4.93/2.04  tff(c_444, plain, (![D_92, A_93, B_94]: (r2_hidden(D_92, A_93) | ~r2_hidden(D_92, k3_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.93/2.04  tff(c_536, plain, (![D_98, B_99]: (r2_hidden(D_98, B_99) | ~r2_hidden(D_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_259, c_444])).
% 4.93/2.04  tff(c_544, plain, (![B_99]: (r2_hidden('#skF_1'(k1_xboole_0), B_99) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_536])).
% 4.93/2.04  tff(c_766, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_544])).
% 4.93/2.04  tff(c_359, plain, (![A_79, B_80]: (r2_hidden('#skF_4'(A_79, B_80), A_79) | r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.93/2.04  tff(c_8, plain, (![B_10, A_7]: (~r2_hidden(B_10, A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.93/2.04  tff(c_367, plain, (![A_81, B_82]: (~v1_xboole_0(A_81) | r1_xboole_0(A_81, B_82))), inference(resolution, [status(thm)], [c_359, c_8])).
% 4.93/2.04  tff(c_54, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=A_34 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.93/2.04  tff(c_371, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=A_81 | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_367, c_54])).
% 4.93/2.04  tff(c_791, plain, (![B_82]: (k4_xboole_0(k1_xboole_0, B_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_766, c_371])).
% 4.93/2.04  tff(c_149, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.93/2.04  tff(c_165, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_149, c_44])).
% 4.93/2.04  tff(c_470, plain, (![A_95, B_96]: (k4_xboole_0(k2_xboole_0(A_95, B_96), B_96)=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.93/2.04  tff(c_496, plain, (![A_63]: (k4_xboole_0(k1_xboole_0, A_63)=k4_xboole_0(A_63, A_63))), inference(superposition, [status(thm), theory('equality')], [c_165, c_470])).
% 4.93/2.04  tff(c_793, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_791, c_496])).
% 4.93/2.04  tff(c_40, plain, (![B_23]: (r1_tarski(B_23, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.93/2.04  tff(c_242, plain, (![B_23]: (k3_xboole_0(B_23, B_23)=B_23)), inference(resolution, [status(thm)], [c_40, c_234])).
% 4.93/2.04  tff(c_862, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k3_xboole_0(A_134, B_135))=k4_xboole_0(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.93/2.04  tff(c_874, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k4_xboole_0(B_23, B_23))), inference(superposition, [status(thm), theory('equality')], [c_242, c_862])).
% 4.93/2.04  tff(c_887, plain, (![B_23]: (k5_xboole_0(B_23, B_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_793, c_874])).
% 4.93/2.04  tff(c_58, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.93/2.04  tff(c_1338, plain, (![A_169, B_170, C_171]: (r1_tarski(k2_tarski(A_169, B_170), C_171) | ~r2_hidden(B_170, C_171) | ~r2_hidden(A_169, C_171))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.93/2.04  tff(c_3184, plain, (![A_248, C_249]: (r1_tarski(k1_tarski(A_248), C_249) | ~r2_hidden(A_248, C_249) | ~r2_hidden(A_248, C_249))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1338])).
% 4.93/2.04  tff(c_46, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.93/2.04  tff(c_3371, plain, (![A_254, C_255]: (k3_xboole_0(k1_tarski(A_254), C_255)=k1_tarski(A_254) | ~r2_hidden(A_254, C_255))), inference(resolution, [status(thm)], [c_3184, c_46])).
% 4.93/2.04  tff(c_42, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.93/2.04  tff(c_3391, plain, (![A_254, C_255]: (k5_xboole_0(k1_tarski(A_254), k1_tarski(A_254))=k4_xboole_0(k1_tarski(A_254), C_255) | ~r2_hidden(A_254, C_255))), inference(superposition, [status(thm), theory('equality')], [c_3371, c_42])).
% 4.93/2.04  tff(c_3442, plain, (![A_256, C_257]: (k4_xboole_0(k1_tarski(A_256), C_257)=k1_xboole_0 | ~r2_hidden(A_256, C_257))), inference(demodulation, [status(thm), theory('equality')], [c_887, c_3391])).
% 4.93/2.04  tff(c_50, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.93/2.04  tff(c_3487, plain, (![C_257, A_256]: (k2_xboole_0(C_257, k1_tarski(A_256))=k2_xboole_0(C_257, k1_xboole_0) | ~r2_hidden(A_256, C_257))), inference(superposition, [status(thm), theory('equality')], [c_3442, c_50])).
% 4.93/2.04  tff(c_4317, plain, (![C_302, A_303]: (k2_xboole_0(C_302, k1_tarski(A_303))=C_302 | ~r2_hidden(A_303, C_302))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3487])).
% 4.93/2.04  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.93/2.04  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.93/2.04  tff(c_78, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_74])).
% 4.93/2.04  tff(c_4405, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4317, c_78])).
% 4.93/2.04  tff(c_4467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_4405])).
% 4.93/2.04  tff(c_4492, plain, (![B_306]: (r2_hidden('#skF_1'(k1_xboole_0), B_306))), inference(splitRight, [status(thm)], [c_544])).
% 4.93/2.04  tff(c_4521, plain, (![B_306]: (~v1_xboole_0(B_306))), inference(resolution, [status(thm)], [c_4492, c_8])).
% 4.93/2.04  tff(c_109, plain, (![B_58, A_59]: (~r2_hidden(B_58, A_59) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.93/2.04  tff(c_114, plain, (![A_7]: (~r2_hidden(A_7, '#skF_1'(A_7)) | v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_10, c_109])).
% 4.93/2.04  tff(c_4519, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_4492, c_114])).
% 4.93/2.04  tff(c_4525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4521, c_4519])).
% 4.93/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.93/2.04  
% 4.93/2.04  Inference rules
% 4.93/2.04  ----------------------
% 4.93/2.04  #Ref     : 0
% 4.93/2.04  #Sup     : 1050
% 4.93/2.04  #Fact    : 0
% 4.93/2.04  #Define  : 0
% 4.93/2.04  #Split   : 3
% 4.93/2.04  #Chain   : 0
% 4.93/2.04  #Close   : 0
% 4.93/2.04  
% 4.93/2.04  Ordering : KBO
% 4.93/2.04  
% 4.93/2.04  Simplification rules
% 4.93/2.04  ----------------------
% 4.93/2.04  #Subsume      : 187
% 4.93/2.04  #Demod        : 818
% 4.93/2.04  #Tautology    : 605
% 4.93/2.04  #SimpNegUnit  : 25
% 4.93/2.04  #BackRed      : 12
% 4.93/2.04  
% 4.93/2.04  #Partial instantiations: 0
% 4.93/2.04  #Strategies tried      : 1
% 4.93/2.04  
% 4.93/2.04  Timing (in seconds)
% 4.93/2.04  ----------------------
% 4.93/2.04  Preprocessing        : 0.32
% 4.93/2.04  Parsing              : 0.17
% 4.93/2.04  CNF conversion       : 0.02
% 4.93/2.04  Main loop            : 0.88
% 4.93/2.04  Inferencing          : 0.29
% 4.93/2.04  Reduction            : 0.35
% 4.93/2.04  Demodulation         : 0.27
% 4.93/2.04  BG Simplification    : 0.03
% 4.93/2.04  Subsumption          : 0.15
% 4.93/2.04  Abstraction          : 0.04
% 4.93/2.04  MUC search           : 0.00
% 4.93/2.05  Cooper               : 0.00
% 4.93/2.05  Total                : 1.23
% 4.93/2.05  Index Insertion      : 0.00
% 4.93/2.05  Index Deletion       : 0.00
% 4.93/2.05  Index Matching       : 0.00
% 4.93/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
