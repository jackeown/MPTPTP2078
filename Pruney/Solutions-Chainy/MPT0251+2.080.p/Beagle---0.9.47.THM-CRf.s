%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:57 EST 2020

% Result     : Theorem 8.18s
% Output     : CNFRefutation 8.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 163 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 232 expanded)
%              Number of equality atoms :   48 ( 125 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_70,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_109,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_44])).

tff(c_346,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_356,plain,(
    ! [B_81] : k4_xboole_0(B_81,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_109])).

tff(c_374,plain,(
    ! [B_81] : k4_xboole_0(B_81,k1_xboole_0) = B_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_356])).

tff(c_1916,plain,(
    ! [A_152,B_153,C_154] :
      ( r2_hidden('#skF_1'(A_152,B_153,C_154),B_153)
      | r2_hidden('#skF_2'(A_152,B_153,C_154),C_154)
      | k3_xboole_0(A_152,B_153) = C_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1953,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_2'(A_152,B_153,B_153),B_153)
      | k3_xboole_0(A_152,B_153) = B_153 ) ),
    inference(resolution,[status(thm)],[c_1916,c_16])).

tff(c_40,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_178,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_182,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_40,c_178])).

tff(c_260,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_269,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_260])).

tff(c_1045,plain,(
    ! [A_123,C_124,B_125] :
      ( ~ r2_hidden(A_123,C_124)
      | ~ r2_hidden(A_123,B_125)
      | ~ r2_hidden(A_123,k5_xboole_0(B_125,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4738,plain,(
    ! [A_204,B_205] :
      ( ~ r2_hidden(A_204,B_205)
      | ~ r2_hidden(A_204,B_205)
      | ~ r2_hidden(A_204,k4_xboole_0(B_205,B_205)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_1045])).

tff(c_4797,plain,(
    ! [A_206] :
      ( ~ r2_hidden(A_206,k1_xboole_0)
      | ~ r2_hidden(A_206,k1_xboole_0)
      | ~ r2_hidden(A_206,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_4738])).

tff(c_4862,plain,(
    ! [A_208] :
      ( ~ r2_hidden('#skF_2'(A_208,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(A_208,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1953,c_4797])).

tff(c_4879,plain,(
    ! [A_209] : k3_xboole_0(A_209,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1953,c_4862])).

tff(c_42,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4904,plain,(
    ! [A_209] : k5_xboole_0(A_209,k1_xboole_0) = k4_xboole_0(A_209,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4879,c_42])).

tff(c_4929,plain,(
    ! [A_209] : k5_xboole_0(A_209,k1_xboole_0) = A_209 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_4904])).

tff(c_1845,plain,(
    ! [A_147,B_148,C_149] :
      ( r2_hidden('#skF_1'(A_147,B_148,C_149),A_147)
      | r2_hidden('#skF_2'(A_147,B_148,C_149),C_149)
      | k3_xboole_0(A_147,B_148) = C_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1882,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148,A_147),A_147)
      | k3_xboole_0(A_147,B_148) = A_147 ) ),
    inference(resolution,[status(thm)],[c_1845,c_16])).

tff(c_5134,plain,(
    ! [B_220] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_220,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k1_xboole_0,B_220) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1882,c_4797])).

tff(c_5151,plain,(
    ! [B_221] : k3_xboole_0(k1_xboole_0,B_221) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1882,c_5134])).

tff(c_5171,plain,(
    ! [B_221] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_5151,c_42])).

tff(c_5192,plain,(
    ! [B_221] : k4_xboole_0(k1_xboole_0,B_221) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_5171])).

tff(c_304,plain,(
    ! [A_77,B_78] : k4_xboole_0(k2_xboole_0(A_77,B_78),B_78) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_316,plain,(
    ! [A_45] : k4_xboole_0(k1_xboole_0,A_45) = k4_xboole_0(A_45,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_304])).

tff(c_52,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_957,plain,(
    ! [A_114,B_115,C_116] :
      ( r1_tarski(k2_tarski(A_114,B_115),C_116)
      | ~ r2_hidden(B_115,C_116)
      | ~ r2_hidden(A_114,C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_991,plain,(
    ! [A_119,C_120] :
      ( r1_tarski(k1_tarski(A_119),C_120)
      | ~ r2_hidden(A_119,C_120)
      | ~ r2_hidden(A_119,C_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_957])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1003,plain,(
    ! [A_121,C_122] :
      ( k3_xboole_0(k1_tarski(A_121),C_122) = k1_tarski(A_121)
      | ~ r2_hidden(A_121,C_122) ) ),
    inference(resolution,[status(thm)],[c_991,c_46])).

tff(c_1021,plain,(
    ! [A_121,C_122] :
      ( k5_xboole_0(k1_tarski(A_121),k1_tarski(A_121)) = k4_xboole_0(k1_tarski(A_121),C_122)
      | ~ r2_hidden(A_121,C_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1003,c_42])).

tff(c_1037,plain,(
    ! [A_121,C_122] :
      ( k4_xboole_0(k1_tarski(A_121),C_122) = k4_xboole_0(k1_xboole_0,k1_tarski(A_121))
      | ~ r2_hidden(A_121,C_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_269,c_1021])).

tff(c_10401,plain,(
    ! [A_306,C_307] :
      ( k4_xboole_0(k1_tarski(A_306),C_307) = k1_xboole_0
      | ~ r2_hidden(A_306,C_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5192,c_1037])).

tff(c_48,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10476,plain,(
    ! [C_307,A_306] :
      ( k2_xboole_0(C_307,k1_tarski(A_306)) = k2_xboole_0(C_307,k1_xboole_0)
      | ~ r2_hidden(A_306,C_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10401,c_48])).

tff(c_10523,plain,(
    ! [C_308,A_309] :
      ( k2_xboole_0(C_308,k1_tarski(A_309)) = C_308
      | ~ r2_hidden(A_309,C_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10476])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_72,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_10653,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10523,c_72])).

tff(c_10724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:55:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.18/2.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.88  
% 8.18/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.88  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 8.18/2.88  
% 8.18/2.88  %Foreground sorts:
% 8.18/2.88  
% 8.18/2.88  
% 8.18/2.88  %Background operators:
% 8.18/2.88  
% 8.18/2.88  
% 8.18/2.88  %Foreground operators:
% 8.18/2.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.18/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.18/2.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.18/2.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.18/2.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.18/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.18/2.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.18/2.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.18/2.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.18/2.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.18/2.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.18/2.88  tff('#skF_5', type, '#skF_5': $i).
% 8.18/2.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.18/2.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.18/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.18/2.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.18/2.88  tff('#skF_4', type, '#skF_4': $i).
% 8.18/2.88  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.18/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.18/2.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.18/2.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.18/2.88  
% 8.54/2.89  tff(f_90, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.54/2.89  tff(f_61, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.54/2.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.54/2.89  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.54/2.89  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.54/2.89  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.54/2.89  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.54/2.89  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.54/2.89  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.54/2.89  tff(f_69, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.54/2.89  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.54/2.89  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.54/2.89  tff(c_70, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.54/2.89  tff(c_44, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.54/2.89  tff(c_93, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.54/2.89  tff(c_109, plain, (![A_45]: (k2_xboole_0(k1_xboole_0, A_45)=A_45)), inference(superposition, [status(thm), theory('equality')], [c_93, c_44])).
% 8.54/2.89  tff(c_346, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.54/2.89  tff(c_356, plain, (![B_81]: (k4_xboole_0(B_81, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_81))), inference(superposition, [status(thm), theory('equality')], [c_346, c_109])).
% 8.54/2.89  tff(c_374, plain, (![B_81]: (k4_xboole_0(B_81, k1_xboole_0)=B_81)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_356])).
% 8.54/2.89  tff(c_1916, plain, (![A_152, B_153, C_154]: (r2_hidden('#skF_1'(A_152, B_153, C_154), B_153) | r2_hidden('#skF_2'(A_152, B_153, C_154), C_154) | k3_xboole_0(A_152, B_153)=C_154)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.54/2.89  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.54/2.89  tff(c_1953, plain, (![A_152, B_153]: (r2_hidden('#skF_2'(A_152, B_153, B_153), B_153) | k3_xboole_0(A_152, B_153)=B_153)), inference(resolution, [status(thm)], [c_1916, c_16])).
% 8.54/2.89  tff(c_40, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.54/2.89  tff(c_178, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.54/2.89  tff(c_182, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_40, c_178])).
% 8.54/2.89  tff(c_260, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.54/2.89  tff(c_269, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_182, c_260])).
% 8.54/2.89  tff(c_1045, plain, (![A_123, C_124, B_125]: (~r2_hidden(A_123, C_124) | ~r2_hidden(A_123, B_125) | ~r2_hidden(A_123, k5_xboole_0(B_125, C_124)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.54/2.89  tff(c_4738, plain, (![A_204, B_205]: (~r2_hidden(A_204, B_205) | ~r2_hidden(A_204, B_205) | ~r2_hidden(A_204, k4_xboole_0(B_205, B_205)))), inference(superposition, [status(thm), theory('equality')], [c_269, c_1045])).
% 8.54/2.89  tff(c_4797, plain, (![A_206]: (~r2_hidden(A_206, k1_xboole_0) | ~r2_hidden(A_206, k1_xboole_0) | ~r2_hidden(A_206, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_374, c_4738])).
% 8.54/2.89  tff(c_4862, plain, (![A_208]: (~r2_hidden('#skF_2'(A_208, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k3_xboole_0(A_208, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1953, c_4797])).
% 8.54/2.89  tff(c_4879, plain, (![A_209]: (k3_xboole_0(A_209, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1953, c_4862])).
% 8.54/2.89  tff(c_42, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.54/2.89  tff(c_4904, plain, (![A_209]: (k5_xboole_0(A_209, k1_xboole_0)=k4_xboole_0(A_209, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4879, c_42])).
% 8.54/2.89  tff(c_4929, plain, (![A_209]: (k5_xboole_0(A_209, k1_xboole_0)=A_209)), inference(demodulation, [status(thm), theory('equality')], [c_374, c_4904])).
% 8.54/2.89  tff(c_1845, plain, (![A_147, B_148, C_149]: (r2_hidden('#skF_1'(A_147, B_148, C_149), A_147) | r2_hidden('#skF_2'(A_147, B_148, C_149), C_149) | k3_xboole_0(A_147, B_148)=C_149)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.54/2.89  tff(c_1882, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148, A_147), A_147) | k3_xboole_0(A_147, B_148)=A_147)), inference(resolution, [status(thm)], [c_1845, c_16])).
% 8.54/2.89  tff(c_5134, plain, (![B_220]: (~r2_hidden('#skF_2'(k1_xboole_0, B_220, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k1_xboole_0, B_220)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1882, c_4797])).
% 8.54/2.89  tff(c_5151, plain, (![B_221]: (k3_xboole_0(k1_xboole_0, B_221)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1882, c_5134])).
% 8.54/2.89  tff(c_5171, plain, (![B_221]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_221))), inference(superposition, [status(thm), theory('equality')], [c_5151, c_42])).
% 8.54/2.89  tff(c_5192, plain, (![B_221]: (k4_xboole_0(k1_xboole_0, B_221)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_5171])).
% 8.54/2.89  tff(c_304, plain, (![A_77, B_78]: (k4_xboole_0(k2_xboole_0(A_77, B_78), B_78)=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.54/2.89  tff(c_316, plain, (![A_45]: (k4_xboole_0(k1_xboole_0, A_45)=k4_xboole_0(A_45, A_45))), inference(superposition, [status(thm), theory('equality')], [c_109, c_304])).
% 8.54/2.89  tff(c_52, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.54/2.89  tff(c_957, plain, (![A_114, B_115, C_116]: (r1_tarski(k2_tarski(A_114, B_115), C_116) | ~r2_hidden(B_115, C_116) | ~r2_hidden(A_114, C_116))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.54/2.89  tff(c_991, plain, (![A_119, C_120]: (r1_tarski(k1_tarski(A_119), C_120) | ~r2_hidden(A_119, C_120) | ~r2_hidden(A_119, C_120))), inference(superposition, [status(thm), theory('equality')], [c_52, c_957])).
% 8.54/2.89  tff(c_46, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.54/2.89  tff(c_1003, plain, (![A_121, C_122]: (k3_xboole_0(k1_tarski(A_121), C_122)=k1_tarski(A_121) | ~r2_hidden(A_121, C_122))), inference(resolution, [status(thm)], [c_991, c_46])).
% 8.54/2.89  tff(c_1021, plain, (![A_121, C_122]: (k5_xboole_0(k1_tarski(A_121), k1_tarski(A_121))=k4_xboole_0(k1_tarski(A_121), C_122) | ~r2_hidden(A_121, C_122))), inference(superposition, [status(thm), theory('equality')], [c_1003, c_42])).
% 8.54/2.89  tff(c_1037, plain, (![A_121, C_122]: (k4_xboole_0(k1_tarski(A_121), C_122)=k4_xboole_0(k1_xboole_0, k1_tarski(A_121)) | ~r2_hidden(A_121, C_122))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_269, c_1021])).
% 8.54/2.89  tff(c_10401, plain, (![A_306, C_307]: (k4_xboole_0(k1_tarski(A_306), C_307)=k1_xboole_0 | ~r2_hidden(A_306, C_307))), inference(demodulation, [status(thm), theory('equality')], [c_5192, c_1037])).
% 8.54/2.89  tff(c_48, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.54/2.89  tff(c_10476, plain, (![C_307, A_306]: (k2_xboole_0(C_307, k1_tarski(A_306))=k2_xboole_0(C_307, k1_xboole_0) | ~r2_hidden(A_306, C_307))), inference(superposition, [status(thm), theory('equality')], [c_10401, c_48])).
% 8.54/2.89  tff(c_10523, plain, (![C_308, A_309]: (k2_xboole_0(C_308, k1_tarski(A_309))=C_308 | ~r2_hidden(A_309, C_308))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10476])).
% 8.54/2.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.54/2.89  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.54/2.89  tff(c_72, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 8.54/2.89  tff(c_10653, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10523, c_72])).
% 8.54/2.89  tff(c_10724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_10653])).
% 8.54/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/2.89  
% 8.54/2.89  Inference rules
% 8.54/2.89  ----------------------
% 8.54/2.89  #Ref     : 0
% 8.54/2.89  #Sup     : 2482
% 8.54/2.89  #Fact    : 4
% 8.54/2.89  #Define  : 0
% 8.54/2.89  #Split   : 0
% 8.54/2.89  #Chain   : 0
% 8.54/2.89  #Close   : 0
% 8.54/2.89  
% 8.54/2.89  Ordering : KBO
% 8.54/2.89  
% 8.54/2.89  Simplification rules
% 8.54/2.89  ----------------------
% 8.54/2.89  #Subsume      : 220
% 8.54/2.89  #Demod        : 4073
% 8.54/2.89  #Tautology    : 1555
% 8.54/2.89  #SimpNegUnit  : 0
% 8.54/2.89  #BackRed      : 27
% 8.54/2.89  
% 8.54/2.89  #Partial instantiations: 0
% 8.54/2.89  #Strategies tried      : 1
% 8.54/2.89  
% 8.54/2.89  Timing (in seconds)
% 8.54/2.89  ----------------------
% 8.56/2.90  Preprocessing        : 0.34
% 8.56/2.90  Parsing              : 0.18
% 8.56/2.90  CNF conversion       : 0.02
% 8.56/2.90  Main loop            : 1.77
% 8.56/2.90  Inferencing          : 0.49
% 8.56/2.90  Reduction            : 0.86
% 8.56/2.90  Demodulation         : 0.75
% 8.56/2.90  BG Simplification    : 0.05
% 8.56/2.90  Subsumption          : 0.28
% 8.56/2.90  Abstraction          : 0.09
% 8.56/2.90  MUC search           : 0.00
% 8.56/2.90  Cooper               : 0.00
% 8.56/2.90  Total                : 2.15
% 8.56/2.90  Index Insertion      : 0.00
% 8.56/2.90  Index Deletion       : 0.00
% 8.56/2.90  Index Matching       : 0.00
% 8.56/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
