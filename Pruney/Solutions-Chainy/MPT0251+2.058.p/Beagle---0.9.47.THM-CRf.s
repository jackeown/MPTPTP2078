%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:54 EST 2020

% Result     : Theorem 14.08s
% Output     : CNFRefutation 14.08s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 142 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :   94 ( 166 expanded)
%              Number of equality atoms :   45 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_80,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_54,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_111,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_215,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(B_59,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_111])).

tff(c_44,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_242,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44])).

tff(c_301,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_22])).

tff(c_30,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_149,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_157,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = A_18 ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_313,plain,(
    ! [A_62] : k3_xboole_0(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_157])).

tff(c_501,plain,(
    ! [A_74,B_75] : k2_xboole_0(k3_xboole_0(A_74,B_75),k4_xboole_0(A_74,B_75)) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_672,plain,(
    ! [A_91] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_91)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_501])).

tff(c_270,plain,(
    ! [A_61] : k2_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_22])).

tff(c_687,plain,(
    ! [A_91] : k4_xboole_0(k1_xboole_0,A_91) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_270])).

tff(c_417,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_426,plain,(
    ! [A_62] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_417])).

tff(c_961,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_426])).

tff(c_1438,plain,(
    ! [A_141,C_142,B_143] :
      ( ~ r2_hidden(A_141,C_142)
      | ~ r2_hidden(A_141,B_143)
      | ~ r2_hidden(A_141,k5_xboole_0(B_143,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3022,plain,(
    ! [A_198] :
      ( ~ r2_hidden(A_198,k1_xboole_0)
      | ~ r2_hidden(A_198,k1_xboole_0)
      | ~ r2_hidden(A_198,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_1438])).

tff(c_3031,plain,(
    ! [B_199] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_199),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_199) ) ),
    inference(resolution,[status(thm)],[c_18,c_3022])).

tff(c_3040,plain,(
    ! [B_5] : r1_xboole_0(k1_xboole_0,B_5) ),
    inference(resolution,[status(thm)],[c_18,c_3031])).

tff(c_1135,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(k2_xboole_0(A_116,B_117),B_117) = A_116
      | ~ r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1179,plain,(
    ! [A_61] :
      ( k4_xboole_0(A_61,A_61) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_1135])).

tff(c_3044,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3040,c_1179])).

tff(c_73,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_73])).

tff(c_156,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_76,c_149])).

tff(c_435,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_417])).

tff(c_36,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1578,plain,(
    ! [A_153,B_154,C_155] :
      ( r1_tarski(k2_tarski(A_153,B_154),C_155)
      | ~ r2_hidden(B_154,C_155)
      | ~ r2_hidden(A_153,C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1844,plain,(
    ! [A_162,C_163] :
      ( r1_tarski(k1_tarski(A_162),C_163)
      | ~ r2_hidden(A_162,C_163)
      | ~ r2_hidden(A_162,C_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1578])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2280,plain,(
    ! [A_173,C_174] :
      ( k3_xboole_0(k1_tarski(A_173),C_174) = k1_tarski(A_173)
      | ~ r2_hidden(A_173,C_174) ) ),
    inference(resolution,[status(thm)],[c_1844,c_24])).

tff(c_20,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2311,plain,(
    ! [A_173,C_174] :
      ( k5_xboole_0(k1_tarski(A_173),k1_tarski(A_173)) = k4_xboole_0(k1_tarski(A_173),C_174)
      | ~ r2_hidden(A_173,C_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2280,c_20])).

tff(c_2344,plain,(
    ! [A_173,C_174] :
      ( k4_xboole_0(k1_tarski(A_173),k1_tarski(A_173)) = k4_xboole_0(k1_tarski(A_173),C_174)
      | ~ r2_hidden(A_173,C_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_2311])).

tff(c_37614,plain,(
    ! [A_533,C_534] :
      ( k4_xboole_0(k1_tarski(A_533),C_534) = k1_xboole_0
      | ~ r2_hidden(A_533,C_534) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3044,c_2344])).

tff(c_26,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37915,plain,(
    ! [C_534,A_533] :
      ( k2_xboole_0(C_534,k1_tarski(A_533)) = k2_xboole_0(C_534,k1_xboole_0)
      | ~ r2_hidden(A_533,C_534) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37614,c_26])).

tff(c_38056,plain,(
    ! [C_535,A_536] :
      ( k2_xboole_0(C_535,k1_tarski(A_536)) = C_535
      | ~ r2_hidden(A_536,C_535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_37915])).

tff(c_221,plain,(
    ! [B_59,A_58] : k2_xboole_0(B_59,A_58) = k2_xboole_0(A_58,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_241,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_52])).

tff(c_38472,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38056,c_241])).

tff(c_38615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_38472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:02:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.08/7.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.08/7.05  
% 14.08/7.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.08/7.05  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 14.08/7.05  
% 14.08/7.05  %Foreground sorts:
% 14.08/7.05  
% 14.08/7.05  
% 14.08/7.05  %Background operators:
% 14.08/7.05  
% 14.08/7.05  
% 14.08/7.05  %Foreground operators:
% 14.08/7.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.08/7.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.08/7.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.08/7.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.08/7.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.08/7.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.08/7.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.08/7.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.08/7.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.08/7.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.08/7.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.08/7.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.08/7.05  tff('#skF_2', type, '#skF_2': $i).
% 14.08/7.05  tff('#skF_3', type, '#skF_3': $i).
% 14.08/7.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.08/7.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.08/7.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.08/7.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.08/7.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.08/7.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.08/7.05  
% 14.08/7.07  tff(f_91, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 14.08/7.07  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 14.08/7.07  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.08/7.07  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.08/7.07  tff(f_80, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 14.08/7.07  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.08/7.07  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.08/7.07  tff(f_62, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 14.08/7.07  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.08/7.07  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 14.08/7.07  tff(f_68, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 14.08/7.07  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 14.08/7.07  tff(f_86, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 14.08/7.07  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.08/7.07  tff(c_54, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.08/7.07  tff(c_22, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.08/7.07  tff(c_18, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.08/7.07  tff(c_34, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.08/7.07  tff(c_111, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.08/7.07  tff(c_215, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(B_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_34, c_111])).
% 14.08/7.07  tff(c_44, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.08/7.07  tff(c_242, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_215, c_44])).
% 14.08/7.07  tff(c_301, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_242, c_22])).
% 14.08/7.07  tff(c_30, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.08/7.07  tff(c_149, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.08/7.07  tff(c_157, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=A_18)), inference(resolution, [status(thm)], [c_30, c_149])).
% 14.08/7.07  tff(c_313, plain, (![A_62]: (k3_xboole_0(k1_xboole_0, A_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_301, c_157])).
% 14.08/7.07  tff(c_501, plain, (![A_74, B_75]: (k2_xboole_0(k3_xboole_0(A_74, B_75), k4_xboole_0(A_74, B_75))=A_74)), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.08/7.07  tff(c_672, plain, (![A_91]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_91))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_313, c_501])).
% 14.08/7.07  tff(c_270, plain, (![A_61]: (k2_xboole_0(k1_xboole_0, A_61)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_242, c_22])).
% 14.08/7.07  tff(c_687, plain, (![A_91]: (k4_xboole_0(k1_xboole_0, A_91)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_672, c_270])).
% 14.08/7.07  tff(c_417, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.08/7.07  tff(c_426, plain, (![A_62]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_62))), inference(superposition, [status(thm), theory('equality')], [c_313, c_417])).
% 14.08/7.07  tff(c_961, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_687, c_426])).
% 14.08/7.07  tff(c_1438, plain, (![A_141, C_142, B_143]: (~r2_hidden(A_141, C_142) | ~r2_hidden(A_141, B_143) | ~r2_hidden(A_141, k5_xboole_0(B_143, C_142)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.08/7.07  tff(c_3022, plain, (![A_198]: (~r2_hidden(A_198, k1_xboole_0) | ~r2_hidden(A_198, k1_xboole_0) | ~r2_hidden(A_198, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_961, c_1438])).
% 14.08/7.07  tff(c_3031, plain, (![B_199]: (~r2_hidden('#skF_1'(k1_xboole_0, B_199), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_199))), inference(resolution, [status(thm)], [c_18, c_3022])).
% 14.08/7.07  tff(c_3040, plain, (![B_5]: (r1_xboole_0(k1_xboole_0, B_5))), inference(resolution, [status(thm)], [c_18, c_3031])).
% 14.08/7.07  tff(c_1135, plain, (![A_116, B_117]: (k4_xboole_0(k2_xboole_0(A_116, B_117), B_117)=A_116 | ~r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.08/7.07  tff(c_1179, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_61))), inference(superposition, [status(thm), theory('equality')], [c_270, c_1135])).
% 14.08/7.07  tff(c_3044, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3040, c_1179])).
% 14.08/7.07  tff(c_73, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.08/7.07  tff(c_76, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_22, c_73])).
% 14.08/7.07  tff(c_156, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(resolution, [status(thm)], [c_76, c_149])).
% 14.08/7.07  tff(c_435, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_156, c_417])).
% 14.08/7.07  tff(c_36, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.08/7.07  tff(c_1578, plain, (![A_153, B_154, C_155]: (r1_tarski(k2_tarski(A_153, B_154), C_155) | ~r2_hidden(B_154, C_155) | ~r2_hidden(A_153, C_155))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.08/7.07  tff(c_1844, plain, (![A_162, C_163]: (r1_tarski(k1_tarski(A_162), C_163) | ~r2_hidden(A_162, C_163) | ~r2_hidden(A_162, C_163))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1578])).
% 14.08/7.07  tff(c_24, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.08/7.07  tff(c_2280, plain, (![A_173, C_174]: (k3_xboole_0(k1_tarski(A_173), C_174)=k1_tarski(A_173) | ~r2_hidden(A_173, C_174))), inference(resolution, [status(thm)], [c_1844, c_24])).
% 14.08/7.07  tff(c_20, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.08/7.07  tff(c_2311, plain, (![A_173, C_174]: (k5_xboole_0(k1_tarski(A_173), k1_tarski(A_173))=k4_xboole_0(k1_tarski(A_173), C_174) | ~r2_hidden(A_173, C_174))), inference(superposition, [status(thm), theory('equality')], [c_2280, c_20])).
% 14.08/7.07  tff(c_2344, plain, (![A_173, C_174]: (k4_xboole_0(k1_tarski(A_173), k1_tarski(A_173))=k4_xboole_0(k1_tarski(A_173), C_174) | ~r2_hidden(A_173, C_174))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_2311])).
% 14.08/7.07  tff(c_37614, plain, (![A_533, C_534]: (k4_xboole_0(k1_tarski(A_533), C_534)=k1_xboole_0 | ~r2_hidden(A_533, C_534))), inference(demodulation, [status(thm), theory('equality')], [c_3044, c_2344])).
% 14.08/7.07  tff(c_26, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.08/7.07  tff(c_37915, plain, (![C_534, A_533]: (k2_xboole_0(C_534, k1_tarski(A_533))=k2_xboole_0(C_534, k1_xboole_0) | ~r2_hidden(A_533, C_534))), inference(superposition, [status(thm), theory('equality')], [c_37614, c_26])).
% 14.08/7.07  tff(c_38056, plain, (![C_535, A_536]: (k2_xboole_0(C_535, k1_tarski(A_536))=C_535 | ~r2_hidden(A_536, C_535))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_37915])).
% 14.08/7.07  tff(c_221, plain, (![B_59, A_58]: (k2_xboole_0(B_59, A_58)=k2_xboole_0(A_58, B_59))), inference(superposition, [status(thm), theory('equality')], [c_215, c_44])).
% 14.08/7.07  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.08/7.07  tff(c_241, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_52])).
% 14.08/7.07  tff(c_38472, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38056, c_241])).
% 14.08/7.07  tff(c_38615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_38472])).
% 14.08/7.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.08/7.07  
% 14.08/7.07  Inference rules
% 14.08/7.07  ----------------------
% 14.08/7.07  #Ref     : 0
% 14.08/7.07  #Sup     : 9410
% 14.08/7.07  #Fact    : 16
% 14.08/7.07  #Define  : 0
% 14.08/7.07  #Split   : 0
% 14.08/7.07  #Chain   : 0
% 14.08/7.07  #Close   : 0
% 14.08/7.07  
% 14.08/7.07  Ordering : KBO
% 14.08/7.07  
% 14.08/7.07  Simplification rules
% 14.08/7.07  ----------------------
% 14.08/7.07  #Subsume      : 1079
% 14.08/7.07  #Demod        : 18713
% 14.08/7.07  #Tautology    : 5999
% 14.08/7.07  #SimpNegUnit  : 86
% 14.08/7.07  #BackRed      : 26
% 14.08/7.07  
% 14.08/7.07  #Partial instantiations: 0
% 14.08/7.07  #Strategies tried      : 1
% 14.08/7.07  
% 14.08/7.07  Timing (in seconds)
% 14.08/7.07  ----------------------
% 14.08/7.07  Preprocessing        : 0.32
% 14.08/7.07  Parsing              : 0.17
% 14.08/7.07  CNF conversion       : 0.02
% 14.08/7.07  Main loop            : 5.98
% 14.08/7.07  Inferencing          : 0.88
% 14.08/7.07  Reduction            : 3.82
% 14.08/7.07  Demodulation         : 3.51
% 14.08/7.07  BG Simplification    : 0.10
% 14.08/7.07  Subsumption          : 0.95
% 14.08/7.07  Abstraction          : 0.21
% 14.08/7.07  MUC search           : 0.00
% 14.08/7.07  Cooper               : 0.00
% 14.08/7.07  Total                : 6.32
% 14.08/7.07  Index Insertion      : 0.00
% 14.08/7.07  Index Deletion       : 0.00
% 14.08/7.07  Index Matching       : 0.00
% 14.08/7.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
