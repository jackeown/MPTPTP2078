%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:24 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 210 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :   96 ( 317 expanded)
%              Number of equality atoms :   57 ( 137 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_47,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_108,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_94,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_106,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_93,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(A_61,B_62)
      | k4_xboole_0(A_61,B_62) != A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [B_62,A_61] :
      ( r1_xboole_0(B_62,A_61)
      | k4_xboole_0(A_61,B_62) != A_61 ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_50,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_130,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_148,plain,(
    ! [B_68,A_69] : r2_hidden(B_68,k2_tarski(A_69,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_24])).

tff(c_151,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_148])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_195,plain,(
    ! [A_13,C_83] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_184])).

tff(c_199,plain,(
    ! [C_84] : ~ r2_hidden(C_84,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_227,plain,(
    ! [A_89] : r1_xboole_0(A_89,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_269,plain,(
    ! [A_94] : k4_xboole_0(A_94,k1_xboole_0) = A_94 ),
    inference(resolution,[status(thm)],[c_227,c_18])).

tff(c_279,plain,(
    ! [A_94] : k4_xboole_0(A_94,A_94) = k3_xboole_0(A_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_16])).

tff(c_289,plain,(
    ! [A_94] : k4_xboole_0(A_94,A_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_279])).

tff(c_233,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(resolution,[status(thm)],[c_227,c_18])).

tff(c_314,plain,(
    ! [A_96] : k4_xboole_0(A_96,A_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_279])).

tff(c_326,plain,(
    ! [A_96] : k4_xboole_0(A_96,k1_xboole_0) = k3_xboole_0(A_96,A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_16])).

tff(c_358,plain,(
    ! [A_99] : k3_xboole_0(A_99,A_99) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_326])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_393,plain,(
    ! [A_100,C_101] :
      ( ~ r1_xboole_0(A_100,A_100)
      | ~ r2_hidden(C_101,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_12])).

tff(c_402,plain,(
    ! [C_101,A_61] :
      ( ~ r2_hidden(C_101,A_61)
      | k4_xboole_0(A_61,A_61) != A_61 ) ),
    inference(resolution,[status(thm)],[c_100,c_393])).

tff(c_413,plain,(
    ! [C_102,A_103] :
      ( ~ r2_hidden(C_102,A_103)
      | k1_xboole_0 != A_103 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_402])).

tff(c_445,plain,(
    ! [A_34] : k1_tarski(A_34) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_413])).

tff(c_60,plain,(
    ! [A_44] : k1_setfam_1(k1_tarski(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_450,plain,(
    ! [A_104,B_105,C_106,D_107] : k2_xboole_0(k1_enumset1(A_104,B_105,C_106),k1_tarski(D_107)) = k2_enumset1(A_104,B_105,C_106,D_107) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_459,plain,(
    ! [A_35,B_36,D_107] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(D_107)) = k2_enumset1(A_35,A_35,B_36,D_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_450])).

tff(c_2467,plain,(
    ! [A_251,B_252,D_253] : k2_xboole_0(k2_tarski(A_251,B_252),k1_tarski(D_253)) = k1_enumset1(A_251,B_252,D_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_459])).

tff(c_2476,plain,(
    ! [A_34,D_253] : k2_xboole_0(k1_tarski(A_34),k1_tarski(D_253)) = k1_enumset1(A_34,A_34,D_253) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2467])).

tff(c_2479,plain,(
    ! [A_34,D_253] : k2_xboole_0(k1_tarski(A_34),k1_tarski(D_253)) = k2_tarski(A_34,D_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2476])).

tff(c_516,plain,(
    ! [A_120,B_121] :
      ( k3_xboole_0(k1_setfam_1(A_120),k1_setfam_1(B_121)) = k1_setfam_1(k2_xboole_0(A_120,B_121))
      | k1_xboole_0 = B_121
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_539,plain,(
    ! [A_44,B_121] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_44),B_121)) = k3_xboole_0(A_44,k1_setfam_1(B_121))
      | k1_xboole_0 = B_121
      | k1_tarski(A_44) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_516])).

tff(c_3240,plain,(
    ! [A_308,B_309] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_308),B_309)) = k3_xboole_0(A_308,k1_setfam_1(B_309))
      | k1_xboole_0 = B_309 ) ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_539])).

tff(c_3255,plain,(
    ! [A_34,D_253] :
      ( k3_xboole_0(A_34,k1_setfam_1(k1_tarski(D_253))) = k1_setfam_1(k2_tarski(A_34,D_253))
      | k1_tarski(D_253) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2479,c_3240])).

tff(c_3262,plain,(
    ! [A_34,D_253] :
      ( k1_setfam_1(k2_tarski(A_34,D_253)) = k3_xboole_0(A_34,D_253)
      | k1_tarski(D_253) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3255])).

tff(c_3263,plain,(
    ! [A_34,D_253] : k1_setfam_1(k2_tarski(A_34,D_253)) = k3_xboole_0(A_34,D_253) ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_3262])).

tff(c_62,plain,(
    k1_setfam_1(k2_tarski('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3263,c_62])).

tff(c_3270,plain,(
    ! [A_310] : ~ r1_xboole_0(A_310,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_3281,plain,(
    ! [B_311] : k4_xboole_0(k1_xboole_0,B_311) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_3270])).

tff(c_3296,plain,(
    ! [B_316] : k3_xboole_0(k1_xboole_0,B_316) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3281])).

tff(c_3301,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:17:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.96  
% 4.44/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.96  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1
% 4.44/1.96  
% 4.44/1.96  %Foreground sorts:
% 4.44/1.96  
% 4.44/1.96  
% 4.44/1.96  %Background operators:
% 4.44/1.96  
% 4.44/1.96  
% 4.44/1.96  %Foreground operators:
% 4.44/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.44/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.44/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.44/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.44/1.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.44/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.44/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.44/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.44/1.96  tff('#skF_6', type, '#skF_6': $i).
% 4.44/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.44/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.44/1.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.44/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.44/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.44/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.44/1.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.44/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.44/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.44/1.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.44/1.96  
% 4.66/1.98  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.66/1.98  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.66/1.98  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.66/1.98  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.66/1.98  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.66/1.98  tff(f_92, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.66/1.98  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.66/1.98  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.66/1.98  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.66/1.98  tff(f_108, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.66/1.98  tff(f_94, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.66/1.98  tff(f_86, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.66/1.98  tff(f_106, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 4.66/1.98  tff(f_111, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.66/1.98  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.66/1.98  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.66/1.98  tff(c_93, plain, (![A_61, B_62]: (r1_xboole_0(A_61, B_62) | k4_xboole_0(A_61, B_62)!=A_61)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.66/1.98  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.66/1.98  tff(c_100, plain, (![B_62, A_61]: (r1_xboole_0(B_62, A_61) | k4_xboole_0(A_61, B_62)!=A_61)), inference(resolution, [status(thm)], [c_93, c_2])).
% 4.66/1.98  tff(c_50, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.66/1.98  tff(c_130, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.66/1.98  tff(c_24, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.98  tff(c_148, plain, (![B_68, A_69]: (r2_hidden(B_68, k2_tarski(A_69, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_24])).
% 4.66/1.98  tff(c_151, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_148])).
% 4.66/1.98  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.66/1.98  tff(c_184, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.98  tff(c_195, plain, (![A_13, C_83]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_184])).
% 4.66/1.98  tff(c_199, plain, (![C_84]: (~r2_hidden(C_84, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_195])).
% 4.66/1.98  tff(c_227, plain, (![A_89]: (r1_xboole_0(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_199])).
% 4.66/1.98  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.66/1.98  tff(c_269, plain, (![A_94]: (k4_xboole_0(A_94, k1_xboole_0)=A_94)), inference(resolution, [status(thm)], [c_227, c_18])).
% 4.66/1.98  tff(c_279, plain, (![A_94]: (k4_xboole_0(A_94, A_94)=k3_xboole_0(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_269, c_16])).
% 4.66/1.98  tff(c_289, plain, (![A_94]: (k4_xboole_0(A_94, A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_279])).
% 4.66/1.98  tff(c_233, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=A_89)), inference(resolution, [status(thm)], [c_227, c_18])).
% 4.66/1.98  tff(c_314, plain, (![A_96]: (k4_xboole_0(A_96, A_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_279])).
% 4.66/1.98  tff(c_326, plain, (![A_96]: (k4_xboole_0(A_96, k1_xboole_0)=k3_xboole_0(A_96, A_96))), inference(superposition, [status(thm), theory('equality')], [c_314, c_16])).
% 4.66/1.98  tff(c_358, plain, (![A_99]: (k3_xboole_0(A_99, A_99)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_326])).
% 4.66/1.98  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.98  tff(c_393, plain, (![A_100, C_101]: (~r1_xboole_0(A_100, A_100) | ~r2_hidden(C_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_358, c_12])).
% 4.66/1.98  tff(c_402, plain, (![C_101, A_61]: (~r2_hidden(C_101, A_61) | k4_xboole_0(A_61, A_61)!=A_61)), inference(resolution, [status(thm)], [c_100, c_393])).
% 4.66/1.98  tff(c_413, plain, (![C_102, A_103]: (~r2_hidden(C_102, A_103) | k1_xboole_0!=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_289, c_402])).
% 4.66/1.98  tff(c_445, plain, (![A_34]: (k1_tarski(A_34)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_151, c_413])).
% 4.66/1.98  tff(c_60, plain, (![A_44]: (k1_setfam_1(k1_tarski(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.66/1.98  tff(c_52, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.66/1.98  tff(c_54, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.66/1.98  tff(c_450, plain, (![A_104, B_105, C_106, D_107]: (k2_xboole_0(k1_enumset1(A_104, B_105, C_106), k1_tarski(D_107))=k2_enumset1(A_104, B_105, C_106, D_107))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.66/1.98  tff(c_459, plain, (![A_35, B_36, D_107]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(D_107))=k2_enumset1(A_35, A_35, B_36, D_107))), inference(superposition, [status(thm), theory('equality')], [c_52, c_450])).
% 4.66/1.98  tff(c_2467, plain, (![A_251, B_252, D_253]: (k2_xboole_0(k2_tarski(A_251, B_252), k1_tarski(D_253))=k1_enumset1(A_251, B_252, D_253))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_459])).
% 4.66/1.98  tff(c_2476, plain, (![A_34, D_253]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(D_253))=k1_enumset1(A_34, A_34, D_253))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2467])).
% 4.66/1.98  tff(c_2479, plain, (![A_34, D_253]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(D_253))=k2_tarski(A_34, D_253))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2476])).
% 4.66/1.98  tff(c_516, plain, (![A_120, B_121]: (k3_xboole_0(k1_setfam_1(A_120), k1_setfam_1(B_121))=k1_setfam_1(k2_xboole_0(A_120, B_121)) | k1_xboole_0=B_121 | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.66/1.98  tff(c_539, plain, (![A_44, B_121]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_44), B_121))=k3_xboole_0(A_44, k1_setfam_1(B_121)) | k1_xboole_0=B_121 | k1_tarski(A_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_516])).
% 4.66/1.98  tff(c_3240, plain, (![A_308, B_309]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_308), B_309))=k3_xboole_0(A_308, k1_setfam_1(B_309)) | k1_xboole_0=B_309)), inference(negUnitSimplification, [status(thm)], [c_445, c_539])).
% 4.66/1.98  tff(c_3255, plain, (![A_34, D_253]: (k3_xboole_0(A_34, k1_setfam_1(k1_tarski(D_253)))=k1_setfam_1(k2_tarski(A_34, D_253)) | k1_tarski(D_253)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2479, c_3240])).
% 4.66/1.98  tff(c_3262, plain, (![A_34, D_253]: (k1_setfam_1(k2_tarski(A_34, D_253))=k3_xboole_0(A_34, D_253) | k1_tarski(D_253)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3255])).
% 4.66/1.98  tff(c_3263, plain, (![A_34, D_253]: (k1_setfam_1(k2_tarski(A_34, D_253))=k3_xboole_0(A_34, D_253))), inference(negUnitSimplification, [status(thm)], [c_445, c_3262])).
% 4.66/1.98  tff(c_62, plain, (k1_setfam_1(k2_tarski('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.66/1.98  tff(c_3268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3263, c_62])).
% 4.66/1.98  tff(c_3270, plain, (![A_310]: (~r1_xboole_0(A_310, k1_xboole_0))), inference(splitRight, [status(thm)], [c_195])).
% 4.66/1.98  tff(c_3281, plain, (![B_311]: (k4_xboole_0(k1_xboole_0, B_311)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_100, c_3270])).
% 4.66/1.98  tff(c_3296, plain, (![B_316]: (k3_xboole_0(k1_xboole_0, B_316)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_3281])).
% 4.66/1.98  tff(c_3301, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_14, c_3296])).
% 4.66/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.98  
% 4.66/1.98  Inference rules
% 4.66/1.98  ----------------------
% 4.66/1.98  #Ref     : 0
% 4.66/1.98  #Sup     : 777
% 4.66/1.98  #Fact    : 0
% 4.66/1.98  #Define  : 0
% 4.66/1.98  #Split   : 1
% 4.66/1.98  #Chain   : 0
% 4.66/1.98  #Close   : 0
% 4.66/1.98  
% 4.66/1.98  Ordering : KBO
% 4.66/1.98  
% 4.66/1.98  Simplification rules
% 4.66/1.98  ----------------------
% 4.66/1.98  #Subsume      : 268
% 4.66/1.98  #Demod        : 194
% 4.66/1.98  #Tautology    : 293
% 4.66/1.98  #SimpNegUnit  : 14
% 4.66/1.98  #BackRed      : 1
% 4.66/1.98  
% 4.66/1.98  #Partial instantiations: 0
% 4.66/1.98  #Strategies tried      : 1
% 4.66/1.98  
% 4.66/1.98  Timing (in seconds)
% 4.66/1.98  ----------------------
% 4.66/1.98  Preprocessing        : 0.43
% 4.66/1.98  Parsing              : 0.24
% 4.66/1.98  CNF conversion       : 0.03
% 4.66/1.98  Main loop            : 0.70
% 4.66/1.98  Inferencing          : 0.25
% 4.66/1.98  Reduction            : 0.22
% 4.66/1.98  Demodulation         : 0.16
% 4.66/1.98  BG Simplification    : 0.03
% 4.66/1.98  Subsumption          : 0.15
% 4.66/1.98  Abstraction          : 0.04
% 4.66/1.98  MUC search           : 0.00
% 4.66/1.98  Cooper               : 0.00
% 4.66/1.98  Total                : 1.17
% 4.66/1.98  Index Insertion      : 0.00
% 4.66/1.98  Index Deletion       : 0.00
% 4.66/1.98  Index Matching       : 0.00
% 4.66/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
