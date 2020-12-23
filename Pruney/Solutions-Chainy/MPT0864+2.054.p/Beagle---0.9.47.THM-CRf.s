%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:15 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 146 expanded)
%              Number of leaves         :   42 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 172 expanded)
%              Number of equality atoms :   59 ( 134 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_984,plain,(
    ! [B_312,C_310,D_314,A_313,E_311] : k4_enumset1(A_313,A_313,B_312,C_310,D_314,E_311) = k3_enumset1(A_313,B_312,C_310,D_314,E_311) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [D_44,C_43,H_50,A_41,B_42,E_45] : r2_hidden(H_50,k4_enumset1(A_41,B_42,C_43,D_44,E_45,H_50)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1024,plain,(
    ! [D_317,E_320,C_318,A_321,B_319] : r2_hidden(E_320,k3_enumset1(A_321,B_319,C_318,D_317,E_320)) ),
    inference(superposition,[status(thm),theory(equality)],[c_984,c_42])).

tff(c_1028,plain,(
    ! [D_322,A_323,B_324,C_325] : r2_hidden(D_322,k2_enumset1(A_323,B_324,C_325,D_322)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1024])).

tff(c_1032,plain,(
    ! [C_326,A_327,B_328] : r2_hidden(C_326,k1_enumset1(A_327,B_328,C_326)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1028])).

tff(c_1045,plain,(
    ! [B_335,A_336] : r2_hidden(B_335,k2_tarski(A_336,B_335)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1032])).

tff(c_1054,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1045])).

tff(c_345,plain,(
    ! [C_136,A_139,E_137,B_138,D_140] : k4_enumset1(A_139,A_139,B_138,C_136,D_140,E_137) = k3_enumset1(A_139,B_138,C_136,D_140,E_137) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [D_44,F_46,C_43,H_50,B_42,E_45] : r2_hidden(H_50,k4_enumset1(H_50,B_42,C_43,D_44,E_45,F_46)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_425,plain,(
    ! [B_148,C_147,A_144,E_145,D_146] : r2_hidden(A_144,k3_enumset1(A_144,B_148,C_147,D_146,E_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_52])).

tff(c_429,plain,(
    ! [A_149,B_150,C_151,D_152] : r2_hidden(A_149,k2_enumset1(A_149,B_150,C_151,D_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_425])).

tff(c_433,plain,(
    ! [A_153,B_154,C_155] : r2_hidden(A_153,k1_enumset1(A_153,B_154,C_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_429])).

tff(c_437,plain,(
    ! [A_156,B_157] : r2_hidden(A_156,k2_tarski(A_156,B_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_433])).

tff(c_443,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_437])).

tff(c_90,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_113,plain,(
    ! [A_59,B_60] : k1_mcart_1(k4_tarski(A_59,B_60)) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_122,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_113])).

tff(c_138,plain,(
    ! [A_62,B_63] : k2_mcart_1(k4_tarski(A_62,B_63)) = B_63 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_147,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_138])).

tff(c_88,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_164,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_147,c_88])).

tff(c_165,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_168,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_90])).

tff(c_372,plain,(
    ! [A_141,B_142,C_143] : k2_zfmisc_1(k2_tarski(A_141,B_142),k1_tarski(C_143)) = k2_tarski(k4_tarski(A_141,C_143),k4_tarski(B_142,C_143)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_416,plain,(
    ! [A_141,C_143] : k2_zfmisc_1(k2_tarski(A_141,A_141),k1_tarski(C_143)) = k1_tarski(k4_tarski(A_141,C_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_372])).

tff(c_612,plain,(
    ! [A_222,C_223] : k2_zfmisc_1(k1_tarski(A_222),k1_tarski(C_223)) = k1_tarski(k4_tarski(A_222,C_223)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_416])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k2_xboole_0(A_64,B_65)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_161,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_154])).

tff(c_32,plain,(
    ! [B_37] : k4_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) != k1_tarski(B_37) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_232,plain,(
    ! [B_37] : k1_tarski(B_37) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_32])).

tff(c_235,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_tarski(A_77),B_78)
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(A_34,B_35))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_243,plain,(
    ! [A_77,B_35] :
      ( k1_tarski(A_77) = k1_xboole_0
      | ~ r2_hidden(A_77,k2_zfmisc_1(k1_tarski(A_77),B_35)) ) ),
    inference(resolution,[status(thm)],[c_235,c_30])).

tff(c_249,plain,(
    ! [A_77,B_35] : ~ r2_hidden(A_77,k2_zfmisc_1(k1_tarski(A_77),B_35)) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_243])).

tff(c_635,plain,(
    ! [A_224,C_225] : ~ r2_hidden(A_224,k1_tarski(k4_tarski(A_224,C_225))) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_249])).

tff(c_638,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_635])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_638])).

tff(c_642,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_645,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_90])).

tff(c_818,plain,(
    ! [A_296,B_297,C_298] : k2_zfmisc_1(k1_tarski(A_296),k2_tarski(B_297,C_298)) = k2_tarski(k4_tarski(A_296,B_297),k4_tarski(A_296,C_298)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_846,plain,(
    ! [A_296,C_298] : k2_zfmisc_1(k1_tarski(A_296),k2_tarski(C_298,C_298)) = k1_tarski(k4_tarski(A_296,C_298)) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_10])).

tff(c_871,plain,(
    ! [A_299,C_300] : k2_zfmisc_1(k1_tarski(A_299),k1_tarski(C_300)) = k1_tarski(k4_tarski(A_299,C_300)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_846])).

tff(c_697,plain,(
    ! [B_37] : k1_tarski(B_37) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_32])).

tff(c_708,plain,(
    ! [A_237,B_238] :
      ( r1_tarski(k1_tarski(A_237),B_238)
      | ~ r2_hidden(A_237,B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(B_35,A_34))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_716,plain,(
    ! [A_237,B_35] :
      ( k1_tarski(A_237) = k1_xboole_0
      | ~ r2_hidden(A_237,k2_zfmisc_1(B_35,k1_tarski(A_237))) ) ),
    inference(resolution,[status(thm)],[c_708,c_28])).

tff(c_722,plain,(
    ! [A_237,B_35] : ~ r2_hidden(A_237,k2_zfmisc_1(B_35,k1_tarski(A_237))) ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_716])).

tff(c_894,plain,(
    ! [C_301,A_302] : ~ r2_hidden(C_301,k1_tarski(k4_tarski(A_302,C_301))) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_722])).

tff(c_897,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_894])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.59  
% 3.18/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.59  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 3.18/1.59  
% 3.18/1.59  %Foreground sorts:
% 3.18/1.59  
% 3.18/1.59  
% 3.18/1.59  %Background operators:
% 3.18/1.59  
% 3.18/1.59  
% 3.18/1.59  %Foreground operators:
% 3.18/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.18/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.59  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.18/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.18/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.59  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.18/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.18/1.59  
% 3.18/1.61  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.18/1.61  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.18/1.61  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.18/1.61  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.18/1.61  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.18/1.61  tff(f_90, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.18/1.61  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.18/1.61  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.18/1.61  tff(f_66, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.18/1.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.18/1.61  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.18/1.61  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.18/1.61  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.18/1.61  tff(f_57, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.18/1.61  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.18/1.61  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.61  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.61  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.61  tff(c_984, plain, (![B_312, C_310, D_314, A_313, E_311]: (k4_enumset1(A_313, A_313, B_312, C_310, D_314, E_311)=k3_enumset1(A_313, B_312, C_310, D_314, E_311))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.61  tff(c_42, plain, (![D_44, C_43, H_50, A_41, B_42, E_45]: (r2_hidden(H_50, k4_enumset1(A_41, B_42, C_43, D_44, E_45, H_50)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.18/1.61  tff(c_1024, plain, (![D_317, E_320, C_318, A_321, B_319]: (r2_hidden(E_320, k3_enumset1(A_321, B_319, C_318, D_317, E_320)))), inference(superposition, [status(thm), theory('equality')], [c_984, c_42])).
% 3.18/1.61  tff(c_1028, plain, (![D_322, A_323, B_324, C_325]: (r2_hidden(D_322, k2_enumset1(A_323, B_324, C_325, D_322)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1024])).
% 3.18/1.61  tff(c_1032, plain, (![C_326, A_327, B_328]: (r2_hidden(C_326, k1_enumset1(A_327, B_328, C_326)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1028])).
% 3.18/1.61  tff(c_1045, plain, (![B_335, A_336]: (r2_hidden(B_335, k2_tarski(A_336, B_335)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1032])).
% 3.18/1.61  tff(c_1054, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1045])).
% 3.18/1.61  tff(c_345, plain, (![C_136, A_139, E_137, B_138, D_140]: (k4_enumset1(A_139, A_139, B_138, C_136, D_140, E_137)=k3_enumset1(A_139, B_138, C_136, D_140, E_137))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.61  tff(c_52, plain, (![D_44, F_46, C_43, H_50, B_42, E_45]: (r2_hidden(H_50, k4_enumset1(H_50, B_42, C_43, D_44, E_45, F_46)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.18/1.61  tff(c_425, plain, (![B_148, C_147, A_144, E_145, D_146]: (r2_hidden(A_144, k3_enumset1(A_144, B_148, C_147, D_146, E_145)))), inference(superposition, [status(thm), theory('equality')], [c_345, c_52])).
% 3.18/1.61  tff(c_429, plain, (![A_149, B_150, C_151, D_152]: (r2_hidden(A_149, k2_enumset1(A_149, B_150, C_151, D_152)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_425])).
% 3.18/1.61  tff(c_433, plain, (![A_153, B_154, C_155]: (r2_hidden(A_153, k1_enumset1(A_153, B_154, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_429])).
% 3.18/1.61  tff(c_437, plain, (![A_156, B_157]: (r2_hidden(A_156, k2_tarski(A_156, B_157)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_433])).
% 3.18/1.61  tff(c_443, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_437])).
% 3.18/1.61  tff(c_90, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.18/1.61  tff(c_113, plain, (![A_59, B_60]: (k1_mcart_1(k4_tarski(A_59, B_60))=A_59)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.61  tff(c_122, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_90, c_113])).
% 3.18/1.61  tff(c_138, plain, (![A_62, B_63]: (k2_mcart_1(k4_tarski(A_62, B_63))=B_63)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.61  tff(c_147, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_90, c_138])).
% 3.18/1.61  tff(c_88, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.18/1.61  tff(c_164, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_147, c_88])).
% 3.18/1.61  tff(c_165, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_164])).
% 3.18/1.61  tff(c_168, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_90])).
% 3.18/1.61  tff(c_372, plain, (![A_141, B_142, C_143]: (k2_zfmisc_1(k2_tarski(A_141, B_142), k1_tarski(C_143))=k2_tarski(k4_tarski(A_141, C_143), k4_tarski(B_142, C_143)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.18/1.61  tff(c_416, plain, (![A_141, C_143]: (k2_zfmisc_1(k2_tarski(A_141, A_141), k1_tarski(C_143))=k1_tarski(k4_tarski(A_141, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_372])).
% 3.18/1.61  tff(c_612, plain, (![A_222, C_223]: (k2_zfmisc_1(k1_tarski(A_222), k1_tarski(C_223))=k1_tarski(k4_tarski(A_222, C_223)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_416])).
% 3.18/1.61  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.61  tff(c_154, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k2_xboole_0(A_64, B_65))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.61  tff(c_161, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_154])).
% 3.18/1.61  tff(c_32, plain, (![B_37]: (k4_xboole_0(k1_tarski(B_37), k1_tarski(B_37))!=k1_tarski(B_37))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.61  tff(c_232, plain, (![B_37]: (k1_tarski(B_37)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_32])).
% 3.18/1.61  tff(c_235, plain, (![A_77, B_78]: (r1_tarski(k1_tarski(A_77), B_78) | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.61  tff(c_30, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(A_34, B_35)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.61  tff(c_243, plain, (![A_77, B_35]: (k1_tarski(A_77)=k1_xboole_0 | ~r2_hidden(A_77, k2_zfmisc_1(k1_tarski(A_77), B_35)))), inference(resolution, [status(thm)], [c_235, c_30])).
% 3.18/1.61  tff(c_249, plain, (![A_77, B_35]: (~r2_hidden(A_77, k2_zfmisc_1(k1_tarski(A_77), B_35)))), inference(negUnitSimplification, [status(thm)], [c_232, c_243])).
% 3.18/1.61  tff(c_635, plain, (![A_224, C_225]: (~r2_hidden(A_224, k1_tarski(k4_tarski(A_224, C_225))))), inference(superposition, [status(thm), theory('equality')], [c_612, c_249])).
% 3.18/1.61  tff(c_638, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_635])).
% 3.18/1.61  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_443, c_638])).
% 3.18/1.61  tff(c_642, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_164])).
% 3.18/1.61  tff(c_645, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_642, c_90])).
% 3.18/1.61  tff(c_818, plain, (![A_296, B_297, C_298]: (k2_zfmisc_1(k1_tarski(A_296), k2_tarski(B_297, C_298))=k2_tarski(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.18/1.61  tff(c_846, plain, (![A_296, C_298]: (k2_zfmisc_1(k1_tarski(A_296), k2_tarski(C_298, C_298))=k1_tarski(k4_tarski(A_296, C_298)))), inference(superposition, [status(thm), theory('equality')], [c_818, c_10])).
% 3.18/1.61  tff(c_871, plain, (![A_299, C_300]: (k2_zfmisc_1(k1_tarski(A_299), k1_tarski(C_300))=k1_tarski(k4_tarski(A_299, C_300)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_846])).
% 3.18/1.61  tff(c_697, plain, (![B_37]: (k1_tarski(B_37)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_32])).
% 3.18/1.61  tff(c_708, plain, (![A_237, B_238]: (r1_tarski(k1_tarski(A_237), B_238) | ~r2_hidden(A_237, B_238))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.61  tff(c_28, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(B_35, A_34)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.61  tff(c_716, plain, (![A_237, B_35]: (k1_tarski(A_237)=k1_xboole_0 | ~r2_hidden(A_237, k2_zfmisc_1(B_35, k1_tarski(A_237))))), inference(resolution, [status(thm)], [c_708, c_28])).
% 3.18/1.61  tff(c_722, plain, (![A_237, B_35]: (~r2_hidden(A_237, k2_zfmisc_1(B_35, k1_tarski(A_237))))), inference(negUnitSimplification, [status(thm)], [c_697, c_716])).
% 3.18/1.61  tff(c_894, plain, (![C_301, A_302]: (~r2_hidden(C_301, k1_tarski(k4_tarski(A_302, C_301))))), inference(superposition, [status(thm), theory('equality')], [c_871, c_722])).
% 3.18/1.61  tff(c_897, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_645, c_894])).
% 3.18/1.61  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1054, c_897])).
% 3.18/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.61  
% 3.18/1.61  Inference rules
% 3.18/1.61  ----------------------
% 3.18/1.61  #Ref     : 0
% 3.18/1.61  #Sup     : 235
% 3.18/1.61  #Fact    : 0
% 3.18/1.61  #Define  : 0
% 3.18/1.61  #Split   : 1
% 3.18/1.61  #Chain   : 0
% 3.18/1.61  #Close   : 0
% 3.18/1.61  
% 3.18/1.61  Ordering : KBO
% 3.18/1.61  
% 3.18/1.61  Simplification rules
% 3.18/1.61  ----------------------
% 3.18/1.61  #Subsume      : 4
% 3.18/1.61  #Demod        : 49
% 3.18/1.61  #Tautology    : 132
% 3.18/1.61  #SimpNegUnit  : 16
% 3.18/1.61  #BackRed      : 6
% 3.18/1.61  
% 3.18/1.61  #Partial instantiations: 0
% 3.18/1.61  #Strategies tried      : 1
% 3.18/1.61  
% 3.18/1.61  Timing (in seconds)
% 3.18/1.61  ----------------------
% 3.18/1.61  Preprocessing        : 0.38
% 3.18/1.61  Parsing              : 0.20
% 3.18/1.61  CNF conversion       : 0.03
% 3.18/1.61  Main loop            : 0.39
% 3.18/1.61  Inferencing          : 0.15
% 3.18/1.61  Reduction            : 0.11
% 3.18/1.61  Demodulation         : 0.08
% 3.18/1.61  BG Simplification    : 0.03
% 3.18/1.61  Subsumption          : 0.08
% 3.18/1.61  Abstraction          : 0.03
% 3.18/1.61  MUC search           : 0.00
% 3.18/1.61  Cooper               : 0.00
% 3.50/1.61  Total                : 0.81
% 3.50/1.61  Index Insertion      : 0.00
% 3.50/1.61  Index Deletion       : 0.00
% 3.50/1.61  Index Matching       : 0.00
% 3.50/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
