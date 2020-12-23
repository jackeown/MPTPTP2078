%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:50 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 175 expanded)
%              Number of leaves         :   36 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  102 ( 255 expanded)
%              Number of equality atoms :   45 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_90,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_64,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [B_18] : r1_tarski(B_18,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_164,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,(
    ! [B_18] : k3_xboole_0(B_18,B_18) = B_18 ),
    inference(resolution,[status(thm)],[c_34,c_164])).

tff(c_368,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_377,plain,(
    ! [B_87,C_88] :
      ( ~ r1_xboole_0(B_87,B_87)
      | ~ r2_hidden(C_88,B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_368])).

tff(c_381,plain,(
    ! [C_88] : ~ r2_hidden(C_88,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_377])).

tff(c_328,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_337,plain,(
    ! [B_18] : k5_xboole_0(B_18,B_18) = k4_xboole_0(B_18,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_328])).

tff(c_382,plain,(
    ! [C_89] : ~ r2_hidden(C_89,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_377])).

tff(c_398,plain,(
    ! [B_93] : r1_tarski(k1_xboole_0,B_93) ),
    inference(resolution,[status(thm)],[c_6,c_382])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_406,plain,(
    ! [B_94] : k3_xboole_0(k1_xboole_0,B_94) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_398,c_40])).

tff(c_36,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_471,plain,(
    ! [B_97] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_36])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_483,plain,(
    ! [D_11] :
      ( r2_hidden(D_11,k1_xboole_0)
      | ~ r2_hidden(D_11,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_12])).

tff(c_495,plain,(
    ! [D_11] :
      ( r2_hidden(D_11,k1_xboole_0)
      | ~ r2_hidden(D_11,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_483])).

tff(c_499,plain,(
    ! [D_98] : ~ r2_hidden(D_98,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_495])).

tff(c_510,plain,(
    ! [B_99] : r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),B_99) ),
    inference(resolution,[status(thm)],[c_6,c_499])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( B_18 = A_17
      | ~ r1_tarski(B_18,A_17)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_404,plain,(
    ! [B_93] :
      ( k1_xboole_0 = B_93
      | ~ r1_tarski(B_93,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_398,c_30])).

tff(c_520,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_510,c_404])).

tff(c_44,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_545,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_44])).

tff(c_549,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_545])).

tff(c_414,plain,(
    ! [B_94] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_36])).

tff(c_565,plain,(
    ! [B_103] : k4_xboole_0(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_414])).

tff(c_576,plain,(
    ! [B_103] : k5_xboole_0(B_103,k1_xboole_0) = k2_xboole_0(B_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_44])).

tff(c_581,plain,(
    ! [B_103] : k5_xboole_0(B_103,k1_xboole_0) = B_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_576])).

tff(c_1364,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_2'(A_183,B_184,C_185),A_183)
      | r2_hidden('#skF_3'(A_183,B_184,C_185),C_185)
      | k4_xboole_0(A_183,B_184) = C_185 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1651,plain,(
    ! [A_208,C_209] :
      ( r2_hidden('#skF_3'(A_208,A_208,C_209),C_209)
      | k4_xboole_0(A_208,A_208) = C_209 ) ),
    inference(resolution,[status(thm)],[c_1364,c_22])).

tff(c_1675,plain,(
    ! [A_208] : k4_xboole_0(A_208,A_208) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1651,c_381])).

tff(c_58,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_897,plain,(
    ! [A_131,B_132] :
      ( k3_xboole_0(k1_tarski(A_131),B_132) = k1_tarski(A_131)
      | ~ r2_hidden(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_58,c_164])).

tff(c_919,plain,(
    ! [A_131,B_132] :
      ( k5_xboole_0(k1_tarski(A_131),k1_tarski(A_131)) = k4_xboole_0(k1_tarski(A_131),B_132)
      | ~ r2_hidden(A_131,B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_36])).

tff(c_936,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(k1_tarski(A_131),k1_tarski(A_131)) = k4_xboole_0(k1_tarski(A_131),B_132)
      | ~ r2_hidden(A_131,B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_919])).

tff(c_10592,plain,(
    ! [A_574,B_575] :
      ( k4_xboole_0(k1_tarski(A_574),B_575) = k1_xboole_0
      | ~ r2_hidden(A_574,B_575) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_936])).

tff(c_10797,plain,(
    ! [B_575,A_574] :
      ( k2_xboole_0(B_575,k1_tarski(A_574)) = k5_xboole_0(B_575,k1_xboole_0)
      | ~ r2_hidden(A_574,B_575) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10592,c_44])).

tff(c_10883,plain,(
    ! [B_576,A_577] :
      ( k2_xboole_0(B_576,k1_tarski(A_577)) = B_576
      | ~ r2_hidden(A_577,B_576) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_10797])).

tff(c_46,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_119,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_203,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(B_65,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_119])).

tff(c_60,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_209,plain,(
    ! [B_65,A_64] : k2_xboole_0(B_65,A_64) = k2_xboole_0(A_64,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_60])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_229,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_62])).

tff(c_10909,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10883,c_229])).

tff(c_10962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.81/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/2.73  
% 7.81/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/2.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.81/2.73  
% 7.81/2.73  %Foreground sorts:
% 7.81/2.73  
% 7.81/2.73  
% 7.81/2.73  %Background operators:
% 7.81/2.73  
% 7.81/2.73  
% 7.81/2.73  %Foreground operators:
% 7.81/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.81/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.81/2.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.81/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.81/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.81/2.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.81/2.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.81/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.81/2.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.81/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.81/2.73  tff('#skF_5', type, '#skF_5': $i).
% 7.81/2.73  tff('#skF_6', type, '#skF_6': $i).
% 7.81/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.81/2.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.81/2.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.81/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.81/2.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.81/2.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.81/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.81/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.81/2.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.81/2.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.81/2.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.81/2.73  
% 7.81/2.75  tff(f_95, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 7.81/2.75  tff(f_66, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.81/2.75  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.81/2.75  tff(f_72, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.81/2.75  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.81/2.75  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.81/2.75  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.81/2.75  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.81/2.75  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.81/2.75  tff(f_74, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.81/2.75  tff(f_88, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.81/2.75  tff(f_76, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.81/2.75  tff(f_90, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.81/2.75  tff(c_64, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.81/2.75  tff(c_38, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.81/2.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.81/2.75  tff(c_42, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.81/2.75  tff(c_34, plain, (![B_18]: (r1_tarski(B_18, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.81/2.75  tff(c_164, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.81/2.75  tff(c_172, plain, (![B_18]: (k3_xboole_0(B_18, B_18)=B_18)), inference(resolution, [status(thm)], [c_34, c_164])).
% 7.81/2.75  tff(c_368, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.81/2.75  tff(c_377, plain, (![B_87, C_88]: (~r1_xboole_0(B_87, B_87) | ~r2_hidden(C_88, B_87))), inference(superposition, [status(thm), theory('equality')], [c_172, c_368])).
% 7.81/2.75  tff(c_381, plain, (![C_88]: (~r2_hidden(C_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_377])).
% 7.81/2.75  tff(c_328, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.81/2.75  tff(c_337, plain, (![B_18]: (k5_xboole_0(B_18, B_18)=k4_xboole_0(B_18, B_18))), inference(superposition, [status(thm), theory('equality')], [c_172, c_328])).
% 7.81/2.75  tff(c_382, plain, (![C_89]: (~r2_hidden(C_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_377])).
% 7.81/2.75  tff(c_398, plain, (![B_93]: (r1_tarski(k1_xboole_0, B_93))), inference(resolution, [status(thm)], [c_6, c_382])).
% 7.81/2.75  tff(c_40, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.81/2.75  tff(c_406, plain, (![B_94]: (k3_xboole_0(k1_xboole_0, B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_398, c_40])).
% 7.81/2.75  tff(c_36, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.81/2.75  tff(c_471, plain, (![B_97]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_97))), inference(superposition, [status(thm), theory('equality')], [c_406, c_36])).
% 7.81/2.75  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.81/2.75  tff(c_483, plain, (![D_11]: (r2_hidden(D_11, k1_xboole_0) | ~r2_hidden(D_11, k5_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_471, c_12])).
% 7.81/2.75  tff(c_495, plain, (![D_11]: (r2_hidden(D_11, k1_xboole_0) | ~r2_hidden(D_11, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_483])).
% 7.81/2.75  tff(c_499, plain, (![D_98]: (~r2_hidden(D_98, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_381, c_495])).
% 7.81/2.75  tff(c_510, plain, (![B_99]: (r1_tarski(k4_xboole_0(k1_xboole_0, k1_xboole_0), B_99))), inference(resolution, [status(thm)], [c_6, c_499])).
% 7.81/2.75  tff(c_30, plain, (![B_18, A_17]: (B_18=A_17 | ~r1_tarski(B_18, A_17) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.81/2.75  tff(c_404, plain, (![B_93]: (k1_xboole_0=B_93 | ~r1_tarski(B_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_398, c_30])).
% 7.81/2.75  tff(c_520, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_510, c_404])).
% 7.81/2.75  tff(c_44, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.81/2.75  tff(c_545, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_520, c_44])).
% 7.81/2.75  tff(c_549, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_545])).
% 7.81/2.75  tff(c_414, plain, (![B_94]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_94))), inference(superposition, [status(thm), theory('equality')], [c_406, c_36])).
% 7.81/2.75  tff(c_565, plain, (![B_103]: (k4_xboole_0(k1_xboole_0, B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_549, c_414])).
% 7.81/2.75  tff(c_576, plain, (![B_103]: (k5_xboole_0(B_103, k1_xboole_0)=k2_xboole_0(B_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_565, c_44])).
% 7.81/2.75  tff(c_581, plain, (![B_103]: (k5_xboole_0(B_103, k1_xboole_0)=B_103)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_576])).
% 7.81/2.75  tff(c_1364, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_2'(A_183, B_184, C_185), A_183) | r2_hidden('#skF_3'(A_183, B_184, C_185), C_185) | k4_xboole_0(A_183, B_184)=C_185)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.81/2.75  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.81/2.75  tff(c_1651, plain, (![A_208, C_209]: (r2_hidden('#skF_3'(A_208, A_208, C_209), C_209) | k4_xboole_0(A_208, A_208)=C_209)), inference(resolution, [status(thm)], [c_1364, c_22])).
% 7.81/2.75  tff(c_1675, plain, (![A_208]: (k4_xboole_0(A_208, A_208)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1651, c_381])).
% 7.81/2.75  tff(c_58, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.81/2.75  tff(c_897, plain, (![A_131, B_132]: (k3_xboole_0(k1_tarski(A_131), B_132)=k1_tarski(A_131) | ~r2_hidden(A_131, B_132))), inference(resolution, [status(thm)], [c_58, c_164])).
% 7.81/2.75  tff(c_919, plain, (![A_131, B_132]: (k5_xboole_0(k1_tarski(A_131), k1_tarski(A_131))=k4_xboole_0(k1_tarski(A_131), B_132) | ~r2_hidden(A_131, B_132))), inference(superposition, [status(thm), theory('equality')], [c_897, c_36])).
% 7.81/2.75  tff(c_936, plain, (![A_131, B_132]: (k4_xboole_0(k1_tarski(A_131), k1_tarski(A_131))=k4_xboole_0(k1_tarski(A_131), B_132) | ~r2_hidden(A_131, B_132))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_919])).
% 7.81/2.75  tff(c_10592, plain, (![A_574, B_575]: (k4_xboole_0(k1_tarski(A_574), B_575)=k1_xboole_0 | ~r2_hidden(A_574, B_575))), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_936])).
% 7.81/2.75  tff(c_10797, plain, (![B_575, A_574]: (k2_xboole_0(B_575, k1_tarski(A_574))=k5_xboole_0(B_575, k1_xboole_0) | ~r2_hidden(A_574, B_575))), inference(superposition, [status(thm), theory('equality')], [c_10592, c_44])).
% 7.81/2.75  tff(c_10883, plain, (![B_576, A_577]: (k2_xboole_0(B_576, k1_tarski(A_577))=B_576 | ~r2_hidden(A_577, B_576))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_10797])).
% 7.81/2.75  tff(c_46, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.81/2.75  tff(c_119, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.81/2.75  tff(c_203, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(B_65, A_64))), inference(superposition, [status(thm), theory('equality')], [c_46, c_119])).
% 7.81/2.75  tff(c_60, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.81/2.75  tff(c_209, plain, (![B_65, A_64]: (k2_xboole_0(B_65, A_64)=k2_xboole_0(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_203, c_60])).
% 7.81/2.75  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.81/2.75  tff(c_229, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_62])).
% 7.81/2.75  tff(c_10909, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10883, c_229])).
% 7.81/2.75  tff(c_10962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_10909])).
% 7.81/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/2.75  
% 7.81/2.75  Inference rules
% 7.81/2.75  ----------------------
% 7.81/2.75  #Ref     : 0
% 7.81/2.75  #Sup     : 2811
% 7.81/2.75  #Fact    : 0
% 7.81/2.75  #Define  : 0
% 7.81/2.75  #Split   : 2
% 7.81/2.75  #Chain   : 0
% 7.81/2.75  #Close   : 0
% 7.81/2.75  
% 7.81/2.75  Ordering : KBO
% 7.81/2.75  
% 7.81/2.75  Simplification rules
% 7.81/2.75  ----------------------
% 7.81/2.75  #Subsume      : 1316
% 7.81/2.75  #Demod        : 1162
% 7.81/2.75  #Tautology    : 661
% 7.81/2.75  #SimpNegUnit  : 30
% 7.81/2.75  #BackRed      : 8
% 7.81/2.75  
% 7.81/2.75  #Partial instantiations: 0
% 7.81/2.75  #Strategies tried      : 1
% 7.81/2.75  
% 7.81/2.75  Timing (in seconds)
% 7.81/2.75  ----------------------
% 7.81/2.75  Preprocessing        : 0.36
% 7.81/2.75  Parsing              : 0.19
% 7.81/2.75  CNF conversion       : 0.03
% 7.81/2.75  Main loop            : 1.60
% 7.81/2.75  Inferencing          : 0.49
% 7.81/2.75  Reduction            : 0.51
% 7.81/2.75  Demodulation         : 0.38
% 7.81/2.75  BG Simplification    : 0.05
% 7.81/2.75  Subsumption          : 0.46
% 7.81/2.75  Abstraction          : 0.07
% 7.81/2.75  MUC search           : 0.00
% 7.81/2.75  Cooper               : 0.00
% 7.81/2.75  Total                : 2.00
% 7.81/2.75  Index Insertion      : 0.00
% 7.81/2.75  Index Deletion       : 0.00
% 7.81/2.75  Index Matching       : 0.00
% 7.81/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
