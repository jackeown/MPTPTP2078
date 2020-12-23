%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:19 EST 2020

% Result     : Theorem 9.19s
% Output     : CNFRefutation 9.40s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 131 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 157 expanded)
%              Number of equality atoms :   41 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_58,plain,(
    ! [C_33] : r2_hidden(C_33,k1_tarski(C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_78,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_312,plain,(
    ! [A_84,B_85] :
      ( k2_xboole_0(k1_tarski(A_84),B_85) = B_85
      | ~ r2_hidden(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_80,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_55,B_56] : k2_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_156,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,k3_xboole_0(A_66,B_65)) = B_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_169,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_6')) = k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_156])).

tff(c_318,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_6')
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_169])).

tff(c_603,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_26,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_151,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_1970,plain,(
    ! [A_188,B_189,C_190] : k2_xboole_0(k3_xboole_0(A_188,B_189),k3_xboole_0(A_188,C_190)) = k3_xboole_0(A_188,k2_xboole_0(B_189,C_190)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8093,plain,(
    ! [B_16351,B_16352,A_16353] : k2_xboole_0(k3_xboole_0(B_16351,B_16352),k3_xboole_0(A_16353,B_16351)) = k3_xboole_0(B_16351,k2_xboole_0(B_16352,A_16353)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1970])).

tff(c_2065,plain,(
    ! [B_2,A_1,C_190] : k2_xboole_0(k3_xboole_0(B_2,A_1),k3_xboole_0(A_1,C_190)) = k3_xboole_0(A_1,k2_xboole_0(B_2,C_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1970])).

tff(c_8320,plain,(
    ! [B_16465,A_16466] : k3_xboole_0(B_16465,k2_xboole_0(A_16466,A_16466)) = k3_xboole_0(A_16466,k2_xboole_0(B_16465,B_16465)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8093,c_2065])).

tff(c_9631,plain,(
    ! [A_17367] : k3_xboole_0(k1_tarski('#skF_6'),k2_xboole_0(A_17367,A_17367)) = k3_xboole_0(A_17367,k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_8320])).

tff(c_2059,plain,(
    ! [C_190] : k3_xboole_0(k1_tarski('#skF_6'),k2_xboole_0(k1_tarski('#skF_7'),C_190)) = k2_xboole_0(k1_tarski('#skF_6'),k3_xboole_0(k1_tarski('#skF_6'),C_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1970])).

tff(c_2091,plain,(
    ! [C_190] : k3_xboole_0(k1_tarski('#skF_6'),k2_xboole_0(k1_tarski('#skF_7'),C_190)) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2059])).

tff(c_9702,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9631,c_2091])).

tff(c_24,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_746,plain,(
    ! [A_125,C_126,B_127] :
      ( r2_hidden(A_125,C_126)
      | ~ r2_hidden(A_125,B_127)
      | r2_hidden(A_125,k5_xboole_0(B_127,C_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13027,plain,(
    ! [A_20402,A_20403,B_20404] :
      ( r2_hidden(A_20402,k3_xboole_0(A_20403,B_20404))
      | ~ r2_hidden(A_20402,A_20403)
      | r2_hidden(A_20402,k4_xboole_0(A_20403,B_20404)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_746])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_368,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,k3_xboole_0(A_87,B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_377,plain,(
    ! [C_89] :
      ( ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7'))
      | ~ r2_hidden(C_89,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_368])).

tff(c_451,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_454,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_451])).

tff(c_456,plain,(
    k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_454])).

tff(c_76,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k1_tarski(A_44),B_45) = B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2092,plain,(
    ! [C_191] : k3_xboole_0(k1_tarski('#skF_6'),k2_xboole_0(k1_tarski('#skF_7'),C_191)) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2059])).

tff(c_2158,plain,(
    ! [B_192] :
      ( k3_xboole_0(k1_tarski('#skF_6'),B_192) = k1_tarski('#skF_6')
      | ~ r2_hidden('#skF_7',B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2092])).

tff(c_30,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_187,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [A_69,B_70] : k3_xboole_0(k4_xboole_0(A_69,B_70),B_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_187])).

tff(c_212,plain,(
    ! [B_2,A_69] : k3_xboole_0(B_2,k4_xboole_0(A_69,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_2202,plain,(
    ! [A_69] :
      ( k1_tarski('#skF_6') = k1_xboole_0
      | ~ r2_hidden('#skF_7',k4_xboole_0(A_69,k1_tarski('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2158,c_212])).

tff(c_2253,plain,(
    ! [A_69] : ~ r2_hidden('#skF_7',k4_xboole_0(A_69,k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_2202])).

tff(c_13168,plain,(
    ! [A_20629] :
      ( r2_hidden('#skF_7',k3_xboole_0(A_20629,k1_tarski('#skF_6')))
      | ~ r2_hidden('#skF_7',A_20629) ) ),
    inference(resolution,[status(thm)],[c_13027,c_2253])).

tff(c_13199,plain,
    ( r2_hidden('#skF_7',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9702,c_13168])).

tff(c_13241,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13199])).

tff(c_13243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_603,c_13241])).

tff(c_13245,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_56,plain,(
    ! [C_33,A_29] :
      ( C_33 = A_29
      | ~ r2_hidden(C_33,k1_tarski(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13273,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_13245,c_56])).

tff(c_13277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_13273])).

tff(c_13280,plain,(
    ! [C_20741] : ~ r2_hidden(C_20741,k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_13285,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_58,c_13280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.19/3.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.08  
% 9.19/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.08  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 9.19/3.08  
% 9.19/3.08  %Foreground sorts:
% 9.19/3.08  
% 9.19/3.08  
% 9.19/3.08  %Background operators:
% 9.19/3.08  
% 9.19/3.08  
% 9.19/3.08  %Foreground operators:
% 9.19/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.19/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.19/3.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.19/3.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.19/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.19/3.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.19/3.08  tff('#skF_7', type, '#skF_7': $i).
% 9.19/3.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.19/3.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.19/3.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.19/3.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.19/3.08  tff('#skF_6', type, '#skF_6': $i).
% 9.19/3.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.19/3.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.19/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.19/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.19/3.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.19/3.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.19/3.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.19/3.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.19/3.08  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.19/3.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.19/3.08  
% 9.40/3.10  tff(f_82, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.40/3.10  tff(f_99, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 9.40/3.10  tff(f_94, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 9.40/3.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.40/3.10  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 9.40/3.10  tff(f_58, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 9.40/3.10  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.40/3.10  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 9.40/3.10  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.40/3.10  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.40/3.10  tff(f_60, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.40/3.10  tff(c_58, plain, (![C_33]: (r2_hidden(C_33, k1_tarski(C_33)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.40/3.10  tff(c_78, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.40/3.10  tff(c_312, plain, (![A_84, B_85]: (k2_xboole_0(k1_tarski(A_84), B_85)=B_85 | ~r2_hidden(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.40/3.10  tff(c_80, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.40/3.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.40/3.10  tff(c_126, plain, (![A_55, B_56]: (k2_xboole_0(A_55, k3_xboole_0(A_55, B_56))=A_55)), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.40/3.10  tff(c_156, plain, (![B_65, A_66]: (k2_xboole_0(B_65, k3_xboole_0(A_66, B_65))=B_65)), inference(superposition, [status(thm), theory('equality')], [c_2, c_126])).
% 9.40/3.10  tff(c_169, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_6'))=k1_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_80, c_156])).
% 9.40/3.10  tff(c_318, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6') | ~r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_312, c_169])).
% 9.40/3.10  tff(c_603, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_318])).
% 9.40/3.10  tff(c_26, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k3_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.40/3.10  tff(c_151, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_80, c_26])).
% 9.40/3.10  tff(c_1970, plain, (![A_188, B_189, C_190]: (k2_xboole_0(k3_xboole_0(A_188, B_189), k3_xboole_0(A_188, C_190))=k3_xboole_0(A_188, k2_xboole_0(B_189, C_190)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.40/3.10  tff(c_8093, plain, (![B_16351, B_16352, A_16353]: (k2_xboole_0(k3_xboole_0(B_16351, B_16352), k3_xboole_0(A_16353, B_16351))=k3_xboole_0(B_16351, k2_xboole_0(B_16352, A_16353)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1970])).
% 9.40/3.10  tff(c_2065, plain, (![B_2, A_1, C_190]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k3_xboole_0(A_1, C_190))=k3_xboole_0(A_1, k2_xboole_0(B_2, C_190)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1970])).
% 9.40/3.10  tff(c_8320, plain, (![B_16465, A_16466]: (k3_xboole_0(B_16465, k2_xboole_0(A_16466, A_16466))=k3_xboole_0(A_16466, k2_xboole_0(B_16465, B_16465)))), inference(superposition, [status(thm), theory('equality')], [c_8093, c_2065])).
% 9.40/3.10  tff(c_9631, plain, (![A_17367]: (k3_xboole_0(k1_tarski('#skF_6'), k2_xboole_0(A_17367, A_17367))=k3_xboole_0(A_17367, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_151, c_8320])).
% 9.40/3.10  tff(c_2059, plain, (![C_190]: (k3_xboole_0(k1_tarski('#skF_6'), k2_xboole_0(k1_tarski('#skF_7'), C_190))=k2_xboole_0(k1_tarski('#skF_6'), k3_xboole_0(k1_tarski('#skF_6'), C_190)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1970])).
% 9.40/3.10  tff(c_2091, plain, (![C_190]: (k3_xboole_0(k1_tarski('#skF_6'), k2_xboole_0(k1_tarski('#skF_7'), C_190))=k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2059])).
% 9.40/3.10  tff(c_9702, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9631, c_2091])).
% 9.40/3.10  tff(c_24, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.40/3.10  tff(c_746, plain, (![A_125, C_126, B_127]: (r2_hidden(A_125, C_126) | ~r2_hidden(A_125, B_127) | r2_hidden(A_125, k5_xboole_0(B_127, C_126)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.40/3.10  tff(c_13027, plain, (![A_20402, A_20403, B_20404]: (r2_hidden(A_20402, k3_xboole_0(A_20403, B_20404)) | ~r2_hidden(A_20402, A_20403) | r2_hidden(A_20402, k4_xboole_0(A_20403, B_20404)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_746])).
% 9.40/3.10  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.40/3.10  tff(c_368, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, k3_xboole_0(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.40/3.10  tff(c_377, plain, (![C_89]: (~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7')) | ~r2_hidden(C_89, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_80, c_368])).
% 9.40/3.10  tff(c_451, plain, (~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_377])).
% 9.40/3.10  tff(c_454, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_451])).
% 9.40/3.10  tff(c_456, plain, (k1_tarski('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_454])).
% 9.40/3.10  tff(c_76, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)=B_45 | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.40/3.10  tff(c_2092, plain, (![C_191]: (k3_xboole_0(k1_tarski('#skF_6'), k2_xboole_0(k1_tarski('#skF_7'), C_191))=k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2059])).
% 9.40/3.10  tff(c_2158, plain, (![B_192]: (k3_xboole_0(k1_tarski('#skF_6'), B_192)=k1_tarski('#skF_6') | ~r2_hidden('#skF_7', B_192))), inference(superposition, [status(thm), theory('equality')], [c_76, c_2092])).
% 9.40/3.10  tff(c_30, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.40/3.10  tff(c_187, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.40/3.10  tff(c_192, plain, (![A_69, B_70]: (k3_xboole_0(k4_xboole_0(A_69, B_70), B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_187])).
% 9.40/3.10  tff(c_212, plain, (![B_2, A_69]: (k3_xboole_0(B_2, k4_xboole_0(A_69, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_192])).
% 9.40/3.10  tff(c_2202, plain, (![A_69]: (k1_tarski('#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_7', k4_xboole_0(A_69, k1_tarski('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_2158, c_212])).
% 9.40/3.10  tff(c_2253, plain, (![A_69]: (~r2_hidden('#skF_7', k4_xboole_0(A_69, k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_456, c_2202])).
% 9.40/3.10  tff(c_13168, plain, (![A_20629]: (r2_hidden('#skF_7', k3_xboole_0(A_20629, k1_tarski('#skF_6'))) | ~r2_hidden('#skF_7', A_20629))), inference(resolution, [status(thm)], [c_13027, c_2253])).
% 9.40/3.10  tff(c_13199, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6')) | ~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_9702, c_13168])).
% 9.40/3.10  tff(c_13241, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13199])).
% 9.40/3.10  tff(c_13243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_603, c_13241])).
% 9.40/3.10  tff(c_13245, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_318])).
% 9.40/3.10  tff(c_56, plain, (![C_33, A_29]: (C_33=A_29 | ~r2_hidden(C_33, k1_tarski(A_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.40/3.10  tff(c_13273, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_13245, c_56])).
% 9.40/3.10  tff(c_13277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_13273])).
% 9.40/3.10  tff(c_13280, plain, (![C_20741]: (~r2_hidden(C_20741, k1_tarski('#skF_6')))), inference(splitRight, [status(thm)], [c_377])).
% 9.40/3.10  tff(c_13285, plain, $false, inference(resolution, [status(thm)], [c_58, c_13280])).
% 9.40/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.40/3.10  
% 9.40/3.10  Inference rules
% 9.40/3.10  ----------------------
% 9.40/3.10  #Ref     : 0
% 9.40/3.10  #Sup     : 2777
% 9.40/3.10  #Fact    : 18
% 9.40/3.10  #Define  : 0
% 9.40/3.10  #Split   : 5
% 9.40/3.10  #Chain   : 0
% 9.40/3.10  #Close   : 0
% 9.40/3.10  
% 9.40/3.10  Ordering : KBO
% 9.40/3.10  
% 9.40/3.10  Simplification rules
% 9.40/3.10  ----------------------
% 9.40/3.10  #Subsume      : 452
% 9.40/3.10  #Demod        : 1338
% 9.40/3.10  #Tautology    : 937
% 9.40/3.10  #SimpNegUnit  : 101
% 9.40/3.10  #BackRed      : 11
% 9.40/3.10  
% 9.40/3.10  #Partial instantiations: 9333
% 9.40/3.10  #Strategies tried      : 1
% 9.40/3.10  
% 9.40/3.10  Timing (in seconds)
% 9.40/3.10  ----------------------
% 9.40/3.10  Preprocessing        : 0.33
% 9.40/3.10  Parsing              : 0.17
% 9.40/3.10  CNF conversion       : 0.03
% 9.40/3.10  Main loop            : 2.00
% 9.40/3.10  Inferencing          : 0.75
% 9.40/3.10  Reduction            : 0.77
% 9.40/3.10  Demodulation         : 0.62
% 9.40/3.10  BG Simplification    : 0.07
% 9.40/3.10  Subsumption          : 0.32
% 9.40/3.10  Abstraction          : 0.08
% 9.40/3.10  MUC search           : 0.00
% 9.40/3.10  Cooper               : 0.00
% 9.40/3.10  Total                : 2.36
% 9.40/3.10  Index Insertion      : 0.00
% 9.40/3.10  Index Deletion       : 0.00
% 9.40/3.10  Index Matching       : 0.00
% 9.40/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
