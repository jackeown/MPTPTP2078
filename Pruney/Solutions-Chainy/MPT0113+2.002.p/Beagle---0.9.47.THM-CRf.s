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
% DateTime   : Thu Dec  3 09:45:11 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 161 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 202 expanded)
%              Number of equality atoms :   52 (  91 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_205,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | k4_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_64,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_209,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_205,c_64])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_211,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_247,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_211])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_252,plain,(
    ! [A_52] : r1_tarski(k1_xboole_0,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_24])).

tff(c_291,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_321,plain,(
    ! [A_57] : k3_xboole_0(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_252,c_291])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_329,plain,(
    ! [A_57] : k3_xboole_0(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_4])).

tff(c_234,plain,(
    ! [A_21,B_22] : k4_xboole_0(k4_xboole_0(A_21,B_22),A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_211])).

tff(c_40,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_320,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_291])).

tff(c_1047,plain,(
    ! [A_100,B_101,C_102] : k4_xboole_0(k3_xboole_0(A_100,B_101),C_102) = k3_xboole_0(A_100,k4_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1301,plain,(
    ! [C_109] : k3_xboole_0('#skF_2',k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_109)) = k4_xboole_0('#skF_2',C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_1047])).

tff(c_1350,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1301])).

tff(c_1363,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_1350])).

tff(c_1365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_1363])).

tff(c_1366,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1369,plain,(
    ! [B_111,A_112] : k2_xboole_0(B_111,A_112) = k2_xboole_0(A_112,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1385,plain,(
    ! [A_112] : k2_xboole_0(k1_xboole_0,A_112) = A_112 ),
    inference(superposition,[status(thm),theory(equality)],[c_1369,c_20])).

tff(c_2218,plain,(
    ! [A_160,B_161] : k2_xboole_0(A_160,k4_xboole_0(B_161,A_160)) = k2_xboole_0(A_160,B_161) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2259,plain,(
    ! [B_161] : k4_xboole_0(B_161,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_1385,c_2218])).

tff(c_2270,plain,(
    ! [B_161] : k4_xboole_0(B_161,k1_xboole_0) = B_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1385,c_2259])).

tff(c_1510,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(A_120,B_121) = k1_xboole_0
      | ~ r1_tarski(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1608,plain,(
    ! [A_124] : k4_xboole_0(A_124,A_124) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_1510])).

tff(c_1619,plain,(
    ! [A_125] : r1_tarski(k1_xboole_0,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_24])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1735,plain,(
    ! [A_129] : k3_xboole_0(k1_xboole_0,A_129) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1619,c_22])).

tff(c_1746,plain,(
    ! [A_129] : k3_xboole_0(A_129,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1735,c_4])).

tff(c_1952,plain,(
    ! [A_143,B_144] : k5_xboole_0(A_143,k3_xboole_0(A_143,B_144)) = k4_xboole_0(A_143,B_144) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1961,plain,(
    ! [A_129] : k5_xboole_0(A_129,k1_xboole_0) = k4_xboole_0(A_129,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1746,c_1952])).

tff(c_3166,plain,(
    ! [A_129] : k5_xboole_0(A_129,k1_xboole_0) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2270,c_1961])).

tff(c_1367,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1550,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(A_122,B_123) = A_122
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1580,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1367,c_1550])).

tff(c_2695,plain,(
    ! [A_175,B_176,C_177] : k4_xboole_0(k3_xboole_0(A_175,B_176),C_177) = k3_xboole_0(A_175,k4_xboole_0(B_176,C_177)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3189,plain,(
    ! [C_192] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_3',C_192)) = k4_xboole_0('#skF_2',C_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_2695])).

tff(c_1583,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_1550])).

tff(c_3223,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3189,c_1583])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1536,plain,(
    ! [A_16,B_17] : k4_xboole_0(k3_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_1510])).

tff(c_2742,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1536,c_2695])).

tff(c_3267,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3223,c_2742])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3310,plain,(
    k5_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3267,c_16])).

tff(c_3331,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3166,c_3310])).

tff(c_1613,plain,(
    ! [A_124] : r1_tarski(k1_xboole_0,A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_24])).

tff(c_1535,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1367,c_1510])).

tff(c_2061,plain,(
    ! [A_148,C_149,B_150] :
      ( r1_xboole_0(A_148,k4_xboole_0(C_149,B_150))
      | ~ r1_tarski(A_148,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2098,plain,(
    ! [A_151] :
      ( r1_xboole_0(A_151,k1_xboole_0)
      | ~ r1_tarski(A_151,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1535,c_2061])).

tff(c_1679,plain,(
    ! [A_126,B_127,C_128] :
      ( ~ r1_xboole_0(A_126,B_127)
      | ~ r2_hidden(C_128,k3_xboole_0(A_126,B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1700,plain,(
    ! [A_5,C_128] :
      ( ~ r1_xboole_0(A_5,A_5)
      | ~ r2_hidden(C_128,A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1679])).

tff(c_2103,plain,(
    ! [C_128] :
      ( ~ r2_hidden(C_128,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2098,c_1700])).

tff(c_2107,plain,(
    ! [C_128] : ~ r2_hidden(C_128,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_2103])).

tff(c_2841,plain,(
    ! [A_179,B_180] : k3_xboole_0(A_179,k4_xboole_0(B_180,A_179)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1536,c_2695])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),k3_xboole_0(A_7,B_8))
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2853,plain,(
    ! [A_179,B_180] :
      ( r2_hidden('#skF_1'(A_179,k4_xboole_0(B_180,A_179)),k1_xboole_0)
      | r1_xboole_0(A_179,k4_xboole_0(B_180,A_179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2841,c_8])).

tff(c_2920,plain,(
    ! [A_179,B_180] : r1_xboole_0(A_179,k4_xboole_0(B_180,A_179)) ),
    inference(negUnitSimplification,[status(thm)],[c_2107,c_2853])).

tff(c_3344,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3331,c_2920])).

tff(c_3367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1366,c_3344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.68  
% 3.68/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.68/1.68  
% 3.68/1.68  %Foreground sorts:
% 3.68/1.68  
% 3.68/1.68  
% 3.68/1.68  %Background operators:
% 3.68/1.68  
% 3.68/1.68  
% 3.68/1.68  %Foreground operators:
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.68/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.68/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.68/1.68  
% 3.68/1.70  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.68/1.70  tff(f_92, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.68/1.70  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.68/1.70  tff(f_53, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.68/1.70  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.68/1.70  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.68/1.70  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.68/1.70  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.68/1.70  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.68/1.70  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.68/1.70  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.68/1.70  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.68/1.70  tff(f_85, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.68/1.70  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.68/1.70  tff(c_205, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | k4_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.68/1.70  tff(c_38, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.70  tff(c_64, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.68/1.70  tff(c_209, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_205, c_64])).
% 3.68/1.70  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.70  tff(c_60, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.70  tff(c_63, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 3.68/1.70  tff(c_211, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.68/1.70  tff(c_247, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_63, c_211])).
% 3.68/1.70  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.68/1.70  tff(c_252, plain, (![A_52]: (r1_tarski(k1_xboole_0, A_52))), inference(superposition, [status(thm), theory('equality')], [c_247, c_24])).
% 3.68/1.70  tff(c_291, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.68/1.70  tff(c_321, plain, (![A_57]: (k3_xboole_0(k1_xboole_0, A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_252, c_291])).
% 3.68/1.70  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.68/1.70  tff(c_329, plain, (![A_57]: (k3_xboole_0(A_57, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_321, c_4])).
% 3.68/1.70  tff(c_234, plain, (![A_21, B_22]: (k4_xboole_0(k4_xboole_0(A_21, B_22), A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_211])).
% 3.68/1.70  tff(c_40, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.70  tff(c_320, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_291])).
% 3.68/1.70  tff(c_1047, plain, (![A_100, B_101, C_102]: (k4_xboole_0(k3_xboole_0(A_100, B_101), C_102)=k3_xboole_0(A_100, k4_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.68/1.70  tff(c_1301, plain, (![C_109]: (k3_xboole_0('#skF_2', k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_109))=k4_xboole_0('#skF_2', C_109))), inference(superposition, [status(thm), theory('equality')], [c_320, c_1047])).
% 3.68/1.70  tff(c_1350, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_234, c_1301])).
% 3.68/1.70  tff(c_1363, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_329, c_1350])).
% 3.68/1.70  tff(c_1365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_1363])).
% 3.68/1.70  tff(c_1366, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 3.68/1.70  tff(c_1369, plain, (![B_111, A_112]: (k2_xboole_0(B_111, A_112)=k2_xboole_0(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.70  tff(c_20, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.68/1.70  tff(c_1385, plain, (![A_112]: (k2_xboole_0(k1_xboole_0, A_112)=A_112)), inference(superposition, [status(thm), theory('equality')], [c_1369, c_20])).
% 3.68/1.70  tff(c_2218, plain, (![A_160, B_161]: (k2_xboole_0(A_160, k4_xboole_0(B_161, A_160))=k2_xboole_0(A_160, B_161))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.68/1.70  tff(c_2259, plain, (![B_161]: (k4_xboole_0(B_161, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_161))), inference(superposition, [status(thm), theory('equality')], [c_1385, c_2218])).
% 3.68/1.70  tff(c_2270, plain, (![B_161]: (k4_xboole_0(B_161, k1_xboole_0)=B_161)), inference(demodulation, [status(thm), theory('equality')], [c_1385, c_2259])).
% 3.68/1.70  tff(c_1510, plain, (![A_120, B_121]: (k4_xboole_0(A_120, B_121)=k1_xboole_0 | ~r1_tarski(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.68/1.70  tff(c_1608, plain, (![A_124]: (k4_xboole_0(A_124, A_124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_63, c_1510])).
% 3.68/1.70  tff(c_1619, plain, (![A_125]: (r1_tarski(k1_xboole_0, A_125))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_24])).
% 3.68/1.70  tff(c_22, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.68/1.70  tff(c_1735, plain, (![A_129]: (k3_xboole_0(k1_xboole_0, A_129)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1619, c_22])).
% 3.68/1.70  tff(c_1746, plain, (![A_129]: (k3_xboole_0(A_129, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1735, c_4])).
% 3.68/1.70  tff(c_1952, plain, (![A_143, B_144]: (k5_xboole_0(A_143, k3_xboole_0(A_143, B_144))=k4_xboole_0(A_143, B_144))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.68/1.70  tff(c_1961, plain, (![A_129]: (k5_xboole_0(A_129, k1_xboole_0)=k4_xboole_0(A_129, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1746, c_1952])).
% 3.68/1.70  tff(c_3166, plain, (![A_129]: (k5_xboole_0(A_129, k1_xboole_0)=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_2270, c_1961])).
% 3.68/1.70  tff(c_1367, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.68/1.70  tff(c_1550, plain, (![A_122, B_123]: (k3_xboole_0(A_122, B_123)=A_122 | ~r1_tarski(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.68/1.70  tff(c_1580, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_1367, c_1550])).
% 3.68/1.70  tff(c_2695, plain, (![A_175, B_176, C_177]: (k4_xboole_0(k3_xboole_0(A_175, B_176), C_177)=k3_xboole_0(A_175, k4_xboole_0(B_176, C_177)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.68/1.70  tff(c_3189, plain, (![C_192]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', C_192))=k4_xboole_0('#skF_2', C_192))), inference(superposition, [status(thm), theory('equality')], [c_1580, c_2695])).
% 3.68/1.70  tff(c_1583, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_1550])).
% 3.68/1.70  tff(c_3223, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3189, c_1583])).
% 3.68/1.70  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.70  tff(c_1536, plain, (![A_16, B_17]: (k4_xboole_0(k3_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1510])).
% 3.68/1.70  tff(c_2742, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1536, c_2695])).
% 3.68/1.70  tff(c_3267, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3223, c_2742])).
% 3.68/1.70  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.68/1.70  tff(c_3310, plain, (k5_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3267, c_16])).
% 3.68/1.70  tff(c_3331, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3166, c_3310])).
% 3.68/1.70  tff(c_1613, plain, (![A_124]: (r1_tarski(k1_xboole_0, A_124))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_24])).
% 3.68/1.70  tff(c_1535, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1367, c_1510])).
% 3.68/1.70  tff(c_2061, plain, (![A_148, C_149, B_150]: (r1_xboole_0(A_148, k4_xboole_0(C_149, B_150)) | ~r1_tarski(A_148, B_150))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.68/1.70  tff(c_2098, plain, (![A_151]: (r1_xboole_0(A_151, k1_xboole_0) | ~r1_tarski(A_151, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1535, c_2061])).
% 3.68/1.70  tff(c_1679, plain, (![A_126, B_127, C_128]: (~r1_xboole_0(A_126, B_127) | ~r2_hidden(C_128, k3_xboole_0(A_126, B_127)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.68/1.70  tff(c_1700, plain, (![A_5, C_128]: (~r1_xboole_0(A_5, A_5) | ~r2_hidden(C_128, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1679])).
% 3.68/1.70  tff(c_2103, plain, (![C_128]: (~r2_hidden(C_128, k1_xboole_0) | ~r1_tarski(k1_xboole_0, '#skF_3'))), inference(resolution, [status(thm)], [c_2098, c_1700])).
% 3.68/1.70  tff(c_2107, plain, (![C_128]: (~r2_hidden(C_128, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_2103])).
% 3.68/1.70  tff(c_2841, plain, (![A_179, B_180]: (k3_xboole_0(A_179, k4_xboole_0(B_180, A_179))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1536, c_2695])).
% 3.68/1.70  tff(c_8, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), k3_xboole_0(A_7, B_8)) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.68/1.70  tff(c_2853, plain, (![A_179, B_180]: (r2_hidden('#skF_1'(A_179, k4_xboole_0(B_180, A_179)), k1_xboole_0) | r1_xboole_0(A_179, k4_xboole_0(B_180, A_179)))), inference(superposition, [status(thm), theory('equality')], [c_2841, c_8])).
% 3.68/1.70  tff(c_2920, plain, (![A_179, B_180]: (r1_xboole_0(A_179, k4_xboole_0(B_180, A_179)))), inference(negUnitSimplification, [status(thm)], [c_2107, c_2853])).
% 3.68/1.70  tff(c_3344, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3331, c_2920])).
% 3.68/1.70  tff(c_3367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1366, c_3344])).
% 3.68/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.70  
% 3.68/1.70  Inference rules
% 3.68/1.70  ----------------------
% 3.68/1.70  #Ref     : 0
% 3.68/1.70  #Sup     : 834
% 3.68/1.70  #Fact    : 0
% 3.68/1.70  #Define  : 0
% 3.68/1.70  #Split   : 6
% 3.68/1.70  #Chain   : 0
% 3.68/1.70  #Close   : 0
% 3.68/1.70  
% 3.68/1.70  Ordering : KBO
% 3.68/1.70  
% 3.68/1.70  Simplification rules
% 3.68/1.70  ----------------------
% 3.68/1.70  #Subsume      : 36
% 3.68/1.70  #Demod        : 427
% 3.68/1.70  #Tautology    : 586
% 3.68/1.70  #SimpNegUnit  : 13
% 3.68/1.70  #BackRed      : 2
% 3.68/1.70  
% 3.68/1.70  #Partial instantiations: 0
% 3.68/1.70  #Strategies tried      : 1
% 3.68/1.70  
% 3.68/1.70  Timing (in seconds)
% 3.68/1.70  ----------------------
% 3.68/1.70  Preprocessing        : 0.29
% 3.68/1.70  Parsing              : 0.16
% 3.68/1.70  CNF conversion       : 0.02
% 3.68/1.70  Main loop            : 0.60
% 3.68/1.70  Inferencing          : 0.21
% 3.68/1.70  Reduction            : 0.23
% 3.68/1.70  Demodulation         : 0.18
% 3.68/1.70  BG Simplification    : 0.02
% 3.68/1.70  Subsumption          : 0.09
% 3.68/1.70  Abstraction          : 0.03
% 3.68/1.70  MUC search           : 0.00
% 3.68/1.70  Cooper               : 0.00
% 3.68/1.70  Total                : 0.94
% 3.68/1.70  Index Insertion      : 0.00
% 3.68/1.70  Index Deletion       : 0.00
% 3.68/1.70  Index Matching       : 0.00
% 3.68/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
