%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:37 EST 2020

% Result     : Theorem 6.07s
% Output     : CNFRefutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 696 expanded)
%              Number of leaves         :   33 ( 247 expanded)
%              Depth                    :   18
%              Number of atoms          :   84 ( 783 expanded)
%              Number of equality atoms :   60 ( 573 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_69,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_338,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_356,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_762,plain,(
    ! [A_98,B_99] : k5_xboole_0(k5_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)) = k2_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] : k5_xboole_0(k5_xboole_0(A_17,B_18),C_19) = k5_xboole_0(A_17,k5_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_774,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k5_xboole_0(B_99,k3_xboole_0(A_98,B_99))) = k2_xboole_0(A_98,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_24])).

tff(c_823,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k4_xboole_0(B_99,A_98)) = k2_xboole_0(A_98,B_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_774])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_543,plain,(
    ! [A_87,B_88,C_89] : k5_xboole_0(k5_xboole_0(A_87,B_88),C_89) = k5_xboole_0(A_87,k5_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ! [A_36] : r1_tarski(A_36,k1_zfmisc_1(k3_tarski(A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_119,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_zfmisc_1(k3_tarski(A_36))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_119])).

tff(c_216,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_227,plain,(
    ! [A_36] : k3_xboole_0(A_36,k1_zfmisc_1(k3_tarski(A_36))) = A_36 ),
    inference(resolution,[status(thm)],[c_42,c_216])).

tff(c_347,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_zfmisc_1(k3_tarski(A_36))) = k5_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_338])).

tff(c_362,plain,(
    ! [A_36] : k5_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_347])).

tff(c_557,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k5_xboole_0(B_88,k5_xboole_0(A_87,B_88))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_362])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_229,plain,(
    ! [A_63] : k3_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_216])).

tff(c_234,plain,(
    ! [A_63] : k3_xboole_0(A_63,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2])).

tff(c_350,plain,(
    ! [A_63] : k5_xboole_0(A_63,k1_xboole_0) = k4_xboole_0(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_338])).

tff(c_363,plain,(
    ! [A_63] : k4_xboole_0(A_63,k1_xboole_0) = A_63 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_350])).

tff(c_1051,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k4_xboole_0(B_113,A_112)) = k2_xboole_0(A_112,B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_774])).

tff(c_1094,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,A_63) = k2_xboole_0(k1_xboole_0,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_1051])).

tff(c_581,plain,(
    ! [A_36,C_89] : k5_xboole_0(A_36,k5_xboole_0(A_36,C_89)) = k5_xboole_0(k1_xboole_0,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_543])).

tff(c_1579,plain,(
    ! [A_125,C_126] : k5_xboole_0(A_125,k5_xboole_0(A_125,C_126)) = k2_xboole_0(k1_xboole_0,C_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_581])).

tff(c_1655,plain,(
    ! [A_36] : k5_xboole_0(A_36,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_1579])).

tff(c_1676,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1655])).

tff(c_1578,plain,(
    ! [A_36,C_89] : k5_xboole_0(A_36,k5_xboole_0(A_36,C_89)) = k2_xboole_0(k1_xboole_0,C_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_581])).

tff(c_1827,plain,(
    ! [A_129,C_130] : k5_xboole_0(A_129,k5_xboole_0(A_129,C_130)) = C_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1578])).

tff(c_1874,plain,(
    ! [B_88,A_87] : k5_xboole_0(B_88,k5_xboole_0(A_87,B_88)) = k5_xboole_0(A_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_1827])).

tff(c_2049,plain,(
    ! [B_134,A_135] : k5_xboole_0(B_134,k5_xboole_0(A_135,B_134)) = A_135 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1874])).

tff(c_1679,plain,(
    ! [A_36,C_89] : k5_xboole_0(A_36,k5_xboole_0(A_36,C_89)) = C_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1578])).

tff(c_2061,plain,(
    ! [B_134,A_135] : k5_xboole_0(B_134,A_135) = k5_xboole_0(A_135,B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_2049,c_1679])).

tff(c_320,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tarski(A_68),B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_330,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(k1_tarski(A_68),B_69) = k1_tarski(A_68)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_320,c_10])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2802,plain,(
    ! [A_147,B_148,C_149] : k5_xboole_0(A_147,k5_xboole_0(k3_xboole_0(A_147,B_148),C_149)) = k5_xboole_0(k4_xboole_0(A_147,B_148),C_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_543])).

tff(c_2902,plain,(
    ! [A_147,B_148] : k5_xboole_0(k4_xboole_0(A_147,B_148),k3_xboole_0(A_147,B_148)) = k5_xboole_0(A_147,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_2802])).

tff(c_3531,plain,(
    ! [A_162,B_163] : k5_xboole_0(k4_xboole_0(A_162,B_163),k3_xboole_0(A_162,B_163)) = A_162 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2902])).

tff(c_3657,plain,(
    ! [A_164,B_165] : k5_xboole_0(k4_xboole_0(A_164,B_165),k3_xboole_0(B_165,A_164)) = A_164 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3531])).

tff(c_3725,plain,(
    ! [B_69,A_68] :
      ( k5_xboole_0(k4_xboole_0(B_69,k1_tarski(A_68)),k1_tarski(A_68)) = B_69
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_3657])).

tff(c_3778,plain,(
    ! [A_68,B_69] :
      ( k2_xboole_0(k1_tarski(A_68),B_69) = B_69
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_2061,c_3725])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = A_45
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_105,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_2649,plain,(
    ! [A_144,B_145] : k5_xboole_0(A_144,k4_xboole_0(A_144,B_145)) = k3_xboole_0(A_144,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1827])).

tff(c_2718,plain,(
    ! [A_13,B_14] : k5_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2649])).

tff(c_2940,plain,(
    ! [B_150,A_151] : k3_xboole_0(B_150,k4_xboole_0(A_151,B_150)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_2,c_2718])).

tff(c_817,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),k3_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_762])).

tff(c_2948,plain,(
    ! [A_151,B_150] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_151,B_150),B_150),k1_xboole_0) = k2_xboole_0(k4_xboole_0(A_151,B_150),B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_2940,c_817])).

tff(c_3003,plain,(
    ! [A_151,B_150] : k2_xboole_0(k4_xboole_0(A_151,B_150),B_150) = k2_xboole_0(B_150,A_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_16,c_2061,c_2948])).

tff(c_44,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7850,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_44])).

tff(c_7943,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_7850])).

tff(c_7947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7943])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.07/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.43  
% 6.18/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.18/2.44  
% 6.18/2.44  %Foreground sorts:
% 6.18/2.44  
% 6.18/2.44  
% 6.18/2.44  %Background operators:
% 6.18/2.44  
% 6.18/2.44  
% 6.18/2.44  %Foreground operators:
% 6.18/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.18/2.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.18/2.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.18/2.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.18/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.18/2.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.18/2.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.18/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.18/2.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.18/2.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.18/2.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.18/2.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.18/2.44  tff('#skF_2', type, '#skF_2': $i).
% 6.18/2.44  tff('#skF_1', type, '#skF_1': $i).
% 6.18/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.18/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.18/2.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.18/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.18/2.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.18/2.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.18/2.44  
% 6.18/2.45  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 6.18/2.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.18/2.45  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.18/2.45  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.18/2.45  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.18/2.45  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.18/2.45  tff(f_69, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 6.18/2.45  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.18/2.45  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.18/2.45  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.18/2.45  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.18/2.45  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.18/2.45  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.18/2.45  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.18/2.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.18/2.45  tff(c_338, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.18/2.45  tff(c_356, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_338])).
% 6.18/2.45  tff(c_762, plain, (![A_98, B_99]: (k5_xboole_0(k5_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99))=k2_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.18/2.45  tff(c_24, plain, (![A_17, B_18, C_19]: (k5_xboole_0(k5_xboole_0(A_17, B_18), C_19)=k5_xboole_0(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.18/2.45  tff(c_774, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k5_xboole_0(B_99, k3_xboole_0(A_98, B_99)))=k2_xboole_0(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_762, c_24])).
% 6.18/2.45  tff(c_823, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k4_xboole_0(B_99, A_98))=k2_xboole_0(A_98, B_99))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_774])).
% 6.18/2.45  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.18/2.45  tff(c_543, plain, (![A_87, B_88, C_89]: (k5_xboole_0(k5_xboole_0(A_87, B_88), C_89)=k5_xboole_0(A_87, k5_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.18/2.45  tff(c_42, plain, (![A_36]: (r1_tarski(A_36, k1_zfmisc_1(k3_tarski(A_36))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.18/2.45  tff(c_119, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.18/2.45  tff(c_130, plain, (![A_36]: (k4_xboole_0(A_36, k1_zfmisc_1(k3_tarski(A_36)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_119])).
% 6.18/2.45  tff(c_216, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.18/2.45  tff(c_227, plain, (![A_36]: (k3_xboole_0(A_36, k1_zfmisc_1(k3_tarski(A_36)))=A_36)), inference(resolution, [status(thm)], [c_42, c_216])).
% 6.18/2.45  tff(c_347, plain, (![A_36]: (k4_xboole_0(A_36, k1_zfmisc_1(k3_tarski(A_36)))=k5_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_227, c_338])).
% 6.18/2.45  tff(c_362, plain, (![A_36]: (k5_xboole_0(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_347])).
% 6.18/2.45  tff(c_557, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k5_xboole_0(B_88, k5_xboole_0(A_87, B_88)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_543, c_362])).
% 6.18/2.45  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.45  tff(c_229, plain, (![A_63]: (k3_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_216])).
% 6.18/2.45  tff(c_234, plain, (![A_63]: (k3_xboole_0(A_63, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_2])).
% 6.18/2.45  tff(c_350, plain, (![A_63]: (k5_xboole_0(A_63, k1_xboole_0)=k4_xboole_0(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_338])).
% 6.18/2.45  tff(c_363, plain, (![A_63]: (k4_xboole_0(A_63, k1_xboole_0)=A_63)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_350])).
% 6.18/2.45  tff(c_1051, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k4_xboole_0(B_113, A_112))=k2_xboole_0(A_112, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_774])).
% 6.18/2.45  tff(c_1094, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, A_63)=k2_xboole_0(k1_xboole_0, A_63))), inference(superposition, [status(thm), theory('equality')], [c_363, c_1051])).
% 6.18/2.45  tff(c_581, plain, (![A_36, C_89]: (k5_xboole_0(A_36, k5_xboole_0(A_36, C_89))=k5_xboole_0(k1_xboole_0, C_89))), inference(superposition, [status(thm), theory('equality')], [c_362, c_543])).
% 6.18/2.45  tff(c_1579, plain, (![A_125, C_126]: (k5_xboole_0(A_125, k5_xboole_0(A_125, C_126))=k2_xboole_0(k1_xboole_0, C_126))), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_581])).
% 6.18/2.45  tff(c_1655, plain, (![A_36]: (k5_xboole_0(A_36, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_36))), inference(superposition, [status(thm), theory('equality')], [c_362, c_1579])).
% 6.18/2.45  tff(c_1676, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1655])).
% 6.18/2.45  tff(c_1578, plain, (![A_36, C_89]: (k5_xboole_0(A_36, k5_xboole_0(A_36, C_89))=k2_xboole_0(k1_xboole_0, C_89))), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_581])).
% 6.18/2.45  tff(c_1827, plain, (![A_129, C_130]: (k5_xboole_0(A_129, k5_xboole_0(A_129, C_130))=C_130)), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1578])).
% 6.18/2.45  tff(c_1874, plain, (![B_88, A_87]: (k5_xboole_0(B_88, k5_xboole_0(A_87, B_88))=k5_xboole_0(A_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_557, c_1827])).
% 6.18/2.45  tff(c_2049, plain, (![B_134, A_135]: (k5_xboole_0(B_134, k5_xboole_0(A_135, B_134))=A_135)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1874])).
% 6.18/2.45  tff(c_1679, plain, (![A_36, C_89]: (k5_xboole_0(A_36, k5_xboole_0(A_36, C_89))=C_89)), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1578])).
% 6.18/2.45  tff(c_2061, plain, (![B_134, A_135]: (k5_xboole_0(B_134, A_135)=k5_xboole_0(A_135, B_134))), inference(superposition, [status(thm), theory('equality')], [c_2049, c_1679])).
% 6.18/2.45  tff(c_320, plain, (![A_68, B_69]: (r1_tarski(k1_tarski(A_68), B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.18/2.45  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.18/2.45  tff(c_330, plain, (![A_68, B_69]: (k3_xboole_0(k1_tarski(A_68), B_69)=k1_tarski(A_68) | ~r2_hidden(A_68, B_69))), inference(resolution, [status(thm)], [c_320, c_10])).
% 6.18/2.45  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.18/2.45  tff(c_2802, plain, (![A_147, B_148, C_149]: (k5_xboole_0(A_147, k5_xboole_0(k3_xboole_0(A_147, B_148), C_149))=k5_xboole_0(k4_xboole_0(A_147, B_148), C_149))), inference(superposition, [status(thm), theory('equality')], [c_8, c_543])).
% 6.18/2.45  tff(c_2902, plain, (![A_147, B_148]: (k5_xboole_0(k4_xboole_0(A_147, B_148), k3_xboole_0(A_147, B_148))=k5_xboole_0(A_147, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_362, c_2802])).
% 6.18/2.45  tff(c_3531, plain, (![A_162, B_163]: (k5_xboole_0(k4_xboole_0(A_162, B_163), k3_xboole_0(A_162, B_163))=A_162)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2902])).
% 6.18/2.45  tff(c_3657, plain, (![A_164, B_165]: (k5_xboole_0(k4_xboole_0(A_164, B_165), k3_xboole_0(B_165, A_164))=A_164)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3531])).
% 6.18/2.45  tff(c_3725, plain, (![B_69, A_68]: (k5_xboole_0(k4_xboole_0(B_69, k1_tarski(A_68)), k1_tarski(A_68))=B_69 | ~r2_hidden(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_330, c_3657])).
% 6.18/2.45  tff(c_3778, plain, (![A_68, B_69]: (k2_xboole_0(k1_tarski(A_68), B_69)=B_69 | ~r2_hidden(A_68, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_823, c_2061, c_3725])).
% 6.18/2.45  tff(c_18, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.18/2.45  tff(c_101, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=A_45 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.18/2.45  tff(c_105, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_101])).
% 6.18/2.45  tff(c_2649, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k4_xboole_0(A_144, B_145))=k3_xboole_0(A_144, B_145))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1827])).
% 6.18/2.45  tff(c_2718, plain, (![A_13, B_14]: (k5_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=k3_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(superposition, [status(thm), theory('equality')], [c_105, c_2649])).
% 6.18/2.45  tff(c_2940, plain, (![B_150, A_151]: (k3_xboole_0(B_150, k4_xboole_0(A_151, B_150))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_362, c_2, c_2718])).
% 6.18/2.45  tff(c_817, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), k3_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_762])).
% 6.18/2.45  tff(c_2948, plain, (![A_151, B_150]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_151, B_150), B_150), k1_xboole_0)=k2_xboole_0(k4_xboole_0(A_151, B_150), B_150))), inference(superposition, [status(thm), theory('equality')], [c_2940, c_817])).
% 6.18/2.45  tff(c_3003, plain, (![A_151, B_150]: (k2_xboole_0(k4_xboole_0(A_151, B_150), B_150)=k2_xboole_0(B_150, A_151))), inference(demodulation, [status(thm), theory('equality')], [c_823, c_16, c_2061, c_2948])).
% 6.18/2.45  tff(c_44, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.18/2.45  tff(c_7850, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_44])).
% 6.18/2.45  tff(c_7943, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3778, c_7850])).
% 6.18/2.45  tff(c_7947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_7943])).
% 6.18/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.45  
% 6.18/2.45  Inference rules
% 6.18/2.45  ----------------------
% 6.18/2.45  #Ref     : 0
% 6.18/2.45  #Sup     : 1952
% 6.18/2.45  #Fact    : 0
% 6.18/2.45  #Define  : 0
% 6.18/2.45  #Split   : 1
% 6.18/2.45  #Chain   : 0
% 6.18/2.45  #Close   : 0
% 6.18/2.45  
% 6.18/2.45  Ordering : KBO
% 6.18/2.45  
% 6.18/2.45  Simplification rules
% 6.18/2.45  ----------------------
% 6.18/2.45  #Subsume      : 76
% 6.18/2.45  #Demod        : 2307
% 6.18/2.45  #Tautology    : 1026
% 6.18/2.45  #SimpNegUnit  : 0
% 6.18/2.45  #BackRed      : 9
% 6.18/2.45  
% 6.18/2.45  #Partial instantiations: 0
% 6.18/2.45  #Strategies tried      : 1
% 6.18/2.45  
% 6.18/2.45  Timing (in seconds)
% 6.18/2.45  ----------------------
% 6.18/2.46  Preprocessing        : 0.32
% 6.18/2.46  Parsing              : 0.17
% 6.18/2.46  CNF conversion       : 0.02
% 6.18/2.46  Main loop            : 1.34
% 6.18/2.46  Inferencing          : 0.36
% 6.18/2.46  Reduction            : 0.69
% 6.18/2.46  Demodulation         : 0.59
% 6.18/2.46  BG Simplification    : 0.05
% 6.18/2.46  Subsumption          : 0.16
% 6.18/2.46  Abstraction          : 0.08
% 6.18/2.46  MUC search           : 0.00
% 6.18/2.46  Cooper               : 0.00
% 6.18/2.46  Total                : 1.70
% 6.18/2.46  Index Insertion      : 0.00
% 6.18/2.46  Index Deletion       : 0.00
% 6.18/2.46  Index Matching       : 0.00
% 6.18/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
