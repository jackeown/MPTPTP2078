%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:41 EST 2020

% Result     : Theorem 11.03s
% Output     : CNFRefutation 11.16s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 307 expanded)
%              Number of leaves         :   42 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 641 expanded)
%              Number of equality atoms :  160 ( 481 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_132,plain,(
    ! [A_79,B_80] : k1_enumset1(A_79,A_79,B_80) = k2_tarski(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_150,plain,(
    ! [B_81,A_82] : r2_hidden(B_81,k2_tarski(A_82,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_10])).

tff(c_153,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_150])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16334,plain,(
    ! [A_7487,B_7488] : k4_xboole_0(A_7487,k4_xboole_0(A_7487,B_7488)) = k3_xboole_0(A_7487,B_7488) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16349,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_16334])).

tff(c_16352,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16349])).

tff(c_32607,plain,(
    ! [B_15004,A_15005] :
      ( ~ r2_hidden(B_15004,A_15005)
      | k4_xboole_0(A_15005,k1_tarski(B_15004)) != A_15005 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32614,plain,(
    ! [B_15004] :
      ( ~ r2_hidden(B_15004,k1_tarski(B_15004))
      | k1_tarski(B_15004) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16352,c_32607])).

tff(c_32617,plain,(
    ! [B_15004] : k1_tarski(B_15004) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_32614])).

tff(c_54,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_3'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,k1_tarski(B_16)) = A_15
      | r2_hidden(B_16,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32876,plain,(
    ! [A_15068,C_15069,B_15070] :
      ( ~ r2_hidden(A_15068,C_15069)
      | k4_xboole_0(k2_tarski(A_15068,B_15070),C_15069) != k2_tarski(A_15068,B_15070) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32970,plain,(
    ! [A_15086,B_15087,B_15088] :
      ( ~ r2_hidden(A_15086,k1_tarski(B_15087))
      | r2_hidden(B_15087,k2_tarski(A_15086,B_15088)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_32876])).

tff(c_32979,plain,(
    ! [B_15087,B_15088] :
      ( r2_hidden(B_15087,k2_tarski('#skF_3'(k1_tarski(B_15087)),B_15088))
      | k1_tarski(B_15087) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_32970])).

tff(c_32986,plain,(
    ! [B_15087,B_15088] : r2_hidden(B_15087,k2_tarski('#skF_3'(k1_tarski(B_15087)),B_15088)) ),
    inference(negUnitSimplification,[status(thm)],[c_32617,c_32979])).

tff(c_34,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32927,plain,(
    ! [E_15080,C_15081,B_15082,A_15083] :
      ( E_15080 = C_15081
      | E_15080 = B_15082
      | E_15080 = A_15083
      | ~ r2_hidden(E_15080,k1_enumset1(A_15083,B_15082,C_15081)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_33260,plain,(
    ! [E_15165,B_15166,A_15167] :
      ( E_15165 = B_15166
      | E_15165 = A_15167
      | E_15165 = A_15167
      | ~ r2_hidden(E_15165,k2_tarski(A_15167,B_15166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_32927])).

tff(c_33292,plain,(
    ! [B_15088,B_15087] :
      ( B_15088 = B_15087
      | '#skF_3'(k1_tarski(B_15087)) = B_15087 ) ),
    inference(resolution,[status(thm)],[c_32986,c_33260])).

tff(c_33322,plain,(
    ! [B_15087] : '#skF_3'(k1_tarski(B_15087)) = B_15087 ),
    inference(factorization,[status(thm),theory(equality)],[c_33292])).

tff(c_32693,plain,(
    ! [B_15024,C_15025,A_15026] :
      ( ~ r2_hidden(B_15024,C_15025)
      | k4_xboole_0(k2_tarski(A_15026,B_15024),C_15025) != k2_tarski(A_15026,B_15024) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32737,plain,(
    ! [B_15033,B_15034,A_15035] :
      ( ~ r2_hidden(B_15033,k1_tarski(B_15034))
      | r2_hidden(B_15034,k2_tarski(A_15035,B_15033)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_32693])).

tff(c_32742,plain,(
    ! [B_15034,A_15035] :
      ( r2_hidden(B_15034,k2_tarski(A_15035,'#skF_3'(k1_tarski(B_15034))))
      | k1_tarski(B_15034) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_32737])).

tff(c_32748,plain,(
    ! [B_15036,A_15037] : r2_hidden(B_15036,k2_tarski(A_15037,'#skF_3'(k1_tarski(B_15036)))) ),
    inference(negUnitSimplification,[status(thm)],[c_32617,c_32742])).

tff(c_32752,plain,(
    ! [B_15036] : r2_hidden(B_15036,k1_tarski('#skF_3'(k1_tarski(B_15036)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_32748])).

tff(c_32805,plain,(
    ! [D_15048,A_15049,C_15050,E_15051] :
      ( ~ r2_hidden(D_15048,A_15049)
      | k3_mcart_1(C_15050,D_15048,E_15051) != '#skF_3'(A_15049)
      | k1_xboole_0 = A_15049 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32809,plain,(
    ! [C_15050,B_15036,E_15051] :
      ( k3_mcart_1(C_15050,B_15036,E_15051) != '#skF_3'(k1_tarski('#skF_3'(k1_tarski(B_15036))))
      | k1_tarski('#skF_3'(k1_tarski(B_15036))) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32752,c_32805])).

tff(c_32831,plain,(
    ! [C_15050,B_15036,E_15051] : k3_mcart_1(C_15050,B_15036,E_15051) != '#skF_3'(k1_tarski('#skF_3'(k1_tarski(B_15036)))) ),
    inference(negUnitSimplification,[status(thm)],[c_32617,c_32809])).

tff(c_48138,plain,(
    ! [C_15050,B_15036,E_15051] : k3_mcart_1(C_15050,B_15036,E_15051) != B_15036 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33322,c_33322,c_32831])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_16471,plain,(
    ! [A_7501,B_7502,C_7503] : k4_tarski(k4_tarski(A_7501,B_7502),C_7503) = k3_mcart_1(A_7501,B_7502,C_7503) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    ! [A_55,B_56] : k2_mcart_1(k4_tarski(A_55,B_56)) = B_56 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    ! [B_29,C_30] : k2_mcart_1(k4_tarski(B_29,C_30)) != k4_tarski(B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_82,plain,(
    ! [B_29,C_30] : k4_tarski(B_29,C_30) != C_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_50])).

tff(c_16489,plain,(
    ! [A_7501,B_7502,C_7503] : k3_mcart_1(A_7501,B_7502,C_7503) != C_7503 ),
    inference(superposition,[status(thm),theory(equality)],[c_16471,c_82])).

tff(c_166,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_166])).

tff(c_184,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_225,plain,(
    ! [B_90,A_91] :
      ( ~ r2_hidden(B_90,A_91)
      | k4_xboole_0(A_91,k1_tarski(B_90)) != A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_229,plain,(
    ! [B_90] :
      ( ~ r2_hidden(B_90,k1_tarski(B_90))
      | k1_tarski(B_90) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_225])).

tff(c_231,plain,(
    ! [B_90] : k1_tarski(B_90) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_229])).

tff(c_345,plain,(
    ! [A_115,C_116,B_117] :
      ( ~ r2_hidden(A_115,C_116)
      | k4_xboole_0(k2_tarski(A_115,B_117),C_116) != k2_tarski(A_115,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_613,plain,(
    ! [A_171,B_172,B_173] :
      ( ~ r2_hidden(A_171,k1_tarski(B_172))
      | r2_hidden(B_172,k2_tarski(A_171,B_173)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_345])).

tff(c_622,plain,(
    ! [B_172,B_173] :
      ( r2_hidden(B_172,k2_tarski('#skF_3'(k1_tarski(B_172)),B_173))
      | k1_tarski(B_172) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_613])).

tff(c_629,plain,(
    ! [B_172,B_173] : r2_hidden(B_172,k2_tarski('#skF_3'(k1_tarski(B_172)),B_173)) ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_622])).

tff(c_589,plain,(
    ! [E_167,C_168,B_169,A_170] :
      ( E_167 = C_168
      | E_167 = B_169
      | E_167 = A_170
      | ~ r2_hidden(E_167,k1_enumset1(A_170,B_169,C_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_886,plain,(
    ! [E_253,B_254,A_255] :
      ( E_253 = B_254
      | E_253 = A_255
      | E_253 = A_255
      | ~ r2_hidden(E_253,k2_tarski(A_255,B_254)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_589])).

tff(c_913,plain,(
    ! [B_173,B_172] :
      ( B_173 = B_172
      | '#skF_3'(k1_tarski(B_172)) = B_172 ) ),
    inference(resolution,[status(thm)],[c_629,c_886])).

tff(c_970,plain,(
    ! [B_172] : '#skF_3'(k1_tarski(B_172)) = B_172 ),
    inference(factorization,[status(thm),theory(equality)],[c_913])).

tff(c_521,plain,(
    ! [C_150,A_151,D_152,E_153] :
      ( ~ r2_hidden(C_150,A_151)
      | k3_mcart_1(C_150,D_152,E_153) != '#skF_3'(A_151)
      | k1_xboole_0 = A_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_531,plain,(
    ! [A_12,D_152,E_153] :
      ( k3_mcart_1(A_12,D_152,E_153) != '#skF_3'(k1_tarski(A_12))
      | k1_tarski(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_521])).

tff(c_556,plain,(
    ! [A_12,D_152,E_153] : k3_mcart_1(A_12,D_152,E_153) != '#skF_3'(k1_tarski(A_12)) ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_531])).

tff(c_16176,plain,(
    ! [A_12,D_152,E_153] : k3_mcart_1(A_12,D_152,E_153) != A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_556])).

tff(c_72,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_160,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_863,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k7_mcart_1(A_237,B_238,C_239,D_240) = k2_mcart_1(D_240)
      | ~ m1_subset_1(D_240,k3_zfmisc_1(A_237,B_238,C_239))
      | k1_xboole_0 = C_239
      | k1_xboole_0 = B_238
      | k1_xboole_0 = A_237 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_866,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_863])).

tff(c_869,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_866])).

tff(c_16282,plain,(
    ! [A_7483,B_7484,C_7485,D_7486] :
      ( k3_mcart_1(k5_mcart_1(A_7483,B_7484,C_7485,D_7486),k6_mcart_1(A_7483,B_7484,C_7485,D_7486),k7_mcart_1(A_7483,B_7484,C_7485,D_7486)) = D_7486
      | ~ m1_subset_1(D_7486,k3_zfmisc_1(A_7483,B_7484,C_7485))
      | k1_xboole_0 = C_7485
      | k1_xboole_0 = B_7484
      | k1_xboole_0 = A_7483 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16321,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_16282])).

tff(c_16328,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_160,c_16321])).

tff(c_16330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_16176,c_16328])).

tff(c_16331,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_16353,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_16331])).

tff(c_32492,plain,(
    ! [A_14996,B_14997,C_14998,D_14999] :
      ( k3_mcart_1(k5_mcart_1(A_14996,B_14997,C_14998,D_14999),k6_mcart_1(A_14996,B_14997,C_14998,D_14999),k7_mcart_1(A_14996,B_14997,C_14998,D_14999)) = D_14999
      | ~ m1_subset_1(D_14999,k3_zfmisc_1(A_14996,B_14997,C_14998))
      | k1_xboole_0 = C_14998
      | k1_xboole_0 = B_14997
      | k1_xboole_0 = A_14996 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32531,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16353,c_32492])).

tff(c_32535,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_32531])).

tff(c_32537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_16489,c_32535])).

tff(c_32538,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_16331])).

tff(c_33302,plain,(
    ! [A_15168,B_15169,C_15170,D_15171] :
      ( k7_mcart_1(A_15168,B_15169,C_15170,D_15171) = k2_mcart_1(D_15171)
      | ~ m1_subset_1(D_15171,k3_zfmisc_1(A_15168,B_15169,C_15170))
      | k1_xboole_0 = C_15170
      | k1_xboole_0 = B_15169
      | k1_xboole_0 = A_15168 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_33305,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_33302])).

tff(c_33308,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_33305])).

tff(c_60,plain,(
    ! [A_45,B_46,C_47,D_49] :
      ( k3_mcart_1(k5_mcart_1(A_45,B_46,C_47,D_49),k6_mcart_1(A_45,B_46,C_47,D_49),k7_mcart_1(A_45,B_46,C_47,D_49)) = D_49
      | ~ m1_subset_1(D_49,k3_zfmisc_1(A_45,B_46,C_47))
      | k1_xboole_0 = C_47
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48290,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_33308,c_60])).

tff(c_48294,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_32538,c_48290])).

tff(c_48296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_48138,c_48294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:49:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.03/4.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.13  
% 11.09/4.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.09/4.14  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 11.09/4.14  
% 11.09/4.14  %Foreground sorts:
% 11.09/4.14  
% 11.09/4.14  
% 11.09/4.14  %Background operators:
% 11.09/4.14  
% 11.09/4.14  
% 11.09/4.14  %Foreground operators:
% 11.09/4.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.09/4.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.09/4.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.09/4.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.09/4.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.09/4.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.09/4.14  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 11.09/4.14  tff('#skF_7', type, '#skF_7': $i).
% 11.09/4.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.09/4.14  tff('#skF_5', type, '#skF_5': $i).
% 11.09/4.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 11.09/4.14  tff('#skF_6', type, '#skF_6': $i).
% 11.09/4.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.09/4.14  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 11.09/4.14  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.09/4.14  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 11.09/4.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.09/4.14  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 11.09/4.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.09/4.14  tff('#skF_4', type, '#skF_4': $i).
% 11.09/4.14  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.09/4.14  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 11.09/4.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.09/4.14  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 11.09/4.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.09/4.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 11.09/4.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.09/4.14  
% 11.16/4.16  tff(f_156, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 11.16/4.16  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.16/4.16  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.16/4.16  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 11.16/4.16  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.16/4.16  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.16/4.16  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.16/4.16  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 11.16/4.16  tff(f_92, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 11.16/4.16  tff(f_63, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 11.16/4.16  tff(f_65, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 11.16/4.16  tff(f_132, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 11.16/4.16  tff(f_76, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 11.16/4.16  tff(f_128, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 11.16/4.16  tff(f_108, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 11.16/4.16  tff(c_80, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.16/4.16  tff(c_78, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.16/4.16  tff(c_76, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.16/4.16  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.16/4.16  tff(c_132, plain, (![A_79, B_80]: (k1_enumset1(A_79, A_79, B_80)=k2_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.16/4.16  tff(c_10, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.16/4.16  tff(c_150, plain, (![B_81, A_82]: (r2_hidden(B_81, k2_tarski(A_82, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_10])).
% 11.16/4.16  tff(c_153, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_150])).
% 11.16/4.16  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.16/4.16  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.16/4.16  tff(c_16334, plain, (![A_7487, B_7488]: (k4_xboole_0(A_7487, k4_xboole_0(A_7487, B_7488))=k3_xboole_0(A_7487, B_7488))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.16/4.16  tff(c_16349, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_16334])).
% 11.16/4.16  tff(c_16352, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16349])).
% 11.16/4.16  tff(c_32607, plain, (![B_15004, A_15005]: (~r2_hidden(B_15004, A_15005) | k4_xboole_0(A_15005, k1_tarski(B_15004))!=A_15005)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.16/4.16  tff(c_32614, plain, (![B_15004]: (~r2_hidden(B_15004, k1_tarski(B_15004)) | k1_tarski(B_15004)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16352, c_32607])).
% 11.16/4.16  tff(c_32617, plain, (![B_15004]: (k1_tarski(B_15004)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_32614])).
% 11.16/4.16  tff(c_54, plain, (![A_31]: (r2_hidden('#skF_3'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.16/4.16  tff(c_38, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k1_tarski(B_16))=A_15 | r2_hidden(B_16, A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.16/4.16  tff(c_32876, plain, (![A_15068, C_15069, B_15070]: (~r2_hidden(A_15068, C_15069) | k4_xboole_0(k2_tarski(A_15068, B_15070), C_15069)!=k2_tarski(A_15068, B_15070))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.16/4.16  tff(c_32970, plain, (![A_15086, B_15087, B_15088]: (~r2_hidden(A_15086, k1_tarski(B_15087)) | r2_hidden(B_15087, k2_tarski(A_15086, B_15088)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_32876])).
% 11.16/4.16  tff(c_32979, plain, (![B_15087, B_15088]: (r2_hidden(B_15087, k2_tarski('#skF_3'(k1_tarski(B_15087)), B_15088)) | k1_tarski(B_15087)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_32970])).
% 11.16/4.16  tff(c_32986, plain, (![B_15087, B_15088]: (r2_hidden(B_15087, k2_tarski('#skF_3'(k1_tarski(B_15087)), B_15088)))), inference(negUnitSimplification, [status(thm)], [c_32617, c_32979])).
% 11.16/4.16  tff(c_34, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.16/4.16  tff(c_32927, plain, (![E_15080, C_15081, B_15082, A_15083]: (E_15080=C_15081 | E_15080=B_15082 | E_15080=A_15083 | ~r2_hidden(E_15080, k1_enumset1(A_15083, B_15082, C_15081)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.16/4.16  tff(c_33260, plain, (![E_15165, B_15166, A_15167]: (E_15165=B_15166 | E_15165=A_15167 | E_15165=A_15167 | ~r2_hidden(E_15165, k2_tarski(A_15167, B_15166)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_32927])).
% 11.16/4.16  tff(c_33292, plain, (![B_15088, B_15087]: (B_15088=B_15087 | '#skF_3'(k1_tarski(B_15087))=B_15087)), inference(resolution, [status(thm)], [c_32986, c_33260])).
% 11.16/4.16  tff(c_33322, plain, (![B_15087]: ('#skF_3'(k1_tarski(B_15087))=B_15087)), inference(factorization, [status(thm), theory('equality')], [c_33292])).
% 11.16/4.16  tff(c_32693, plain, (![B_15024, C_15025, A_15026]: (~r2_hidden(B_15024, C_15025) | k4_xboole_0(k2_tarski(A_15026, B_15024), C_15025)!=k2_tarski(A_15026, B_15024))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.16/4.16  tff(c_32737, plain, (![B_15033, B_15034, A_15035]: (~r2_hidden(B_15033, k1_tarski(B_15034)) | r2_hidden(B_15034, k2_tarski(A_15035, B_15033)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_32693])).
% 11.16/4.16  tff(c_32742, plain, (![B_15034, A_15035]: (r2_hidden(B_15034, k2_tarski(A_15035, '#skF_3'(k1_tarski(B_15034)))) | k1_tarski(B_15034)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_32737])).
% 11.16/4.16  tff(c_32748, plain, (![B_15036, A_15037]: (r2_hidden(B_15036, k2_tarski(A_15037, '#skF_3'(k1_tarski(B_15036)))))), inference(negUnitSimplification, [status(thm)], [c_32617, c_32742])).
% 11.16/4.16  tff(c_32752, plain, (![B_15036]: (r2_hidden(B_15036, k1_tarski('#skF_3'(k1_tarski(B_15036)))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_32748])).
% 11.16/4.16  tff(c_32805, plain, (![D_15048, A_15049, C_15050, E_15051]: (~r2_hidden(D_15048, A_15049) | k3_mcart_1(C_15050, D_15048, E_15051)!='#skF_3'(A_15049) | k1_xboole_0=A_15049)), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.16/4.16  tff(c_32809, plain, (![C_15050, B_15036, E_15051]: (k3_mcart_1(C_15050, B_15036, E_15051)!='#skF_3'(k1_tarski('#skF_3'(k1_tarski(B_15036)))) | k1_tarski('#skF_3'(k1_tarski(B_15036)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_32752, c_32805])).
% 11.16/4.16  tff(c_32831, plain, (![C_15050, B_15036, E_15051]: (k3_mcart_1(C_15050, B_15036, E_15051)!='#skF_3'(k1_tarski('#skF_3'(k1_tarski(B_15036)))))), inference(negUnitSimplification, [status(thm)], [c_32617, c_32809])).
% 11.16/4.16  tff(c_48138, plain, (![C_15050, B_15036, E_15051]: (k3_mcart_1(C_15050, B_15036, E_15051)!=B_15036)), inference(demodulation, [status(thm), theory('equality')], [c_33322, c_33322, c_32831])).
% 11.16/4.16  tff(c_74, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.16/4.16  tff(c_16471, plain, (![A_7501, B_7502, C_7503]: (k4_tarski(k4_tarski(A_7501, B_7502), C_7503)=k3_mcart_1(A_7501, B_7502, C_7503))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.16/4.16  tff(c_70, plain, (![A_55, B_56]: (k2_mcart_1(k4_tarski(A_55, B_56))=B_56)), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.16/4.16  tff(c_50, plain, (![B_29, C_30]: (k2_mcart_1(k4_tarski(B_29, C_30))!=k4_tarski(B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.16/4.16  tff(c_82, plain, (![B_29, C_30]: (k4_tarski(B_29, C_30)!=C_30)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_50])).
% 11.16/4.16  tff(c_16489, plain, (![A_7501, B_7502, C_7503]: (k3_mcart_1(A_7501, B_7502, C_7503)!=C_7503)), inference(superposition, [status(thm), theory('equality')], [c_16471, c_82])).
% 11.16/4.16  tff(c_166, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.16/4.16  tff(c_181, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_166])).
% 11.16/4.16  tff(c_184, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_181])).
% 11.16/4.16  tff(c_225, plain, (![B_90, A_91]: (~r2_hidden(B_90, A_91) | k4_xboole_0(A_91, k1_tarski(B_90))!=A_91)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.16/4.16  tff(c_229, plain, (![B_90]: (~r2_hidden(B_90, k1_tarski(B_90)) | k1_tarski(B_90)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_225])).
% 11.16/4.16  tff(c_231, plain, (![B_90]: (k1_tarski(B_90)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_229])).
% 11.16/4.16  tff(c_345, plain, (![A_115, C_116, B_117]: (~r2_hidden(A_115, C_116) | k4_xboole_0(k2_tarski(A_115, B_117), C_116)!=k2_tarski(A_115, B_117))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.16/4.16  tff(c_613, plain, (![A_171, B_172, B_173]: (~r2_hidden(A_171, k1_tarski(B_172)) | r2_hidden(B_172, k2_tarski(A_171, B_173)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_345])).
% 11.16/4.16  tff(c_622, plain, (![B_172, B_173]: (r2_hidden(B_172, k2_tarski('#skF_3'(k1_tarski(B_172)), B_173)) | k1_tarski(B_172)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_613])).
% 11.16/4.16  tff(c_629, plain, (![B_172, B_173]: (r2_hidden(B_172, k2_tarski('#skF_3'(k1_tarski(B_172)), B_173)))), inference(negUnitSimplification, [status(thm)], [c_231, c_622])).
% 11.16/4.16  tff(c_589, plain, (![E_167, C_168, B_169, A_170]: (E_167=C_168 | E_167=B_169 | E_167=A_170 | ~r2_hidden(E_167, k1_enumset1(A_170, B_169, C_168)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.16/4.16  tff(c_886, plain, (![E_253, B_254, A_255]: (E_253=B_254 | E_253=A_255 | E_253=A_255 | ~r2_hidden(E_253, k2_tarski(A_255, B_254)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_589])).
% 11.16/4.16  tff(c_913, plain, (![B_173, B_172]: (B_173=B_172 | '#skF_3'(k1_tarski(B_172))=B_172)), inference(resolution, [status(thm)], [c_629, c_886])).
% 11.16/4.16  tff(c_970, plain, (![B_172]: ('#skF_3'(k1_tarski(B_172))=B_172)), inference(factorization, [status(thm), theory('equality')], [c_913])).
% 11.16/4.16  tff(c_521, plain, (![C_150, A_151, D_152, E_153]: (~r2_hidden(C_150, A_151) | k3_mcart_1(C_150, D_152, E_153)!='#skF_3'(A_151) | k1_xboole_0=A_151)), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.16/4.16  tff(c_531, plain, (![A_12, D_152, E_153]: (k3_mcart_1(A_12, D_152, E_153)!='#skF_3'(k1_tarski(A_12)) | k1_tarski(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_521])).
% 11.16/4.16  tff(c_556, plain, (![A_12, D_152, E_153]: (k3_mcart_1(A_12, D_152, E_153)!='#skF_3'(k1_tarski(A_12)))), inference(negUnitSimplification, [status(thm)], [c_231, c_531])).
% 11.16/4.16  tff(c_16176, plain, (![A_12, D_152, E_153]: (k3_mcart_1(A_12, D_152, E_153)!=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_970, c_556])).
% 11.16/4.16  tff(c_72, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.16/4.16  tff(c_160, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_72])).
% 11.16/4.16  tff(c_863, plain, (![A_237, B_238, C_239, D_240]: (k7_mcart_1(A_237, B_238, C_239, D_240)=k2_mcart_1(D_240) | ~m1_subset_1(D_240, k3_zfmisc_1(A_237, B_238, C_239)) | k1_xboole_0=C_239 | k1_xboole_0=B_238 | k1_xboole_0=A_237)), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.16/4.16  tff(c_866, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_74, c_863])).
% 11.16/4.16  tff(c_869, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_866])).
% 11.16/4.16  tff(c_16282, plain, (![A_7483, B_7484, C_7485, D_7486]: (k3_mcart_1(k5_mcart_1(A_7483, B_7484, C_7485, D_7486), k6_mcart_1(A_7483, B_7484, C_7485, D_7486), k7_mcart_1(A_7483, B_7484, C_7485, D_7486))=D_7486 | ~m1_subset_1(D_7486, k3_zfmisc_1(A_7483, B_7484, C_7485)) | k1_xboole_0=C_7485 | k1_xboole_0=B_7484 | k1_xboole_0=A_7483)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.16/4.16  tff(c_16321, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_869, c_16282])).
% 11.16/4.16  tff(c_16328, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_160, c_16321])).
% 11.16/4.16  tff(c_16330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_16176, c_16328])).
% 11.16/4.16  tff(c_16331, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_72])).
% 11.16/4.16  tff(c_16353, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_16331])).
% 11.16/4.16  tff(c_32492, plain, (![A_14996, B_14997, C_14998, D_14999]: (k3_mcart_1(k5_mcart_1(A_14996, B_14997, C_14998, D_14999), k6_mcart_1(A_14996, B_14997, C_14998, D_14999), k7_mcart_1(A_14996, B_14997, C_14998, D_14999))=D_14999 | ~m1_subset_1(D_14999, k3_zfmisc_1(A_14996, B_14997, C_14998)) | k1_xboole_0=C_14998 | k1_xboole_0=B_14997 | k1_xboole_0=A_14996)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.16/4.16  tff(c_32531, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16353, c_32492])).
% 11.16/4.16  tff(c_32535, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_32531])).
% 11.16/4.16  tff(c_32537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_16489, c_32535])).
% 11.16/4.16  tff(c_32538, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_16331])).
% 11.16/4.16  tff(c_33302, plain, (![A_15168, B_15169, C_15170, D_15171]: (k7_mcart_1(A_15168, B_15169, C_15170, D_15171)=k2_mcart_1(D_15171) | ~m1_subset_1(D_15171, k3_zfmisc_1(A_15168, B_15169, C_15170)) | k1_xboole_0=C_15170 | k1_xboole_0=B_15169 | k1_xboole_0=A_15168)), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.16/4.16  tff(c_33305, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_74, c_33302])).
% 11.16/4.16  tff(c_33308, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_33305])).
% 11.16/4.16  tff(c_60, plain, (![A_45, B_46, C_47, D_49]: (k3_mcart_1(k5_mcart_1(A_45, B_46, C_47, D_49), k6_mcart_1(A_45, B_46, C_47, D_49), k7_mcart_1(A_45, B_46, C_47, D_49))=D_49 | ~m1_subset_1(D_49, k3_zfmisc_1(A_45, B_46, C_47)) | k1_xboole_0=C_47 | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.16/4.16  tff(c_48290, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_33308, c_60])).
% 11.16/4.16  tff(c_48294, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_32538, c_48290])).
% 11.16/4.16  tff(c_48296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_48138, c_48294])).
% 11.16/4.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.16/4.16  
% 11.16/4.16  Inference rules
% 11.16/4.16  ----------------------
% 11.16/4.16  #Ref     : 0
% 11.16/4.16  #Sup     : 8917
% 11.16/4.16  #Fact    : 6
% 11.16/4.16  #Define  : 0
% 11.16/4.16  #Split   : 2
% 11.16/4.16  #Chain   : 0
% 11.16/4.16  #Close   : 0
% 11.16/4.16  
% 11.16/4.16  Ordering : KBO
% 11.16/4.16  
% 11.16/4.16  Simplification rules
% 11.16/4.16  ----------------------
% 11.16/4.16  #Subsume      : 2303
% 11.16/4.16  #Demod        : 2050
% 11.16/4.16  #Tautology    : 414
% 11.16/4.16  #SimpNegUnit  : 254
% 11.16/4.16  #BackRed      : 61
% 11.16/4.16  
% 11.16/4.16  #Partial instantiations: 11088
% 11.16/4.16  #Strategies tried      : 1
% 11.16/4.16  
% 11.16/4.16  Timing (in seconds)
% 11.16/4.16  ----------------------
% 11.16/4.16  Preprocessing        : 0.35
% 11.16/4.16  Parsing              : 0.18
% 11.16/4.16  CNF conversion       : 0.03
% 11.16/4.16  Main loop            : 3.04
% 11.16/4.16  Inferencing          : 1.00
% 11.16/4.16  Reduction            : 1.07
% 11.16/4.16  Demodulation         : 0.67
% 11.16/4.16  BG Simplification    : 0.18
% 11.16/4.16  Subsumption          : 0.59
% 11.16/4.16  Abstraction          : 0.24
% 11.16/4.16  MUC search           : 0.00
% 11.16/4.16  Cooper               : 0.00
% 11.16/4.16  Total                : 3.43
% 11.16/4.16  Index Insertion      : 0.00
% 11.16/4.16  Index Deletion       : 0.00
% 11.16/4.16  Index Matching       : 0.00
% 11.16/4.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
