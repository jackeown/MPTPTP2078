%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:23 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 474 expanded)
%              Number of leaves         :   30 ( 170 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 961 expanded)
%              Number of equality atoms :   93 ( 352 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_279,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_295,plain,(
    ! [B_73] : k3_xboole_0(k1_xboole_0,B_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_32])).

tff(c_20,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_135,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_123])).

tff(c_307,plain,(
    ! [B_13] : k4_xboole_0(B_13,k1_xboole_0) = k3_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_279])).

tff(c_26,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_123])).

tff(c_288,plain,(
    ! [A_72,B_73] : k4_xboole_0(k3_xboole_0(A_72,B_73),A_72) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_134])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_445,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(A_86,B_85)
      | ~ v1_zfmisc_1(B_85)
      | v1_xboole_0(B_85)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4172,plain,(
    ! [B_254,A_255] :
      ( B_254 = A_255
      | ~ v1_zfmisc_1(B_254)
      | v1_xboole_0(B_254)
      | v1_xboole_0(A_255)
      | k4_xboole_0(A_255,B_254) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_445])).

tff(c_4174,plain,(
    ! [A_255] :
      ( A_255 = '#skF_3'
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_255)
      | k4_xboole_0(A_255,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_4172])).

tff(c_4178,plain,(
    ! [A_256] :
      ( A_256 = '#skF_3'
      | v1_xboole_0(A_256)
      | k4_xboole_0(A_256,'#skF_3') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4174])).

tff(c_44,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4204,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | k4_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4178,c_44])).

tff(c_4221,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_4204])).

tff(c_30,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_660,plain,(
    ! [B_105,A_106] :
      ( B_105 = A_106
      | ~ r1_tarski(B_105,A_106)
      | k4_xboole_0(A_106,B_105) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_236])).

tff(c_675,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_660])).

tff(c_709,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = A_109
      | k3_xboole_0(A_109,B_110) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_675])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_91,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_42])).

tff(c_753,plain,
    ( k1_xboole_0 != '#skF_3'
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_91])).

tff(c_793,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_4230,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4221,c_793])).

tff(c_1972,plain,(
    ! [B_175,A_176] :
      ( B_175 = A_176
      | ~ v1_zfmisc_1(B_175)
      | v1_xboole_0(B_175)
      | v1_xboole_0(A_176)
      | k4_xboole_0(A_176,B_175) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_445])).

tff(c_1974,plain,(
    ! [A_176] :
      ( A_176 = '#skF_3'
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_176)
      | k4_xboole_0(A_176,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_1972])).

tff(c_1978,plain,(
    ! [A_177] :
      ( A_177 = '#skF_3'
      | v1_xboole_0(A_177)
      | k4_xboole_0(A_177,'#skF_3') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1974])).

tff(c_2004,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | k4_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1978,c_44])).

tff(c_2021,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_2004])).

tff(c_136,plain,(
    ! [B_53] : k4_xboole_0(B_53,B_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_123])).

tff(c_145,plain,(
    ! [B_53] : r1_tarski(k1_xboole_0,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_26])).

tff(c_466,plain,(
    ! [B_53] :
      ( k1_xboole_0 = B_53
      | ~ v1_zfmisc_1(B_53)
      | v1_xboole_0(B_53)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_145,c_445])).

tff(c_483,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_377,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_504,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92),B_93)
      | ~ r1_tarski(A_92,B_93)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_4,c_377])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_512,plain,(
    ! [B_94,A_95] :
      ( ~ v1_xboole_0(B_94)
      | ~ r1_tarski(A_95,B_94)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_504,c_2])).

tff(c_607,plain,(
    ! [B_100,A_101] :
      ( ~ v1_xboole_0(B_100)
      | v1_xboole_0(A_101)
      | k4_xboole_0(A_101,B_100) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_512])).

tff(c_628,plain,(
    ! [A_104] :
      ( v1_xboole_0(A_104)
      | k4_xboole_0(A_104,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_483,c_607])).

tff(c_657,plain,(
    k4_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_628,c_44])).

tff(c_717,plain,
    ( k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_657])).

tff(c_794,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_2026,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2021,c_794])).

tff(c_211,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_222,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_211,c_2])).

tff(c_28,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_234,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_222,c_28])).

tff(c_2065,plain,(
    ! [A_178] :
      ( k1_xboole_0 = A_178
      | A_178 = '#skF_3'
      | k4_xboole_0(A_178,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1978,c_234])).

tff(c_2166,plain,(
    ! [B_179] :
      ( k3_xboole_0('#skF_3',B_179) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_179) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_2065])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_206,plain,(
    ! [B_59,A_60] :
      ( ~ r1_xboole_0(B_59,A_60)
      | ~ r1_tarski(B_59,A_60)
      | v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_929,plain,(
    ! [A_121,B_122] :
      ( ~ r1_tarski(A_121,B_122)
      | v1_xboole_0(A_121)
      | k3_xboole_0(A_121,B_122) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_206])).

tff(c_955,plain,(
    ! [B_13] :
      ( v1_xboole_0(B_13)
      | k3_xboole_0(B_13,B_13) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_929])).

tff(c_2205,plain,
    ( v1_xboole_0('#skF_3')
    | k3_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2166,c_955])).

tff(c_2254,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2205])).

tff(c_282,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,k4_xboole_0(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_30])).

tff(c_2289,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_3')) = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2254,c_282])).

tff(c_2322,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_135,c_2289])).

tff(c_2324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2026,c_2322])).

tff(c_2326,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_2445,plain,(
    ! [A_183] :
      ( k3_xboole_0(A_183,A_183) = A_183
      | k3_xboole_0(A_183,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_307])).

tff(c_2451,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2326,c_2445])).

tff(c_4228,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4221,c_4221,c_4221,c_2451])).

tff(c_4270,plain,(
    ! [A_257] :
      ( k1_xboole_0 = A_257
      | A_257 = '#skF_3'
      | k4_xboole_0(A_257,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4178,c_234])).

tff(c_4620,plain,(
    ! [B_260] :
      ( k4_xboole_0('#skF_3',B_260) = k1_xboole_0
      | k4_xboole_0('#skF_3',B_260) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_4270])).

tff(c_4786,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4620,c_91])).

tff(c_4243,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4221,c_282])).

tff(c_4265,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_4243])).

tff(c_4801,plain,(
    k3_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4786,c_4265])).

tff(c_4803,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4228,c_4801])).

tff(c_4805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4230,c_4803])).

tff(c_4807,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_4809,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4807,c_657])).

tff(c_4813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_307,c_4809])).

tff(c_4816,plain,(
    ! [B_261] :
      ( k1_xboole_0 = B_261
      | ~ v1_zfmisc_1(B_261)
      | v1_xboole_0(B_261) ) ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_4819,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_4816])).

tff(c_4822,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4819])).

tff(c_4832,plain,(
    ! [B_53] : r1_tarski('#skF_3',B_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4822,c_145])).

tff(c_4858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4832,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:25:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.04  
% 5.02/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.02/2.04  
% 5.02/2.04  %Foreground sorts:
% 5.02/2.04  
% 5.02/2.04  
% 5.02/2.04  %Background operators:
% 5.02/2.04  
% 5.02/2.04  
% 5.02/2.04  %Foreground operators:
% 5.02/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.02/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.02/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.02/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.02/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.02/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.02/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.02/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.02/2.04  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.02/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.02/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.02/2.04  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.02/2.04  
% 5.33/2.07  tff(f_99, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 5.33/2.07  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.33/2.07  tff(f_62, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.33/2.07  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.33/2.07  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.33/2.07  tff(f_54, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.33/2.07  tff(f_87, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.33/2.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.33/2.07  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.33/2.07  tff(f_58, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.33/2.07  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.33/2.07  tff(f_70, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.33/2.07  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.33/2.07  tff(c_46, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.33/2.07  tff(c_279, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.33/2.07  tff(c_32, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.33/2.07  tff(c_295, plain, (![B_73]: (k3_xboole_0(k1_xboole_0, B_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_279, c_32])).
% 5.33/2.07  tff(c_20, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.33/2.07  tff(c_123, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.33/2.07  tff(c_135, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_123])).
% 5.33/2.07  tff(c_307, plain, (![B_13]: (k4_xboole_0(B_13, k1_xboole_0)=k3_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_135, c_279])).
% 5.33/2.07  tff(c_26, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.33/2.07  tff(c_134, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_123])).
% 5.33/2.07  tff(c_288, plain, (![A_72, B_73]: (k4_xboole_0(k3_xboole_0(A_72, B_73), A_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_279, c_134])).
% 5.33/2.07  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.33/2.07  tff(c_445, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(A_86, B_85) | ~v1_zfmisc_1(B_85) | v1_xboole_0(B_85) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.33/2.07  tff(c_4172, plain, (![B_254, A_255]: (B_254=A_255 | ~v1_zfmisc_1(B_254) | v1_xboole_0(B_254) | v1_xboole_0(A_255) | k4_xboole_0(A_255, B_254)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_445])).
% 5.33/2.07  tff(c_4174, plain, (![A_255]: (A_255='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(A_255) | k4_xboole_0(A_255, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_4172])).
% 5.33/2.07  tff(c_4178, plain, (![A_256]: (A_256='#skF_3' | v1_xboole_0(A_256) | k4_xboole_0(A_256, '#skF_3')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_4174])).
% 5.33/2.07  tff(c_44, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.33/2.07  tff(c_4204, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | k4_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4178, c_44])).
% 5.33/2.07  tff(c_4221, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_4204])).
% 5.33/2.07  tff(c_30, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.33/2.07  tff(c_236, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.33/2.07  tff(c_660, plain, (![B_105, A_106]: (B_105=A_106 | ~r1_tarski(B_105, A_106) | k4_xboole_0(A_106, B_105)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_236])).
% 5.33/2.07  tff(c_675, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_660])).
% 5.33/2.07  tff(c_709, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=A_109 | k3_xboole_0(A_109, B_110)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_675])).
% 5.33/2.07  tff(c_82, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | k4_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.33/2.07  tff(c_42, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.33/2.07  tff(c_91, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_42])).
% 5.33/2.07  tff(c_753, plain, (k1_xboole_0!='#skF_3' | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_709, c_91])).
% 5.33/2.07  tff(c_793, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_753])).
% 5.33/2.07  tff(c_4230, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4221, c_793])).
% 5.33/2.07  tff(c_1972, plain, (![B_175, A_176]: (B_175=A_176 | ~v1_zfmisc_1(B_175) | v1_xboole_0(B_175) | v1_xboole_0(A_176) | k4_xboole_0(A_176, B_175)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_445])).
% 5.33/2.07  tff(c_1974, plain, (![A_176]: (A_176='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(A_176) | k4_xboole_0(A_176, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_1972])).
% 5.33/2.07  tff(c_1978, plain, (![A_177]: (A_177='#skF_3' | v1_xboole_0(A_177) | k4_xboole_0(A_177, '#skF_3')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_1974])).
% 5.33/2.07  tff(c_2004, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | k4_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1978, c_44])).
% 5.33/2.07  tff(c_2021, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_2004])).
% 5.33/2.07  tff(c_136, plain, (![B_53]: (k4_xboole_0(B_53, B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_123])).
% 5.33/2.07  tff(c_145, plain, (![B_53]: (r1_tarski(k1_xboole_0, B_53))), inference(superposition, [status(thm), theory('equality')], [c_136, c_26])).
% 5.33/2.07  tff(c_466, plain, (![B_53]: (k1_xboole_0=B_53 | ~v1_zfmisc_1(B_53) | v1_xboole_0(B_53) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_145, c_445])).
% 5.33/2.07  tff(c_483, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_466])).
% 5.33/2.07  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.07  tff(c_377, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.33/2.07  tff(c_504, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92), B_93) | ~r1_tarski(A_92, B_93) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_4, c_377])).
% 5.33/2.07  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.07  tff(c_512, plain, (![B_94, A_95]: (~v1_xboole_0(B_94) | ~r1_tarski(A_95, B_94) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_504, c_2])).
% 5.33/2.07  tff(c_607, plain, (![B_100, A_101]: (~v1_xboole_0(B_100) | v1_xboole_0(A_101) | k4_xboole_0(A_101, B_100)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_512])).
% 5.33/2.07  tff(c_628, plain, (![A_104]: (v1_xboole_0(A_104) | k4_xboole_0(A_104, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_483, c_607])).
% 5.33/2.07  tff(c_657, plain, (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_628, c_44])).
% 5.33/2.07  tff(c_717, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_709, c_657])).
% 5.33/2.07  tff(c_794, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_717])).
% 5.33/2.07  tff(c_2026, plain, (k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2021, c_794])).
% 5.33/2.07  tff(c_211, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.33/2.07  tff(c_222, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_211, c_2])).
% 5.33/2.07  tff(c_28, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.33/2.07  tff(c_234, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_222, c_28])).
% 5.33/2.07  tff(c_2065, plain, (![A_178]: (k1_xboole_0=A_178 | A_178='#skF_3' | k4_xboole_0(A_178, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1978, c_234])).
% 5.33/2.07  tff(c_2166, plain, (![B_179]: (k3_xboole_0('#skF_3', B_179)=k1_xboole_0 | k3_xboole_0('#skF_3', B_179)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_288, c_2065])).
% 5.33/2.07  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.33/2.07  tff(c_206, plain, (![B_59, A_60]: (~r1_xboole_0(B_59, A_60) | ~r1_tarski(B_59, A_60) | v1_xboole_0(B_59))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.33/2.07  tff(c_929, plain, (![A_121, B_122]: (~r1_tarski(A_121, B_122) | v1_xboole_0(A_121) | k3_xboole_0(A_121, B_122)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_206])).
% 5.33/2.07  tff(c_955, plain, (![B_13]: (v1_xboole_0(B_13) | k3_xboole_0(B_13, B_13)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_929])).
% 5.33/2.07  tff(c_2205, plain, (v1_xboole_0('#skF_3') | k3_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2166, c_955])).
% 5.33/2.07  tff(c_2254, plain, (k3_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_2205])).
% 5.33/2.07  tff(c_282, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k3_xboole_0(A_72, k4_xboole_0(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_30])).
% 5.33/2.07  tff(c_2289, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_3'))=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2254, c_282])).
% 5.33/2.07  tff(c_2322, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_135, c_2289])).
% 5.33/2.07  tff(c_2324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2026, c_2322])).
% 5.33/2.07  tff(c_2326, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_717])).
% 5.33/2.07  tff(c_2445, plain, (![A_183]: (k3_xboole_0(A_183, A_183)=A_183 | k3_xboole_0(A_183, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_709, c_307])).
% 5.33/2.07  tff(c_2451, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2326, c_2445])).
% 5.33/2.07  tff(c_4228, plain, (k3_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4221, c_4221, c_4221, c_2451])).
% 5.33/2.07  tff(c_4270, plain, (![A_257]: (k1_xboole_0=A_257 | A_257='#skF_3' | k4_xboole_0(A_257, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4178, c_234])).
% 5.33/2.07  tff(c_4620, plain, (![B_260]: (k4_xboole_0('#skF_3', B_260)=k1_xboole_0 | k4_xboole_0('#skF_3', B_260)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_134, c_4270])).
% 5.33/2.07  tff(c_4786, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4620, c_91])).
% 5.33/2.07  tff(c_4243, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4221, c_282])).
% 5.33/2.07  tff(c_4265, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_4243])).
% 5.33/2.07  tff(c_4801, plain, (k3_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4786, c_4265])).
% 5.33/2.07  tff(c_4803, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4228, c_4801])).
% 5.33/2.07  tff(c_4805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4230, c_4803])).
% 5.33/2.07  tff(c_4807, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_753])).
% 5.33/2.07  tff(c_4809, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4807, c_657])).
% 5.33/2.07  tff(c_4813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_307, c_4809])).
% 5.33/2.07  tff(c_4816, plain, (![B_261]: (k1_xboole_0=B_261 | ~v1_zfmisc_1(B_261) | v1_xboole_0(B_261))), inference(splitRight, [status(thm)], [c_466])).
% 5.33/2.07  tff(c_4819, plain, (k1_xboole_0='#skF_3' | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_4816])).
% 5.33/2.07  tff(c_4822, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_4819])).
% 5.33/2.07  tff(c_4832, plain, (![B_53]: (r1_tarski('#skF_3', B_53))), inference(demodulation, [status(thm), theory('equality')], [c_4822, c_145])).
% 5.33/2.07  tff(c_4858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4832, c_42])).
% 5.33/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.07  
% 5.33/2.07  Inference rules
% 5.33/2.07  ----------------------
% 5.33/2.07  #Ref     : 0
% 5.33/2.07  #Sup     : 1184
% 5.33/2.07  #Fact    : 2
% 5.33/2.07  #Define  : 0
% 5.33/2.07  #Split   : 4
% 5.33/2.07  #Chain   : 0
% 5.33/2.07  #Close   : 0
% 5.33/2.07  
% 5.33/2.07  Ordering : KBO
% 5.33/2.07  
% 5.33/2.07  Simplification rules
% 5.33/2.07  ----------------------
% 5.33/2.07  #Subsume      : 381
% 5.33/2.07  #Demod        : 663
% 5.33/2.07  #Tautology    : 461
% 5.33/2.07  #SimpNegUnit  : 62
% 5.33/2.07  #BackRed      : 38
% 5.33/2.07  
% 5.33/2.07  #Partial instantiations: 0
% 5.33/2.07  #Strategies tried      : 1
% 5.33/2.07  
% 5.33/2.07  Timing (in seconds)
% 5.33/2.07  ----------------------
% 5.33/2.07  Preprocessing        : 0.33
% 5.33/2.07  Parsing              : 0.17
% 5.33/2.07  CNF conversion       : 0.02
% 5.33/2.07  Main loop            : 0.90
% 5.33/2.07  Inferencing          : 0.30
% 5.33/2.07  Reduction            : 0.29
% 5.33/2.07  Demodulation         : 0.21
% 5.33/2.07  BG Simplification    : 0.03
% 5.33/2.07  Subsumption          : 0.21
% 5.33/2.07  Abstraction          : 0.05
% 5.33/2.07  MUC search           : 0.00
% 5.33/2.07  Cooper               : 0.00
% 5.33/2.07  Total                : 1.28
% 5.33/2.07  Index Insertion      : 0.00
% 5.33/2.07  Index Deletion       : 0.00
% 5.33/2.07  Index Matching       : 0.00
% 5.33/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
