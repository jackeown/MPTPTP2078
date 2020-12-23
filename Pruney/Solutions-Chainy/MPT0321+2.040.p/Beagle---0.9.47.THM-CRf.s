%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:18 EST 2020

% Result     : Theorem 38.07s
% Output     : CNFRefutation 38.07s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 427 expanded)
%              Number of leaves         :   33 ( 153 expanded)
%              Depth                    :   19
%              Number of atoms          :  226 ( 875 expanded)
%              Number of equality atoms :  104 ( 540 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_66,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(c_64,plain,
    ( '#skF_5' != '#skF_3'
    | '#skF_2' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_73,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_397,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_412,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = k4_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_397])).

tff(c_420,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_412])).

tff(c_152,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),A_54) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_152])).

tff(c_238,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_252,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_155,c_238])).

tff(c_46,plain,(
    ! [A_31] : k2_zfmisc_1(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1180,plain,(
    ! [C_123,A_124,B_125] :
      ( r1_tarski(k2_zfmisc_1(C_123,A_124),k2_zfmisc_1(C_123,B_125))
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1331,plain,(
    ! [A_134,A_135] :
      ( r1_tarski(k2_zfmisc_1(A_134,A_135),k1_xboole_0)
      | ~ r1_tarski(A_135,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1180])).

tff(c_321,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_330,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_321])).

tff(c_1334,plain,(
    ! [A_134,A_135] :
      ( k2_zfmisc_1(A_134,A_135) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,k2_zfmisc_1(A_134,A_135)) != k1_xboole_0
      | ~ r1_tarski(A_135,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1331,c_330])).

tff(c_1369,plain,(
    ! [A_136,A_137] :
      ( k2_zfmisc_1(A_136,A_137) = k1_xboole_0
      | ~ r1_tarski(A_137,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_1334])).

tff(c_1374,plain,(
    ! [A_136,A_7] :
      ( k2_zfmisc_1(A_136,A_7) = k1_xboole_0
      | k4_xboole_0(A_7,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_1369])).

tff(c_1395,plain,(
    ! [A_138,A_139] :
      ( k2_zfmisc_1(A_138,A_139) = k1_xboole_0
      | k1_xboole_0 != A_139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_1374])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_70,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_574,plain,(
    ! [B_89,A_90] :
      ( k1_xboole_0 = B_89
      | k1_xboole_0 = A_90
      | k2_zfmisc_1(A_90,B_89) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_577,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_574])).

tff(c_584,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_66,c_577])).

tff(c_1453,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_584])).

tff(c_1194,plain,(
    ! [B_125] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_2',B_125))
      | ~ r1_tarski('#skF_3',B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1180])).

tff(c_2413,plain,(
    ! [B_176,A_177,C_178] :
      ( ~ r1_tarski(k2_zfmisc_1(B_176,A_177),k2_zfmisc_1(C_178,A_177))
      | r1_tarski(B_176,C_178)
      | k1_xboole_0 = A_177 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2417,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_1194,c_2413])).

tff(c_2459,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1453,c_2417])).

tff(c_2477,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2459])).

tff(c_56,plain,(
    ! [A_36,C_38,B_37] :
      ( r1_tarski(k2_zfmisc_1(A_36,C_38),k2_zfmisc_1(B_37,C_38))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1913,plain,(
    ! [A_162,B_163,C_164] :
      ( ~ r1_tarski(k2_zfmisc_1(A_162,B_163),k2_zfmisc_1(A_162,C_164))
      | r1_tarski(B_163,C_164)
      | k1_xboole_0 = A_162 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1938,plain,(
    ! [C_164] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_2',C_164))
      | r1_tarski('#skF_3',C_164)
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1913])).

tff(c_3084,plain,(
    ! [C_197] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_2',C_197))
      | r1_tarski('#skF_3',C_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1938])).

tff(c_3094,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_3084])).

tff(c_3119,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2477,c_3094])).

tff(c_3134,plain,(
    k4_xboole_0('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_3119])).

tff(c_851,plain,(
    ! [A_108,B_109,C_110] : k4_xboole_0(k3_xboole_0(A_108,B_109),C_110) = k3_xboole_0(A_108,k4_xboole_0(B_109,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [A_11,B_12] : k4_xboole_0(k3_xboole_0(A_11,B_12),A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_238])).

tff(c_872,plain,(
    ! [C_110,B_109] : k3_xboole_0(C_110,k4_xboole_0(B_109,C_110)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_253])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58,plain,(
    ! [A_39,C_41,B_40,D_42] : k3_xboole_0(k2_zfmisc_1(A_39,C_41),k2_zfmisc_1(B_40,D_42)) = k2_zfmisc_1(k3_xboole_0(A_39,B_40),k3_xboole_0(C_41,D_42)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_823,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( ~ r1_xboole_0(A_104,B_105)
      | r1_xboole_0(k2_zfmisc_1(A_104,C_106),k2_zfmisc_1(B_105,D_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1056,plain,(
    ! [B_115,D_116] :
      ( ~ r1_xboole_0('#skF_2',B_115)
      | r1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_115,D_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_823])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1076,plain,(
    ! [B_115,D_116] :
      ( k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_115,D_116)) = k1_xboole_0
      | ~ r1_xboole_0('#skF_2',B_115) ) ),
    inference(resolution,[status(thm)],[c_1056,c_2])).

tff(c_44470,plain,(
    ! [B_698,D_699] :
      ( k2_zfmisc_1(k3_xboole_0('#skF_4',B_698),k3_xboole_0('#skF_5',D_699)) = k1_xboole_0
      | ~ r1_xboole_0('#skF_2',B_698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1076])).

tff(c_45490,plain,(
    ! [B_710] :
      ( k2_zfmisc_1(k3_xboole_0('#skF_4',B_710),'#skF_5') = k1_xboole_0
      | ~ r1_xboole_0('#skF_2',B_710) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44470])).

tff(c_44,plain,(
    ! [B_32,A_31] :
      ( k1_xboole_0 = B_32
      | k1_xboole_0 = A_31
      | k2_zfmisc_1(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_45688,plain,(
    ! [B_710] :
      ( k1_xboole_0 = '#skF_5'
      | k3_xboole_0('#skF_4',B_710) = k1_xboole_0
      | ~ r1_xboole_0('#skF_2',B_710) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45490,c_44])).

tff(c_46276,plain,(
    ! [B_717] :
      ( k3_xboole_0('#skF_4',B_717) = k1_xboole_0
      | ~ r1_xboole_0('#skF_2',B_717) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1453,c_45688])).

tff(c_47392,plain,(
    ! [B_731] :
      ( k3_xboole_0('#skF_4',B_731) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_731) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_46276])).

tff(c_47515,plain,(
    ! [B_732] : k3_xboole_0('#skF_4',k4_xboole_0(B_732,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_47392])).

tff(c_903,plain,(
    ! [A_17,B_18,C_110] : k3_xboole_0(A_17,k4_xboole_0(k2_xboole_0(A_17,B_18),C_110)) = k4_xboole_0(A_17,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_851])).

tff(c_47667,plain,(
    k4_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47515,c_903])).

tff(c_47862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3134,c_47667])).

tff(c_47863,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2459])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47869,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_47863,c_8])).

tff(c_47881,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_47869])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ! [C_38,A_36,B_37] :
      ( r1_tarski(k2_zfmisc_1(C_38,A_36),k2_zfmisc_1(C_38,B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_47864,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2459])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47970,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_47864,c_30])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski('#skF_1'(A_13,B_14,C_15),C_15)
      | k3_xboole_0(B_14,C_15) = A_13
      | ~ r1_tarski(A_13,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48818,plain,(
    ! [A_753,B_754,C_755] :
      ( ~ r1_tarski('#skF_1'(A_753,B_754,C_755),A_753)
      | k3_xboole_0(B_754,C_755) = A_753
      | ~ r1_tarski(A_753,C_755)
      | ~ r1_tarski(A_753,B_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48826,plain,(
    ! [B_14,C_15] :
      ( k3_xboole_0(B_14,C_15) = C_15
      | ~ r1_tarski(C_15,C_15)
      | ~ r1_tarski(C_15,B_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_48818])).

tff(c_48910,plain,(
    ! [B_759,C_760] :
      ( k3_xboole_0(B_759,C_760) = C_760
      | ~ r1_tarski(C_760,B_759) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48826])).

tff(c_48961,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47863,c_48910])).

tff(c_1286,plain,(
    ! [A_130] :
      ( r1_tarski(k2_zfmisc_1('#skF_2',A_130),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_130,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1180])).

tff(c_1315,plain,(
    ! [A_130] :
      ( k3_xboole_0(k2_zfmisc_1('#skF_2',A_130),k2_zfmisc_1('#skF_4','#skF_5')) = k2_zfmisc_1('#skF_2',A_130)
      | ~ r1_tarski(A_130,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1286,c_30])).

tff(c_196305,plain,(
    ! [A_1672] :
      ( k2_zfmisc_1('#skF_4',k3_xboole_0(A_1672,'#skF_5')) = k2_zfmisc_1('#skF_2',A_1672)
      | ~ r1_tarski(A_1672,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48961,c_58,c_1315])).

tff(c_196606,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = k2_zfmisc_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_47970,c_196305])).

tff(c_196666,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_70,c_196606])).

tff(c_196700,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k2_zfmisc_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196666,c_70])).

tff(c_52,plain,(
    ! [B_34,A_33,C_35] :
      ( ~ r1_tarski(k2_zfmisc_1(B_34,A_33),k2_zfmisc_1(C_35,A_33))
      | r1_tarski(B_34,C_35)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_197005,plain,(
    ! [C_35] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1(C_35,'#skF_3'))
      | r1_tarski('#skF_2',C_35)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196700,c_52])).

tff(c_197137,plain,(
    ! [C_1673] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1(C_1673,'#skF_3'))
      | r1_tarski('#skF_2',C_1673) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_197005])).

tff(c_197181,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_197137])).

tff(c_197201,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_197181])).

tff(c_197203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47881,c_197201])).

tff(c_197204,plain,(
    '#skF_5' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_197205,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_197206,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197205,c_68])).

tff(c_197285,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197205,c_70])).

tff(c_199044,plain,(
    ! [A_1785,C_1786,B_1787] :
      ( r1_tarski(k2_zfmisc_1(A_1785,C_1786),k2_zfmisc_1(B_1787,C_1786))
      | ~ r1_tarski(A_1785,B_1787) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_199067,plain,(
    ! [B_1787] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1(B_1787,'#skF_5'))
      | ~ r1_tarski('#skF_4',B_1787) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197285,c_199044])).

tff(c_199487,plain,(
    ! [A_1799,B_1800,C_1801] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1799,B_1800),k2_zfmisc_1(A_1799,C_1801))
      | r1_tarski(B_1800,C_1801)
      | k1_xboole_0 = A_1799 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_199491,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_199067,c_199487])).

tff(c_199532,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_199491])).

tff(c_199533,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_197206,c_199532])).

tff(c_199554,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_199533,c_8])).

tff(c_199563,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_197204,c_199554])).

tff(c_197941,plain,(
    ! [C_1735,A_1736,B_1737] :
      ( r1_tarski(k2_zfmisc_1(C_1735,A_1736),k2_zfmisc_1(C_1735,B_1737))
      | ~ r1_tarski(A_1736,B_1737) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_197961,plain,(
    ! [A_1736] :
      ( r1_tarski(k2_zfmisc_1('#skF_4',A_1736),k2_zfmisc_1('#skF_4','#skF_3'))
      | ~ r1_tarski(A_1736,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197285,c_197941])).

tff(c_199501,plain,(
    ! [A_1736] :
      ( r1_tarski(A_1736,'#skF_3')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(A_1736,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_197961,c_199487])).

tff(c_199675,plain,(
    ! [A_1803] :
      ( r1_tarski(A_1803,'#skF_3')
      | ~ r1_tarski(A_1803,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_197206,c_199501])).

tff(c_199698,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_199675])).

tff(c_199709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199563,c_199698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.07/28.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.07/28.85  
% 38.07/28.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.07/28.85  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 38.07/28.85  
% 38.07/28.85  %Foreground sorts:
% 38.07/28.85  
% 38.07/28.85  
% 38.07/28.85  %Background operators:
% 38.07/28.85  
% 38.07/28.85  
% 38.07/28.85  %Foreground operators:
% 38.07/28.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 38.07/28.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.07/28.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 38.07/28.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 38.07/28.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 38.07/28.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.07/28.85  tff('#skF_5', type, '#skF_5': $i).
% 38.07/28.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 38.07/28.85  tff('#skF_2', type, '#skF_2': $i).
% 38.07/28.85  tff('#skF_3', type, '#skF_3': $i).
% 38.07/28.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.07/28.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 38.07/28.85  tff('#skF_4', type, '#skF_4': $i).
% 38.07/28.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.07/28.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.07/28.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 38.07/28.85  
% 38.07/28.87  tff(f_120, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 38.07/28.87  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 38.07/28.87  tff(f_70, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 38.07/28.87  tff(f_66, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 38.07/28.87  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 38.07/28.87  tff(f_45, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 38.07/28.87  tff(f_84, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 38.07/28.87  tff(f_101, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 38.07/28.87  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 38.07/28.87  tff(f_95, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 38.07/28.87  tff(f_68, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 38.07/28.87  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 38.07/28.87  tff(f_60, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 38.07/28.87  tff(f_103, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 38.07/28.87  tff(f_109, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 38.07/28.87  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 38.07/28.87  tff(f_58, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 38.07/28.87  tff(c_64, plain, ('#skF_5'!='#skF_3' | '#skF_2'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 38.07/28.87  tff(c_73, plain, ('#skF_2'!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 38.07/28.87  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.07/28.87  tff(c_36, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_70])).
% 38.07/28.87  tff(c_32, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 38.07/28.87  tff(c_397, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_43])).
% 38.07/28.87  tff(c_412, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=k4_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_397])).
% 38.07/28.87  tff(c_420, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_412])).
% 38.07/28.87  tff(c_152, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), A_54))), inference(cnfTransformation, [status(thm)], [f_45])).
% 38.07/28.87  tff(c_155, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(superposition, [status(thm), theory('equality')], [c_32, c_152])).
% 38.07/28.87  tff(c_238, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.07/28.87  tff(c_252, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_155, c_238])).
% 38.07/28.87  tff(c_46, plain, (![A_31]: (k2_zfmisc_1(A_31, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.07/28.87  tff(c_1180, plain, (![C_123, A_124, B_125]: (r1_tarski(k2_zfmisc_1(C_123, A_124), k2_zfmisc_1(C_123, B_125)) | ~r1_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_101])).
% 38.07/28.87  tff(c_1331, plain, (![A_134, A_135]: (r1_tarski(k2_zfmisc_1(A_134, A_135), k1_xboole_0) | ~r1_tarski(A_135, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1180])).
% 38.07/28.87  tff(c_321, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.07/28.87  tff(c_330, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_321])).
% 38.07/28.87  tff(c_1334, plain, (![A_134, A_135]: (k2_zfmisc_1(A_134, A_135)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k2_zfmisc_1(A_134, A_135))!=k1_xboole_0 | ~r1_tarski(A_135, k1_xboole_0))), inference(resolution, [status(thm)], [c_1331, c_330])).
% 38.07/28.87  tff(c_1369, plain, (![A_136, A_137]: (k2_zfmisc_1(A_136, A_137)=k1_xboole_0 | ~r1_tarski(A_137, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_1334])).
% 38.07/28.87  tff(c_1374, plain, (![A_136, A_7]: (k2_zfmisc_1(A_136, A_7)=k1_xboole_0 | k4_xboole_0(A_7, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1369])).
% 38.07/28.87  tff(c_1395, plain, (![A_138, A_139]: (k2_zfmisc_1(A_138, A_139)=k1_xboole_0 | k1_xboole_0!=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_420, c_1374])).
% 38.07/28.87  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_120])).
% 38.07/28.87  tff(c_66, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 38.07/28.87  tff(c_70, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 38.07/28.87  tff(c_574, plain, (![B_89, A_90]: (k1_xboole_0=B_89 | k1_xboole_0=A_90 | k2_zfmisc_1(A_90, B_89)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.07/28.87  tff(c_577, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70, c_574])).
% 38.07/28.87  tff(c_584, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_66, c_577])).
% 38.07/28.87  tff(c_1453, plain, (k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1395, c_584])).
% 38.07/28.87  tff(c_1194, plain, (![B_125]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_2', B_125)) | ~r1_tarski('#skF_3', B_125))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1180])).
% 38.07/28.87  tff(c_2413, plain, (![B_176, A_177, C_178]: (~r1_tarski(k2_zfmisc_1(B_176, A_177), k2_zfmisc_1(C_178, A_177)) | r1_tarski(B_176, C_178) | k1_xboole_0=A_177)), inference(cnfTransformation, [status(thm)], [f_95])).
% 38.07/28.87  tff(c_2417, plain, (r1_tarski('#skF_4', '#skF_2') | k1_xboole_0='#skF_5' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_1194, c_2413])).
% 38.07/28.87  tff(c_2459, plain, (r1_tarski('#skF_4', '#skF_2') | ~r1_tarski('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1453, c_2417])).
% 38.07/28.87  tff(c_2477, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_2459])).
% 38.07/28.87  tff(c_56, plain, (![A_36, C_38, B_37]: (r1_tarski(k2_zfmisc_1(A_36, C_38), k2_zfmisc_1(B_37, C_38)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_101])).
% 38.07/28.87  tff(c_1913, plain, (![A_162, B_163, C_164]: (~r1_tarski(k2_zfmisc_1(A_162, B_163), k2_zfmisc_1(A_162, C_164)) | r1_tarski(B_163, C_164) | k1_xboole_0=A_162)), inference(cnfTransformation, [status(thm)], [f_95])).
% 38.07/28.87  tff(c_1938, plain, (![C_164]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_2', C_164)) | r1_tarski('#skF_3', C_164) | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_1913])).
% 38.07/28.87  tff(c_3084, plain, (![C_197]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_2', C_197)) | r1_tarski('#skF_3', C_197))), inference(negUnitSimplification, [status(thm)], [c_68, c_1938])).
% 38.07/28.87  tff(c_3094, plain, (r1_tarski('#skF_3', '#skF_5') | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_3084])).
% 38.07/28.87  tff(c_3119, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2477, c_3094])).
% 38.07/28.87  tff(c_3134, plain, (k4_xboole_0('#skF_4', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_3119])).
% 38.07/28.87  tff(c_851, plain, (![A_108, B_109, C_110]: (k4_xboole_0(k3_xboole_0(A_108, B_109), C_110)=k3_xboole_0(A_108, k4_xboole_0(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 38.07/28.87  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 38.07/28.87  tff(c_253, plain, (![A_11, B_12]: (k4_xboole_0(k3_xboole_0(A_11, B_12), A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_238])).
% 38.07/28.87  tff(c_872, plain, (![C_110, B_109]: (k3_xboole_0(C_110, k4_xboole_0(B_109, C_110))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_851, c_253])).
% 38.07/28.87  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 38.07/28.87  tff(c_28, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k2_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 38.07/28.87  tff(c_58, plain, (![A_39, C_41, B_40, D_42]: (k3_xboole_0(k2_zfmisc_1(A_39, C_41), k2_zfmisc_1(B_40, D_42))=k2_zfmisc_1(k3_xboole_0(A_39, B_40), k3_xboole_0(C_41, D_42)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 38.07/28.87  tff(c_823, plain, (![A_104, B_105, C_106, D_107]: (~r1_xboole_0(A_104, B_105) | r1_xboole_0(k2_zfmisc_1(A_104, C_106), k2_zfmisc_1(B_105, D_107)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 38.07/28.87  tff(c_1056, plain, (![B_115, D_116]: (~r1_xboole_0('#skF_2', B_115) | r1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_115, D_116)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_823])).
% 38.07/28.87  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 38.07/28.87  tff(c_1076, plain, (![B_115, D_116]: (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_115, D_116))=k1_xboole_0 | ~r1_xboole_0('#skF_2', B_115))), inference(resolution, [status(thm)], [c_1056, c_2])).
% 38.07/28.87  tff(c_44470, plain, (![B_698, D_699]: (k2_zfmisc_1(k3_xboole_0('#skF_4', B_698), k3_xboole_0('#skF_5', D_699))=k1_xboole_0 | ~r1_xboole_0('#skF_2', B_698))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1076])).
% 38.07/28.87  tff(c_45490, plain, (![B_710]: (k2_zfmisc_1(k3_xboole_0('#skF_4', B_710), '#skF_5')=k1_xboole_0 | ~r1_xboole_0('#skF_2', B_710))), inference(superposition, [status(thm), theory('equality')], [c_28, c_44470])).
% 38.07/28.87  tff(c_44, plain, (![B_32, A_31]: (k1_xboole_0=B_32 | k1_xboole_0=A_31 | k2_zfmisc_1(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.07/28.87  tff(c_45688, plain, (![B_710]: (k1_xboole_0='#skF_5' | k3_xboole_0('#skF_4', B_710)=k1_xboole_0 | ~r1_xboole_0('#skF_2', B_710))), inference(superposition, [status(thm), theory('equality')], [c_45490, c_44])).
% 38.07/28.87  tff(c_46276, plain, (![B_717]: (k3_xboole_0('#skF_4', B_717)=k1_xboole_0 | ~r1_xboole_0('#skF_2', B_717))), inference(negUnitSimplification, [status(thm)], [c_1453, c_45688])).
% 38.07/28.87  tff(c_47392, plain, (![B_731]: (k3_xboole_0('#skF_4', B_731)=k1_xboole_0 | k3_xboole_0('#skF_2', B_731)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_46276])).
% 38.07/28.87  tff(c_47515, plain, (![B_732]: (k3_xboole_0('#skF_4', k4_xboole_0(B_732, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_872, c_47392])).
% 38.07/28.87  tff(c_903, plain, (![A_17, B_18, C_110]: (k3_xboole_0(A_17, k4_xboole_0(k2_xboole_0(A_17, B_18), C_110))=k4_xboole_0(A_17, C_110))), inference(superposition, [status(thm), theory('equality')], [c_28, c_851])).
% 38.07/28.87  tff(c_47667, plain, (k4_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_47515, c_903])).
% 38.07/28.87  tff(c_47862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3134, c_47667])).
% 38.07/28.87  tff(c_47863, plain, (r1_tarski('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_2459])).
% 38.07/28.87  tff(c_8, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.07/28.87  tff(c_47869, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_47863, c_8])).
% 38.07/28.87  tff(c_47881, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_73, c_47869])).
% 38.07/28.87  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.07/28.87  tff(c_54, plain, (![C_38, A_36, B_37]: (r1_tarski(k2_zfmisc_1(C_38, A_36), k2_zfmisc_1(C_38, B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_101])).
% 38.07/28.87  tff(c_47864, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_2459])).
% 38.07/28.87  tff(c_30, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 38.07/28.87  tff(c_47970, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_47864, c_30])).
% 38.07/28.87  tff(c_24, plain, (![A_13, B_14, C_15]: (r1_tarski('#skF_1'(A_13, B_14, C_15), C_15) | k3_xboole_0(B_14, C_15)=A_13 | ~r1_tarski(A_13, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 38.07/28.87  tff(c_48818, plain, (![A_753, B_754, C_755]: (~r1_tarski('#skF_1'(A_753, B_754, C_755), A_753) | k3_xboole_0(B_754, C_755)=A_753 | ~r1_tarski(A_753, C_755) | ~r1_tarski(A_753, B_754))), inference(cnfTransformation, [status(thm)], [f_58])).
% 38.07/28.87  tff(c_48826, plain, (![B_14, C_15]: (k3_xboole_0(B_14, C_15)=C_15 | ~r1_tarski(C_15, C_15) | ~r1_tarski(C_15, B_14))), inference(resolution, [status(thm)], [c_24, c_48818])).
% 38.07/28.87  tff(c_48910, plain, (![B_759, C_760]: (k3_xboole_0(B_759, C_760)=C_760 | ~r1_tarski(C_760, B_759))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48826])).
% 38.07/28.87  tff(c_48961, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_47863, c_48910])).
% 38.07/28.87  tff(c_1286, plain, (![A_130]: (r1_tarski(k2_zfmisc_1('#skF_2', A_130), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_130, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1180])).
% 38.07/28.87  tff(c_1315, plain, (![A_130]: (k3_xboole_0(k2_zfmisc_1('#skF_2', A_130), k2_zfmisc_1('#skF_4', '#skF_5'))=k2_zfmisc_1('#skF_2', A_130) | ~r1_tarski(A_130, '#skF_3'))), inference(resolution, [status(thm)], [c_1286, c_30])).
% 38.07/28.87  tff(c_196305, plain, (![A_1672]: (k2_zfmisc_1('#skF_4', k3_xboole_0(A_1672, '#skF_5'))=k2_zfmisc_1('#skF_2', A_1672) | ~r1_tarski(A_1672, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48961, c_58, c_1315])).
% 38.07/28.87  tff(c_196606, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k2_zfmisc_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_47970, c_196305])).
% 38.07/28.87  tff(c_196666, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_70, c_196606])).
% 38.07/28.87  tff(c_196700, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k2_zfmisc_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196666, c_70])).
% 38.07/28.87  tff(c_52, plain, (![B_34, A_33, C_35]: (~r1_tarski(k2_zfmisc_1(B_34, A_33), k2_zfmisc_1(C_35, A_33)) | r1_tarski(B_34, C_35) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_95])).
% 38.07/28.87  tff(c_197005, plain, (![C_35]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1(C_35, '#skF_3')) | r1_tarski('#skF_2', C_35) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_196700, c_52])).
% 38.07/28.87  tff(c_197137, plain, (![C_1673]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1(C_1673, '#skF_3')) | r1_tarski('#skF_2', C_1673))), inference(negUnitSimplification, [status(thm)], [c_66, c_197005])).
% 38.07/28.87  tff(c_197181, plain, (r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_197137])).
% 38.07/28.87  tff(c_197201, plain, (r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_197181])).
% 38.07/28.87  tff(c_197203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47881, c_197201])).
% 38.07/28.87  tff(c_197204, plain, ('#skF_5'!='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 38.07/28.87  tff(c_197205, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 38.07/28.87  tff(c_197206, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_197205, c_68])).
% 38.07/28.87  tff(c_197285, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_197205, c_70])).
% 38.07/28.87  tff(c_199044, plain, (![A_1785, C_1786, B_1787]: (r1_tarski(k2_zfmisc_1(A_1785, C_1786), k2_zfmisc_1(B_1787, C_1786)) | ~r1_tarski(A_1785, B_1787))), inference(cnfTransformation, [status(thm)], [f_101])).
% 38.07/28.87  tff(c_199067, plain, (![B_1787]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1(B_1787, '#skF_5')) | ~r1_tarski('#skF_4', B_1787))), inference(superposition, [status(thm), theory('equality')], [c_197285, c_199044])).
% 38.07/28.87  tff(c_199487, plain, (![A_1799, B_1800, C_1801]: (~r1_tarski(k2_zfmisc_1(A_1799, B_1800), k2_zfmisc_1(A_1799, C_1801)) | r1_tarski(B_1800, C_1801) | k1_xboole_0=A_1799)), inference(cnfTransformation, [status(thm)], [f_95])).
% 38.07/28.87  tff(c_199491, plain, (r1_tarski('#skF_3', '#skF_5') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_199067, c_199487])).
% 38.07/28.87  tff(c_199532, plain, (r1_tarski('#skF_3', '#skF_5') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_199491])).
% 38.07/28.87  tff(c_199533, plain, (r1_tarski('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_197206, c_199532])).
% 38.07/28.87  tff(c_199554, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_199533, c_8])).
% 38.07/28.87  tff(c_199563, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_197204, c_199554])).
% 38.07/28.87  tff(c_197941, plain, (![C_1735, A_1736, B_1737]: (r1_tarski(k2_zfmisc_1(C_1735, A_1736), k2_zfmisc_1(C_1735, B_1737)) | ~r1_tarski(A_1736, B_1737))), inference(cnfTransformation, [status(thm)], [f_101])).
% 38.07/28.87  tff(c_197961, plain, (![A_1736]: (r1_tarski(k2_zfmisc_1('#skF_4', A_1736), k2_zfmisc_1('#skF_4', '#skF_3')) | ~r1_tarski(A_1736, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_197285, c_197941])).
% 38.07/28.87  tff(c_199501, plain, (![A_1736]: (r1_tarski(A_1736, '#skF_3') | k1_xboole_0='#skF_4' | ~r1_tarski(A_1736, '#skF_5'))), inference(resolution, [status(thm)], [c_197961, c_199487])).
% 38.07/28.87  tff(c_199675, plain, (![A_1803]: (r1_tarski(A_1803, '#skF_3') | ~r1_tarski(A_1803, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_197206, c_199501])).
% 38.07/28.87  tff(c_199698, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_199675])).
% 38.07/28.87  tff(c_199709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199563, c_199698])).
% 38.07/28.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.07/28.87  
% 38.07/28.87  Inference rules
% 38.07/28.87  ----------------------
% 38.07/28.87  #Ref     : 3
% 38.07/28.87  #Sup     : 50601
% 38.07/28.87  #Fact    : 0
% 38.07/28.87  #Define  : 0
% 38.07/28.87  #Split   : 37
% 38.07/28.87  #Chain   : 0
% 38.07/28.87  #Close   : 0
% 38.07/28.87  
% 38.07/28.87  Ordering : KBO
% 38.07/28.87  
% 38.07/28.87  Simplification rules
% 38.07/28.87  ----------------------
% 38.07/28.87  #Subsume      : 14983
% 38.07/28.87  #Demod        : 35212
% 38.07/28.87  #Tautology    : 24760
% 38.07/28.87  #SimpNegUnit  : 996
% 38.07/28.87  #BackRed      : 94
% 38.07/28.87  
% 38.07/28.87  #Partial instantiations: 0
% 38.07/28.87  #Strategies tried      : 1
% 38.07/28.87  
% 38.07/28.87  Timing (in seconds)
% 38.07/28.87  ----------------------
% 38.07/28.88  Preprocessing        : 0.33
% 38.07/28.88  Parsing              : 0.18
% 38.07/28.88  CNF conversion       : 0.02
% 38.07/28.88  Main loop            : 27.76
% 38.07/28.88  Inferencing          : 2.88
% 38.07/28.88  Reduction            : 16.43
% 38.07/28.88  Demodulation         : 13.84
% 38.07/28.88  BG Simplification    : 0.29
% 38.07/28.88  Subsumption          : 7.08
% 38.07/28.88  Abstraction          : 0.53
% 38.07/28.88  MUC search           : 0.00
% 38.07/28.88  Cooper               : 0.00
% 38.07/28.88  Total                : 28.14
% 38.07/28.88  Index Insertion      : 0.00
% 38.07/28.88  Index Deletion       : 0.00
% 38.07/28.88  Index Matching       : 0.00
% 38.07/28.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
