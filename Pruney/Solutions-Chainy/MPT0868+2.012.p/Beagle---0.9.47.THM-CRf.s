%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:25 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 181 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 ( 358 expanded)
%              Number of equality atoms :   72 ( 142 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_mcart_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_109,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_13,B_14)),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_482,plain,(
    ! [C_125,B_126,A_127] :
      ( ~ v1_xboole_0(C_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(C_125))
      | ~ r2_hidden(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_498,plain,(
    ! [B_130,A_131,A_132] :
      ( ~ v1_xboole_0(B_130)
      | ~ r2_hidden(A_131,A_132)
      | ~ r1_tarski(A_132,B_130) ) ),
    inference(resolution,[status(thm)],[c_10,c_482])).

tff(c_505,plain,(
    ! [B_133,A_134] :
      ( ~ v1_xboole_0(B_133)
      | ~ r1_tarski(A_134,B_133)
      | k1_xboole_0 = A_134 ) ),
    inference(resolution,[status(thm)],[c_32,c_498])).

tff(c_510,plain,(
    ! [A_135,B_136] :
      ( ~ v1_xboole_0(A_135)
      | k1_relat_1(k2_zfmisc_1(A_135,B_136)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_505])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_relat_1(A_12))
      | ~ v1_relat_1(A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_516,plain,(
    ! [A_135,B_136] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_135,B_136))
      | v1_xboole_0(k2_zfmisc_1(A_135,B_136))
      | ~ v1_xboole_0(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_16])).

tff(c_533,plain,(
    ! [A_138,B_139] :
      ( v1_xboole_0(k2_zfmisc_1(A_138,B_139))
      | ~ v1_xboole_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_516])).

tff(c_464,plain,(
    ! [B_115,A_116] :
      ( ~ v1_xboole_0(B_115)
      | B_115 = A_116
      | ~ v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_467,plain,(
    ! [A_116] :
      ( k1_xboole_0 = A_116
      | ~ v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_2,c_464])).

tff(c_567,plain,(
    ! [A_142,B_143] :
      ( k2_zfmisc_1(A_142,B_143) = k1_xboole_0
      | ~ v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_533,c_467])).

tff(c_574,plain,(
    ! [B_144] : k2_zfmisc_1(k1_xboole_0,B_144) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_567])).

tff(c_509,plain,(
    ! [A_13,B_14] :
      ( ~ v1_xboole_0(A_13)
      | k1_relat_1(k2_zfmisc_1(A_13,B_14)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_505])).

tff(c_585,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_509])).

tff(c_601,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_585])).

tff(c_36,plain,(
    ! [A_34,B_35] : k2_mcart_1(k4_tarski(A_34,B_35)) = B_35 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    ! [B_20,C_21] : k2_mcart_1(k4_tarski(B_20,C_21)) != k4_tarski(B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [B_20,C_21] : k4_tarski(B_20,C_21) != C_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24])).

tff(c_127,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_131,plain,(
    ! [B_68,A_69,A_70] :
      ( ~ v1_xboole_0(B_68)
      | ~ r2_hidden(A_69,A_70)
      | ~ r1_tarski(A_70,B_68) ) ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_145,plain,(
    ! [B_73,A_74] :
      ( ~ v1_xboole_0(B_73)
      | ~ r1_tarski(A_74,B_73)
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_32,c_131])).

tff(c_154,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(A_75)
      | k1_relat_1(k2_zfmisc_1(A_75,B_76)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_145])).

tff(c_163,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_75,B_76))
      | v1_xboole_0(k2_zfmisc_1(A_75,B_76))
      | ~ v1_xboole_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_192,plain,(
    ! [A_81,B_82] :
      ( v1_xboole_0(k2_zfmisc_1(A_81,B_82))
      | ~ v1_xboole_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_163])).

tff(c_73,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | B_47 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_200,plain,(
    ! [A_83,B_84] :
      ( k2_zfmisc_1(A_83,B_84) = k1_xboole_0
      | ~ v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_192,c_76])).

tff(c_207,plain,(
    ! [B_85] : k2_zfmisc_1(k1_xboole_0,B_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_200])).

tff(c_153,plain,(
    ! [A_13,B_14] :
      ( ~ v1_xboole_0(A_13)
      | k1_relat_1(k2_zfmisc_1(A_13,B_14)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_145])).

tff(c_215,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_153])).

tff(c_233,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_215])).

tff(c_34,plain,(
    ! [A_34,B_35] : k1_mcart_1(k4_tarski(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    ! [B_20,C_21] : k1_mcart_1(k4_tarski(B_20,C_21)) != k4_tarski(B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_45,plain,(
    ! [B_20,C_21] : k4_tarski(B_20,C_21) != B_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26])).

tff(c_38,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_68,plain,(
    k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_138,plain,(
    ! [A_71,B_72] :
      ( k4_tarski(k1_mcart_1(A_71),k2_mcart_1(A_71)) = A_71
      | ~ r2_hidden(A_71,B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_391,plain,(
    ! [A_110,B_111] :
      ( k4_tarski(k1_mcart_1(A_110),k2_mcart_1(A_110)) = A_110
      | ~ v1_relat_1(B_111)
      | v1_xboole_0(B_111)
      | ~ m1_subset_1(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_395,plain,
    ( k4_tarski(k1_mcart_1('#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_391])).

tff(c_399,plain,
    ( k4_tarski('#skF_4',k2_mcart_1('#skF_4')) = '#skF_4'
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_68,c_395])).

tff(c_400,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_399])).

tff(c_418,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_400,c_76])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k1_relat_1(k2_zfmisc_1(A_15,B_16)) = A_15
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_438,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_22])).

tff(c_453,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_438])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_44,c_453])).

tff(c_456,plain,(
    k2_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_604,plain,(
    ! [A_145,B_146] :
      ( k4_tarski(k1_mcart_1(A_145),k2_mcart_1(A_145)) = A_145
      | ~ r2_hidden(A_145,B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_770,plain,(
    ! [A_174,B_175] :
      ( k4_tarski(k1_mcart_1(A_174),k2_mcart_1(A_174)) = A_174
      | ~ v1_relat_1(B_175)
      | v1_xboole_0(B_175)
      | ~ m1_subset_1(A_174,B_175) ) ),
    inference(resolution,[status(thm)],[c_6,c_604])).

tff(c_774,plain,
    ( k4_tarski(k1_mcart_1('#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_770])).

tff(c_778,plain,
    ( k4_tarski(k1_mcart_1('#skF_4'),'#skF_4') = '#skF_4'
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_456,c_774])).

tff(c_779,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_778])).

tff(c_808,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_779,c_467])).

tff(c_822,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_22])).

tff(c_841,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_822])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_44,c_841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.77/1.41  
% 2.77/1.41  %Foreground sorts:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Background operators:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Foreground operators:
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.77/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.77/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.41  
% 3.00/1.43  tff(f_127, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 3.00/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.00/1.43  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.00/1.43  tff(f_63, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 3.00/1.43  tff(f_105, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ((r2_hidden(C, D) & r2_hidden(D, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_mcart_1)).
% 3.00/1.43  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.00/1.43  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.00/1.43  tff(f_61, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.00/1.43  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.00/1.43  tff(f_109, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.00/1.43  tff(f_84, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.00/1.43  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.00/1.43  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.00/1.43  tff(f_75, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 3.00/1.43  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.00/1.43  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.00/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.00/1.43  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.43  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_13, B_14)), A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.43  tff(c_32, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.00/1.43  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.43  tff(c_482, plain, (![C_125, B_126, A_127]: (~v1_xboole_0(C_125) | ~m1_subset_1(B_126, k1_zfmisc_1(C_125)) | ~r2_hidden(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.43  tff(c_498, plain, (![B_130, A_131, A_132]: (~v1_xboole_0(B_130) | ~r2_hidden(A_131, A_132) | ~r1_tarski(A_132, B_130))), inference(resolution, [status(thm)], [c_10, c_482])).
% 3.00/1.43  tff(c_505, plain, (![B_133, A_134]: (~v1_xboole_0(B_133) | ~r1_tarski(A_134, B_133) | k1_xboole_0=A_134)), inference(resolution, [status(thm)], [c_32, c_498])).
% 3.00/1.43  tff(c_510, plain, (![A_135, B_136]: (~v1_xboole_0(A_135) | k1_relat_1(k2_zfmisc_1(A_135, B_136))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_505])).
% 3.00/1.43  tff(c_16, plain, (![A_12]: (~v1_xboole_0(k1_relat_1(A_12)) | ~v1_relat_1(A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.00/1.43  tff(c_516, plain, (![A_135, B_136]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_135, B_136)) | v1_xboole_0(k2_zfmisc_1(A_135, B_136)) | ~v1_xboole_0(A_135))), inference(superposition, [status(thm), theory('equality')], [c_510, c_16])).
% 3.00/1.43  tff(c_533, plain, (![A_138, B_139]: (v1_xboole_0(k2_zfmisc_1(A_138, B_139)) | ~v1_xboole_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_516])).
% 3.00/1.43  tff(c_464, plain, (![B_115, A_116]: (~v1_xboole_0(B_115) | B_115=A_116 | ~v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.43  tff(c_467, plain, (![A_116]: (k1_xboole_0=A_116 | ~v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_2, c_464])).
% 3.00/1.43  tff(c_567, plain, (![A_142, B_143]: (k2_zfmisc_1(A_142, B_143)=k1_xboole_0 | ~v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_533, c_467])).
% 3.00/1.43  tff(c_574, plain, (![B_144]: (k2_zfmisc_1(k1_xboole_0, B_144)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_567])).
% 3.00/1.43  tff(c_509, plain, (![A_13, B_14]: (~v1_xboole_0(A_13) | k1_relat_1(k2_zfmisc_1(A_13, B_14))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_505])).
% 3.00/1.43  tff(c_585, plain, (~v1_xboole_0(k1_xboole_0) | k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_574, c_509])).
% 3.00/1.43  tff(c_601, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_585])).
% 3.00/1.43  tff(c_36, plain, (![A_34, B_35]: (k2_mcart_1(k4_tarski(A_34, B_35))=B_35)), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.00/1.43  tff(c_24, plain, (![B_20, C_21]: (k2_mcart_1(k4_tarski(B_20, C_21))!=k4_tarski(B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.00/1.43  tff(c_46, plain, (![B_20, C_21]: (k4_tarski(B_20, C_21)!=C_21)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24])).
% 3.00/1.43  tff(c_127, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.43  tff(c_131, plain, (![B_68, A_69, A_70]: (~v1_xboole_0(B_68) | ~r2_hidden(A_69, A_70) | ~r1_tarski(A_70, B_68))), inference(resolution, [status(thm)], [c_10, c_127])).
% 3.00/1.43  tff(c_145, plain, (![B_73, A_74]: (~v1_xboole_0(B_73) | ~r1_tarski(A_74, B_73) | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_32, c_131])).
% 3.00/1.43  tff(c_154, plain, (![A_75, B_76]: (~v1_xboole_0(A_75) | k1_relat_1(k2_zfmisc_1(A_75, B_76))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_145])).
% 3.00/1.43  tff(c_163, plain, (![A_75, B_76]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_75, B_76)) | v1_xboole_0(k2_zfmisc_1(A_75, B_76)) | ~v1_xboole_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_154, c_16])).
% 3.00/1.43  tff(c_192, plain, (![A_81, B_82]: (v1_xboole_0(k2_zfmisc_1(A_81, B_82)) | ~v1_xboole_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_163])).
% 3.00/1.43  tff(c_73, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | B_47=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.43  tff(c_76, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_2, c_73])).
% 3.00/1.43  tff(c_200, plain, (![A_83, B_84]: (k2_zfmisc_1(A_83, B_84)=k1_xboole_0 | ~v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_192, c_76])).
% 3.00/1.43  tff(c_207, plain, (![B_85]: (k2_zfmisc_1(k1_xboole_0, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_200])).
% 3.00/1.43  tff(c_153, plain, (![A_13, B_14]: (~v1_xboole_0(A_13) | k1_relat_1(k2_zfmisc_1(A_13, B_14))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_145])).
% 3.00/1.43  tff(c_215, plain, (~v1_xboole_0(k1_xboole_0) | k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_207, c_153])).
% 3.00/1.43  tff(c_233, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_215])).
% 3.00/1.43  tff(c_34, plain, (![A_34, B_35]: (k1_mcart_1(k4_tarski(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.00/1.43  tff(c_26, plain, (![B_20, C_21]: (k1_mcart_1(k4_tarski(B_20, C_21))!=k4_tarski(B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.00/1.43  tff(c_45, plain, (![B_20, C_21]: (k4_tarski(B_20, C_21)!=B_20)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26])).
% 3.00/1.43  tff(c_38, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.00/1.43  tff(c_68, plain, (k1_mcart_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 3.00/1.43  tff(c_40, plain, (m1_subset_1('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.00/1.43  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.00/1.43  tff(c_138, plain, (![A_71, B_72]: (k4_tarski(k1_mcart_1(A_71), k2_mcart_1(A_71))=A_71 | ~r2_hidden(A_71, B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.00/1.43  tff(c_391, plain, (![A_110, B_111]: (k4_tarski(k1_mcart_1(A_110), k2_mcart_1(A_110))=A_110 | ~v1_relat_1(B_111) | v1_xboole_0(B_111) | ~m1_subset_1(A_110, B_111))), inference(resolution, [status(thm)], [c_6, c_138])).
% 3.00/1.43  tff(c_395, plain, (k4_tarski(k1_mcart_1('#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_391])).
% 3.00/1.43  tff(c_399, plain, (k4_tarski('#skF_4', k2_mcart_1('#skF_4'))='#skF_4' | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_68, c_395])).
% 3.00/1.43  tff(c_400, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_45, c_399])).
% 3.00/1.43  tff(c_418, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_400, c_76])).
% 3.00/1.43  tff(c_22, plain, (![A_15, B_16]: (k1_relat_1(k2_zfmisc_1(A_15, B_16))=A_15 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.00/1.43  tff(c_438, plain, (k1_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_418, c_22])).
% 3.00/1.43  tff(c_453, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_233, c_438])).
% 3.00/1.43  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_44, c_453])).
% 3.00/1.43  tff(c_456, plain, (k2_mcart_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 3.00/1.43  tff(c_604, plain, (![A_145, B_146]: (k4_tarski(k1_mcart_1(A_145), k2_mcart_1(A_145))=A_145 | ~r2_hidden(A_145, B_146) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.00/1.43  tff(c_770, plain, (![A_174, B_175]: (k4_tarski(k1_mcart_1(A_174), k2_mcart_1(A_174))=A_174 | ~v1_relat_1(B_175) | v1_xboole_0(B_175) | ~m1_subset_1(A_174, B_175))), inference(resolution, [status(thm)], [c_6, c_604])).
% 3.00/1.43  tff(c_774, plain, (k4_tarski(k1_mcart_1('#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_770])).
% 3.00/1.43  tff(c_778, plain, (k4_tarski(k1_mcart_1('#skF_4'), '#skF_4')='#skF_4' | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_456, c_774])).
% 3.00/1.43  tff(c_779, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_778])).
% 3.00/1.43  tff(c_808, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_779, c_467])).
% 3.00/1.43  tff(c_822, plain, (k1_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_808, c_22])).
% 3.00/1.43  tff(c_841, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_601, c_822])).
% 3.00/1.43  tff(c_843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_44, c_841])).
% 3.00/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.43  
% 3.00/1.43  Inference rules
% 3.00/1.43  ----------------------
% 3.00/1.43  #Ref     : 0
% 3.00/1.43  #Sup     : 192
% 3.00/1.43  #Fact    : 0
% 3.00/1.43  #Define  : 0
% 3.00/1.43  #Split   : 3
% 3.00/1.43  #Chain   : 0
% 3.00/1.43  #Close   : 0
% 3.00/1.43  
% 3.00/1.43  Ordering : KBO
% 3.00/1.43  
% 3.00/1.43  Simplification rules
% 3.00/1.43  ----------------------
% 3.00/1.43  #Subsume      : 20
% 3.00/1.43  #Demod        : 78
% 3.00/1.43  #Tautology    : 90
% 3.00/1.43  #SimpNegUnit  : 4
% 3.00/1.43  #BackRed      : 4
% 3.00/1.43  
% 3.00/1.43  #Partial instantiations: 0
% 3.00/1.43  #Strategies tried      : 1
% 3.00/1.43  
% 3.00/1.43  Timing (in seconds)
% 3.00/1.43  ----------------------
% 3.00/1.43  Preprocessing        : 0.31
% 3.00/1.43  Parsing              : 0.17
% 3.00/1.43  CNF conversion       : 0.02
% 3.00/1.43  Main loop            : 0.34
% 3.00/1.43  Inferencing          : 0.13
% 3.00/1.43  Reduction            : 0.09
% 3.00/1.43  Demodulation         : 0.06
% 3.00/1.43  BG Simplification    : 0.02
% 3.00/1.43  Subsumption          : 0.06
% 3.00/1.43  Abstraction          : 0.02
% 3.00/1.43  MUC search           : 0.00
% 3.00/1.43  Cooper               : 0.00
% 3.00/1.43  Total                : 0.69
% 3.00/1.43  Index Insertion      : 0.00
% 3.00/1.43  Index Deletion       : 0.00
% 3.00/1.43  Index Matching       : 0.00
% 3.00/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
