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
% DateTime   : Thu Dec  3 10:14:12 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 464 expanded)
%              Number of leaves         :   47 ( 172 expanded)
%              Depth                    :   16
%              Number of atoms          :  201 (1019 expanded)
%              Number of equality atoms :   65 ( 360 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_16,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_165,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_169,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_165])).

tff(c_32,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_177,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_32])).

tff(c_179,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_186,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_190,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_186])).

tff(c_223,plain,(
    ! [B_80,A_81] :
      ( k7_relat_1(B_80,A_81) = B_80
      | ~ v4_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_226,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_190,c_223])).

tff(c_229,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_226])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_233,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_20])).

tff(c_237,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_233])).

tff(c_18,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_242,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_18])).

tff(c_249,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_242])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,k1_relat_1(B_19))
      | k11_relat_1(B_19,A_18) = k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_200,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_204,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_200])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_433,plain,(
    ! [B_104,C_105,A_106] :
      ( r2_hidden(k1_funct_1(B_104,C_105),A_106)
      | ~ r2_hidden(C_105,k1_relat_1(B_104))
      | ~ v1_funct_1(B_104)
      | ~ v5_relat_1(B_104,A_106)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_454,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_433,c_64])).

tff(c_465,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_204,c_72,c_454])).

tff(c_473,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_465])).

tff(c_479,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_249,c_473])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_479])).

tff(c_482,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_491,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_482,c_30])).

tff(c_34,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_176,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_34])).

tff(c_178,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_484,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_178])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_484])).

tff(c_529,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_541,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_66])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_538,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_8])).

tff(c_537,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_529,c_30])).

tff(c_710,plain,(
    ! [A_132,B_133] :
      ( r2_hidden(A_132,k1_relat_1(B_133))
      | k11_relat_1(B_133,A_132) = '#skF_4'
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_22])).

tff(c_722,plain,(
    ! [A_132] :
      ( r2_hidden(A_132,'#skF_4')
      | k11_relat_1('#skF_4',A_132) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_710])).

tff(c_728,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,'#skF_4')
      | k11_relat_1('#skF_4',A_134) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_722])).

tff(c_54,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_734,plain,(
    ! [A_134] :
      ( ~ r1_tarski('#skF_4',A_134)
      | k11_relat_1('#skF_4',A_134) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_728,c_54])).

tff(c_741,plain,(
    ! [A_134] : k11_relat_1('#skF_4',A_134) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_734])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k11_relat_1(B_19,A_18) != k1_xboole_0
      | ~ r2_hidden(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_691,plain,(
    ! [B_129,A_130] :
      ( k11_relat_1(B_129,A_130) != '#skF_4'
      | ~ r2_hidden(A_130,k1_relat_1(B_129))
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_24])).

tff(c_694,plain,(
    ! [A_130] :
      ( k11_relat_1('#skF_4',A_130) != '#skF_4'
      | ~ r2_hidden(A_130,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_691])).

tff(c_700,plain,(
    ! [A_130] :
      ( k11_relat_1('#skF_4',A_130) != '#skF_4'
      | ~ r2_hidden(A_130,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_694])).

tff(c_766,plain,(
    ! [A_130] : ~ r2_hidden(A_130,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_700])).

tff(c_46,plain,(
    ! [A_24,B_27] :
      ( k1_funct_1(A_24,B_27) = k1_xboole_0
      | r2_hidden(B_27,k1_relat_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_746,plain,(
    ! [A_135,B_136] :
      ( k1_funct_1(A_135,B_136) = '#skF_4'
      | r2_hidden(B_136,k1_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_46])).

tff(c_758,plain,(
    ! [B_136] :
      ( k1_funct_1('#skF_4',B_136) = '#skF_4'
      | r2_hidden(B_136,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_746])).

tff(c_763,plain,(
    ! [B_136] :
      ( k1_funct_1('#skF_4',B_136) = '#skF_4'
      | r2_hidden(B_136,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_72,c_758])).

tff(c_783,plain,(
    ! [B_136] : k1_funct_1('#skF_4',B_136) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_766,c_763])).

tff(c_784,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [D_45,C_44,B_43,A_42] :
      ( r2_hidden(k1_funct_1(D_45,C_44),B_43)
      | k1_xboole_0 = B_43
      | ~ r2_hidden(C_44,A_42)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(D_45,A_42,B_43)
      | ~ v1_funct_1(D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_987,plain,(
    ! [D_165,C_166,B_167,A_168] :
      ( r2_hidden(k1_funct_1(D_165,C_166),B_167)
      | B_167 = '#skF_4'
      | ~ r2_hidden(C_166,A_168)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167)))
      | ~ v1_funct_2(D_165,A_168,B_167)
      | ~ v1_funct_1(D_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_62])).

tff(c_1607,plain,(
    ! [D_268,A_269,B_270] :
      ( r2_hidden(k1_funct_1(D_268,'#skF_1'(A_269)),B_270)
      | B_270 = '#skF_4'
      | ~ m1_subset_1(D_268,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_2(D_268,A_269,B_270)
      | ~ v1_funct_1(D_268)
      | v1_xboole_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_4,c_987])).

tff(c_1673,plain,(
    ! [B_270,A_269] :
      ( r2_hidden('#skF_4',B_270)
      | B_270 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_2('#skF_4',A_269,B_270)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_1607])).

tff(c_1696,plain,(
    ! [B_271,A_272] :
      ( r2_hidden('#skF_4',B_271)
      | B_271 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_272,B_271)))
      | ~ v1_funct_2('#skF_4',A_272,B_271)
      | v1_xboole_0(A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1673])).

tff(c_1699,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_1696])).

tff(c_1702,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1699])).

tff(c_1704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_541,c_784,c_1702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.61  
% 3.94/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.94/1.62  
% 3.94/1.62  %Foreground sorts:
% 3.94/1.62  
% 3.94/1.62  
% 3.94/1.62  %Background operators:
% 3.94/1.62  
% 3.94/1.62  
% 3.94/1.62  %Foreground operators:
% 3.94/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.94/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.94/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.94/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.94/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.94/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.94/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.94/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.94/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.94/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.94/1.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.94/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.94/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.94/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.94/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.94/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.94/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.94/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.94/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.94/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.62  
% 3.94/1.63  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.94/1.63  tff(f_153, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.94/1.63  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.94/1.63  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.94/1.63  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.94/1.63  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.94/1.63  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.94/1.63  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.94/1.63  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.94/1.63  tff(f_114, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.94/1.63  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.94/1.63  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.94/1.63  tff(f_119, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.94/1.63  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.94/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.94/1.63  tff(f_141, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.94/1.63  tff(c_16, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.94/1.63  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.94/1.63  tff(c_165, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.94/1.63  tff(c_169, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_165])).
% 3.94/1.63  tff(c_32, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.94/1.63  tff(c_177, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_169, c_32])).
% 3.94/1.63  tff(c_179, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_177])).
% 3.94/1.63  tff(c_186, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.94/1.63  tff(c_190, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_186])).
% 3.94/1.63  tff(c_223, plain, (![B_80, A_81]: (k7_relat_1(B_80, A_81)=B_80 | ~v4_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.94/1.63  tff(c_226, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_190, c_223])).
% 3.94/1.63  tff(c_229, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_226])).
% 3.94/1.63  tff(c_20, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.94/1.63  tff(c_233, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_229, c_20])).
% 3.94/1.63  tff(c_237, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_233])).
% 3.94/1.63  tff(c_18, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.94/1.63  tff(c_242, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_237, c_18])).
% 3.94/1.63  tff(c_249, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_242])).
% 3.94/1.63  tff(c_22, plain, (![A_18, B_19]: (r2_hidden(A_18, k1_relat_1(B_19)) | k11_relat_1(B_19, A_18)=k1_xboole_0 | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.94/1.63  tff(c_200, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.94/1.63  tff(c_204, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_200])).
% 3.94/1.63  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.94/1.63  tff(c_433, plain, (![B_104, C_105, A_106]: (r2_hidden(k1_funct_1(B_104, C_105), A_106) | ~r2_hidden(C_105, k1_relat_1(B_104)) | ~v1_funct_1(B_104) | ~v5_relat_1(B_104, A_106) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.94/1.63  tff(c_64, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.94/1.63  tff(c_454, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_433, c_64])).
% 3.94/1.63  tff(c_465, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_204, c_72, c_454])).
% 3.94/1.63  tff(c_473, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_465])).
% 3.94/1.63  tff(c_479, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_169, c_249, c_473])).
% 3.94/1.63  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_479])).
% 3.94/1.63  tff(c_482, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_177])).
% 3.94/1.63  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.94/1.63  tff(c_491, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_482, c_30])).
% 3.94/1.63  tff(c_34, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.94/1.63  tff(c_176, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_169, c_34])).
% 3.94/1.63  tff(c_178, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_176])).
% 3.94/1.63  tff(c_484, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_178])).
% 3.94/1.63  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_491, c_484])).
% 3.94/1.63  tff(c_529, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_176])).
% 3.94/1.63  tff(c_66, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.94/1.63  tff(c_541, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_529, c_66])).
% 3.94/1.63  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.94/1.63  tff(c_538, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_8])).
% 3.94/1.63  tff(c_537, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_529, c_529, c_30])).
% 3.94/1.63  tff(c_710, plain, (![A_132, B_133]: (r2_hidden(A_132, k1_relat_1(B_133)) | k11_relat_1(B_133, A_132)='#skF_4' | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_22])).
% 3.94/1.63  tff(c_722, plain, (![A_132]: (r2_hidden(A_132, '#skF_4') | k11_relat_1('#skF_4', A_132)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_710])).
% 3.94/1.63  tff(c_728, plain, (![A_134]: (r2_hidden(A_134, '#skF_4') | k11_relat_1('#skF_4', A_134)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_722])).
% 3.94/1.63  tff(c_54, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.94/1.63  tff(c_734, plain, (![A_134]: (~r1_tarski('#skF_4', A_134) | k11_relat_1('#skF_4', A_134)='#skF_4')), inference(resolution, [status(thm)], [c_728, c_54])).
% 3.94/1.63  tff(c_741, plain, (![A_134]: (k11_relat_1('#skF_4', A_134)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_734])).
% 3.94/1.63  tff(c_24, plain, (![B_19, A_18]: (k11_relat_1(B_19, A_18)!=k1_xboole_0 | ~r2_hidden(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.94/1.63  tff(c_691, plain, (![B_129, A_130]: (k11_relat_1(B_129, A_130)!='#skF_4' | ~r2_hidden(A_130, k1_relat_1(B_129)) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_24])).
% 3.94/1.63  tff(c_694, plain, (![A_130]: (k11_relat_1('#skF_4', A_130)!='#skF_4' | ~r2_hidden(A_130, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_691])).
% 3.94/1.63  tff(c_700, plain, (![A_130]: (k11_relat_1('#skF_4', A_130)!='#skF_4' | ~r2_hidden(A_130, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_694])).
% 3.94/1.63  tff(c_766, plain, (![A_130]: (~r2_hidden(A_130, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_741, c_700])).
% 3.94/1.63  tff(c_46, plain, (![A_24, B_27]: (k1_funct_1(A_24, B_27)=k1_xboole_0 | r2_hidden(B_27, k1_relat_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.94/1.63  tff(c_746, plain, (![A_135, B_136]: (k1_funct_1(A_135, B_136)='#skF_4' | r2_hidden(B_136, k1_relat_1(A_135)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_46])).
% 3.94/1.63  tff(c_758, plain, (![B_136]: (k1_funct_1('#skF_4', B_136)='#skF_4' | r2_hidden(B_136, '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_746])).
% 3.94/1.63  tff(c_763, plain, (![B_136]: (k1_funct_1('#skF_4', B_136)='#skF_4' | r2_hidden(B_136, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_72, c_758])).
% 3.94/1.63  tff(c_783, plain, (![B_136]: (k1_funct_1('#skF_4', B_136)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_766, c_763])).
% 3.94/1.63  tff(c_784, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_64])).
% 3.94/1.63  tff(c_70, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.94/1.63  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.63  tff(c_62, plain, (![D_45, C_44, B_43, A_42]: (r2_hidden(k1_funct_1(D_45, C_44), B_43) | k1_xboole_0=B_43 | ~r2_hidden(C_44, A_42) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(D_45, A_42, B_43) | ~v1_funct_1(D_45))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.94/1.63  tff(c_987, plain, (![D_165, C_166, B_167, A_168]: (r2_hidden(k1_funct_1(D_165, C_166), B_167) | B_167='#skF_4' | ~r2_hidden(C_166, A_168) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))) | ~v1_funct_2(D_165, A_168, B_167) | ~v1_funct_1(D_165))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_62])).
% 3.94/1.63  tff(c_1607, plain, (![D_268, A_269, B_270]: (r2_hidden(k1_funct_1(D_268, '#skF_1'(A_269)), B_270) | B_270='#skF_4' | ~m1_subset_1(D_268, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_2(D_268, A_269, B_270) | ~v1_funct_1(D_268) | v1_xboole_0(A_269))), inference(resolution, [status(thm)], [c_4, c_987])).
% 3.94/1.63  tff(c_1673, plain, (![B_270, A_269]: (r2_hidden('#skF_4', B_270) | B_270='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_2('#skF_4', A_269, B_270) | ~v1_funct_1('#skF_4') | v1_xboole_0(A_269))), inference(superposition, [status(thm), theory('equality')], [c_783, c_1607])).
% 3.94/1.63  tff(c_1696, plain, (![B_271, A_272]: (r2_hidden('#skF_4', B_271) | B_271='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_272, B_271))) | ~v1_funct_2('#skF_4', A_272, B_271) | v1_xboole_0(A_272))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1673])).
% 3.94/1.63  tff(c_1699, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_1696])).
% 3.94/1.63  tff(c_1702, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1699])).
% 3.94/1.63  tff(c_1704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_541, c_784, c_1702])).
% 3.94/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.63  
% 3.94/1.63  Inference rules
% 3.94/1.63  ----------------------
% 3.94/1.63  #Ref     : 0
% 3.94/1.63  #Sup     : 342
% 3.94/1.63  #Fact    : 0
% 3.94/1.63  #Define  : 0
% 3.94/1.63  #Split   : 2
% 3.94/1.63  #Chain   : 0
% 3.94/1.63  #Close   : 0
% 3.94/1.63  
% 3.94/1.63  Ordering : KBO
% 3.94/1.63  
% 3.94/1.63  Simplification rules
% 3.94/1.63  ----------------------
% 3.94/1.63  #Subsume      : 56
% 3.94/1.63  #Demod        : 454
% 3.94/1.63  #Tautology    : 142
% 3.94/1.63  #SimpNegUnit  : 7
% 3.94/1.63  #BackRed      : 25
% 3.94/1.63  
% 3.94/1.63  #Partial instantiations: 0
% 3.94/1.63  #Strategies tried      : 1
% 3.94/1.63  
% 3.94/1.63  Timing (in seconds)
% 3.94/1.63  ----------------------
% 3.94/1.64  Preprocessing        : 0.34
% 3.94/1.64  Parsing              : 0.19
% 3.94/1.64  CNF conversion       : 0.02
% 3.94/1.64  Main loop            : 0.53
% 3.94/1.64  Inferencing          : 0.18
% 3.94/1.64  Reduction            : 0.17
% 3.94/1.64  Demodulation         : 0.12
% 3.94/1.64  BG Simplification    : 0.02
% 3.94/1.64  Subsumption          : 0.11
% 3.94/1.64  Abstraction          : 0.02
% 3.94/1.64  MUC search           : 0.00
% 3.94/1.64  Cooper               : 0.00
% 3.94/1.64  Total                : 0.91
% 3.94/1.64  Index Insertion      : 0.00
% 3.94/1.64  Index Deletion       : 0.00
% 3.94/1.64  Index Matching       : 0.00
% 3.94/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
