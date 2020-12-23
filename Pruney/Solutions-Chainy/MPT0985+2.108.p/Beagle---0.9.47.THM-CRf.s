%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:43 EST 2020

% Result     : Theorem 6.49s
% Output     : CNFRefutation 6.61s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 454 expanded)
%              Number of leaves         :   60 ( 191 expanded)
%              Depth                    :   13
%              Number of atoms          :  214 (1265 expanded)
%              Number of equality atoms :   58 ( 219 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_2 > k10_relat_1 > #nlpp > k4_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_277,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_260,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_152,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_186,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_192,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_168,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_882,plain,(
    ! [C_186,A_187,B_188] :
      ( v1_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_894,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_168,c_882])).

tff(c_172,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_166,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_1221,plain,(
    ! [A_213] :
      ( k4_relat_1(A_213) = k2_funct_1(A_213)
      | ~ v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1227,plain,
    ( k4_relat_1('#skF_7') = k2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_166,c_1221])).

tff(c_1231,plain,(
    k4_relat_1('#skF_7') = k2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_172,c_1227])).

tff(c_64,plain,(
    ! [A_50] :
      ( v1_relat_1(k4_relat_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1238,plain,
    ( v1_relat_1(k2_funct_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_64])).

tff(c_1250,plain,(
    v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_172,c_166,c_1238])).

tff(c_447,plain,(
    ! [C_140,A_141,B_142] :
      ( v1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_459,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_168,c_447])).

tff(c_737,plain,(
    ! [A_163] :
      ( v1_funct_1(k2_funct_1(A_163))
      | ~ v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_162,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5')
    | ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_290,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_740,plain,
    ( ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_737,c_290])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_172,c_166,c_740])).

tff(c_746,plain,(
    v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_46,plain,(
    ! [A_46] :
      ( k2_relat_1(k4_relat_1(A_46)) = k1_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1244,plain,
    ( k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_46])).

tff(c_1254,plain,(
    k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_1244])).

tff(c_164,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_1596,plain,(
    ! [A_230,B_231,C_232] :
      ( k2_relset_1(A_230,B_231,C_232) = k2_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1599,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_168,c_1596])).

tff(c_1611,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_1599])).

tff(c_48,plain,(
    ! [A_46] :
      ( k1_relat_1(k4_relat_1(A_46)) = k2_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1241,plain,
    ( k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_48])).

tff(c_1252,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_1241])).

tff(c_1619,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1252])).

tff(c_3346,plain,(
    ! [B_336,A_337] :
      ( m1_subset_1(B_336,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_336),A_337)))
      | ~ r1_tarski(k2_relat_1(B_336),A_337)
      | ~ v1_funct_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_3365,plain,(
    ! [A_337] :
      ( m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_337)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_7')),A_337)
      | ~ v1_funct_1(k2_funct_1('#skF_7'))
      | ~ v1_relat_1(k2_funct_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1619,c_3346])).

tff(c_3398,plain,(
    ! [A_338] :
      ( m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_338)))
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_746,c_1254,c_3365])).

tff(c_745,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5')
    | ~ m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_768,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_3428,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3398,c_768])).

tff(c_1890,plain,(
    ! [B_250,A_251] :
      ( k9_relat_1(k2_funct_1(B_250),A_251) = k10_relat_1(B_250,A_251)
      | ~ v2_funct_1(B_250)
      | ~ v1_funct_1(B_250)
      | ~ v1_relat_1(B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_38,plain,(
    ! [A_41] :
      ( k9_relat_1(A_41,k1_relat_1(A_41)) = k2_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1337,plain,
    ( k9_relat_1(k2_funct_1('#skF_7'),k2_relat_1('#skF_7')) = k2_relat_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_38])).

tff(c_1341,plain,(
    k9_relat_1(k2_funct_1('#skF_7'),k2_relat_1('#skF_7')) = k2_relat_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_1337])).

tff(c_1467,plain,(
    k9_relat_1(k2_funct_1('#skF_7'),k2_relat_1('#skF_7')) = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_1341])).

tff(c_1617,plain,(
    k9_relat_1(k2_funct_1('#skF_7'),'#skF_6') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1467])).

tff(c_1896,plain,
    ( k10_relat_1('#skF_7','#skF_6') = k1_relat_1('#skF_7')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1890,c_1617])).

tff(c_1916,plain,(
    k10_relat_1('#skF_7','#skF_6') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_172,c_166,c_1896])).

tff(c_2692,plain,(
    ! [A_291,B_292,C_293,D_294] :
      ( k7_relset_1(A_291,B_292,C_293,D_294) = k9_relat_1(C_293,D_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_2712,plain,(
    ! [D_294] : k7_relset_1('#skF_5','#skF_6','#skF_7',D_294) = k9_relat_1('#skF_7',D_294) ),
    inference(resolution,[status(thm)],[c_168,c_2692])).

tff(c_3500,plain,(
    ! [A_340,B_341,C_342] :
      ( k7_relset_1(A_340,B_341,C_342,A_340) = k2_relset_1(A_340,B_341,C_342)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3512,plain,(
    k7_relset_1('#skF_5','#skF_6','#skF_7','#skF_5') = k2_relset_1('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_168,c_3500])).

tff(c_3528,plain,(
    k9_relat_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2712,c_164,c_3512])).

tff(c_74,plain,(
    ! [B_55,A_54] :
      ( r1_tarski(k10_relat_1(B_55,k9_relat_1(B_55,A_54)),A_54)
      | ~ v2_funct_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3536,plain,
    ( r1_tarski(k10_relat_1('#skF_7','#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3528,c_74])).

tff(c_3540,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_172,c_166,c_1916,c_3536])).

tff(c_3542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3428,c_3540])).

tff(c_3544,plain,(
    m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_3645,plain,(
    ! [C_357,A_358,B_359] :
      ( v1_relat_1(C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_3660,plain,(
    v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3544,c_3645])).

tff(c_3661,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_168,c_3645])).

tff(c_4218,plain,(
    ! [A_395] :
      ( k4_relat_1(A_395) = k2_funct_1(A_395)
      | ~ v2_funct_1(A_395)
      | ~ v1_funct_1(A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4224,plain,
    ( k4_relat_1('#skF_7') = k2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_166,c_4218])).

tff(c_4228,plain,(
    k4_relat_1('#skF_7') = k2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3661,c_172,c_4224])).

tff(c_4241,plain,
    ( k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4228,c_46])).

tff(c_4251,plain,(
    k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3661,c_4241])).

tff(c_4414,plain,(
    ! [A_403,B_404,C_405] :
      ( k2_relset_1(A_403,B_404,C_405) = k2_relat_1(C_405)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_403,B_404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_4426,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_168,c_4414])).

tff(c_4443,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_4426])).

tff(c_4238,plain,
    ( k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4228,c_48])).

tff(c_4249,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3661,c_4238])).

tff(c_4459,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4443,c_4249])).

tff(c_5311,plain,(
    ! [B_448,A_449] :
      ( v1_funct_2(B_448,k1_relat_1(B_448),A_449)
      | ~ r1_tarski(k2_relat_1(B_448),A_449)
      | ~ v1_funct_1(B_448)
      | ~ v1_relat_1(B_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_5317,plain,(
    ! [A_449] :
      ( v1_funct_2(k2_funct_1('#skF_7'),'#skF_6',A_449)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_7')),A_449)
      | ~ v1_funct_1(k2_funct_1('#skF_7'))
      | ~ v1_relat_1(k2_funct_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4459,c_5311])).

tff(c_5332,plain,(
    ! [A_450] :
      ( v1_funct_2(k2_funct_1('#skF_7'),'#skF_6',A_450)
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3660,c_746,c_4251,c_5317])).

tff(c_3543,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_5342,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_5332,c_3543])).

tff(c_4646,plain,(
    ! [B_424,A_425] :
      ( k9_relat_1(k2_funct_1(B_424),A_425) = k10_relat_1(B_424,A_425)
      | ~ v2_funct_1(B_424)
      | ~ v1_funct_1(B_424)
      | ~ v1_relat_1(B_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4495,plain,
    ( k9_relat_1(k2_funct_1('#skF_7'),'#skF_6') = k2_relat_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4459,c_38])).

tff(c_4510,plain,(
    k9_relat_1(k2_funct_1('#skF_7'),'#skF_6') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3660,c_4251,c_4495])).

tff(c_4652,plain,
    ( k10_relat_1('#skF_7','#skF_6') = k1_relat_1('#skF_7')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4646,c_4510])).

tff(c_4672,plain,(
    k10_relat_1('#skF_7','#skF_6') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3661,c_172,c_166,c_4652])).

tff(c_5393,plain,(
    ! [A_457,B_458,C_459,D_460] :
      ( k7_relset_1(A_457,B_458,C_459,D_460) = k9_relat_1(C_459,D_460)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(A_457,B_458))) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_5417,plain,(
    ! [D_460] : k7_relset_1('#skF_5','#skF_6','#skF_7',D_460) = k9_relat_1('#skF_7',D_460) ),
    inference(resolution,[status(thm)],[c_168,c_5393])).

tff(c_5694,plain,(
    ! [A_486,B_487,C_488] :
      ( k7_relset_1(A_486,B_487,C_488,A_486) = k2_relset_1(A_486,B_487,C_488)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_5704,plain,(
    k7_relset_1('#skF_5','#skF_6','#skF_7','#skF_5') = k2_relset_1('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_168,c_5694])).

tff(c_5720,plain,(
    k9_relat_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5417,c_164,c_5704])).

tff(c_5728,plain,
    ( r1_tarski(k10_relat_1('#skF_7','#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5720,c_74])).

tff(c_5732,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3661,c_172,c_166,c_4672,c_5728])).

tff(c_5734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5342,c_5732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.49/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.29  
% 6.49/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.29  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_2 > k10_relat_1 > #nlpp > k4_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.49/2.29  
% 6.49/2.29  %Foreground sorts:
% 6.49/2.29  
% 6.49/2.29  
% 6.49/2.29  %Background operators:
% 6.49/2.29  
% 6.49/2.29  
% 6.49/2.29  %Foreground operators:
% 6.49/2.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.49/2.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.49/2.29  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 6.49/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.49/2.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.49/2.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.49/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.49/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.49/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.49/2.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.49/2.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.49/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.49/2.29  tff('#skF_7', type, '#skF_7': $i).
% 6.49/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.49/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.49/2.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.49/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.49/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.49/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.49/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.49/2.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.49/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.49/2.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.49/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.49/2.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 6.49/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.49/2.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.49/2.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.49/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.49/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.49/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.49/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.49/2.29  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.49/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.49/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.49/2.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.49/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.49/2.29  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.49/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.49/2.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.49/2.29  
% 6.61/2.31  tff(f_277, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.61/2.31  tff(f_174, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.61/2.31  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.61/2.31  tff(f_110, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_funct_1)).
% 6.61/2.31  tff(f_122, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 6.61/2.31  tff(f_77, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 6.61/2.31  tff(f_182, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.61/2.31  tff(f_260, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.61/2.31  tff(f_152, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 6.61/2.31  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 6.61/2.31  tff(f_186, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.61/2.31  tff(f_192, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 6.61/2.31  tff(f_136, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 6.61/2.31  tff(c_168, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_277])).
% 6.61/2.31  tff(c_882, plain, (![C_186, A_187, B_188]: (v1_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.61/2.31  tff(c_894, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_168, c_882])).
% 6.61/2.31  tff(c_172, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_277])).
% 6.61/2.31  tff(c_166, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_277])).
% 6.61/2.31  tff(c_1221, plain, (![A_213]: (k4_relat_1(A_213)=k2_funct_1(A_213) | ~v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.61/2.31  tff(c_1227, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_166, c_1221])).
% 6.61/2.31  tff(c_1231, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_172, c_1227])).
% 6.61/2.31  tff(c_64, plain, (![A_50]: (v1_relat_1(k4_relat_1(A_50)) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.61/2.31  tff(c_1238, plain, (v1_relat_1(k2_funct_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_64])).
% 6.61/2.31  tff(c_1250, plain, (v1_relat_1(k2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_894, c_172, c_166, c_1238])).
% 6.61/2.31  tff(c_447, plain, (![C_140, A_141, B_142]: (v1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.61/2.31  tff(c_459, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_168, c_447])).
% 6.61/2.31  tff(c_737, plain, (![A_163]: (v1_funct_1(k2_funct_1(A_163)) | ~v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.61/2.31  tff(c_162, plain, (~m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5') | ~v1_funct_1(k2_funct_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_277])).
% 6.61/2.31  tff(c_290, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_162])).
% 6.61/2.31  tff(c_740, plain, (~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_737, c_290])).
% 6.61/2.31  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_172, c_166, c_740])).
% 6.61/2.31  tff(c_746, plain, (v1_funct_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_162])).
% 6.61/2.31  tff(c_46, plain, (![A_46]: (k2_relat_1(k4_relat_1(A_46))=k1_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.61/2.31  tff(c_1244, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_46])).
% 6.61/2.31  tff(c_1254, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_1244])).
% 6.61/2.31  tff(c_164, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_277])).
% 6.61/2.31  tff(c_1596, plain, (![A_230, B_231, C_232]: (k2_relset_1(A_230, B_231, C_232)=k2_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.61/2.31  tff(c_1599, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_168, c_1596])).
% 6.61/2.31  tff(c_1611, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_1599])).
% 6.61/2.31  tff(c_48, plain, (![A_46]: (k1_relat_1(k4_relat_1(A_46))=k2_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.61/2.31  tff(c_1241, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_48])).
% 6.61/2.31  tff(c_1252, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_1241])).
% 6.61/2.31  tff(c_1619, plain, (k1_relat_1(k2_funct_1('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1252])).
% 6.61/2.31  tff(c_3346, plain, (![B_336, A_337]: (m1_subset_1(B_336, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_336), A_337))) | ~r1_tarski(k2_relat_1(B_336), A_337) | ~v1_funct_1(B_336) | ~v1_relat_1(B_336))), inference(cnfTransformation, [status(thm)], [f_260])).
% 6.61/2.31  tff(c_3365, plain, (![A_337]: (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_337))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_7')), A_337) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1619, c_3346])).
% 6.61/2.31  tff(c_3398, plain, (![A_338]: (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_338))) | ~r1_tarski(k1_relat_1('#skF_7'), A_338))), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_746, c_1254, c_3365])).
% 6.61/2.31  tff(c_745, plain, (~v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5') | ~m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(splitRight, [status(thm)], [c_162])).
% 6.61/2.31  tff(c_768, plain, (~m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(splitLeft, [status(thm)], [c_745])).
% 6.61/2.31  tff(c_3428, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_3398, c_768])).
% 6.61/2.31  tff(c_1890, plain, (![B_250, A_251]: (k9_relat_1(k2_funct_1(B_250), A_251)=k10_relat_1(B_250, A_251) | ~v2_funct_1(B_250) | ~v1_funct_1(B_250) | ~v1_relat_1(B_250))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.61/2.31  tff(c_38, plain, (![A_41]: (k9_relat_1(A_41, k1_relat_1(A_41))=k2_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.61/2.31  tff(c_1337, plain, (k9_relat_1(k2_funct_1('#skF_7'), k2_relat_1('#skF_7'))=k2_relat_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1252, c_38])).
% 6.61/2.31  tff(c_1341, plain, (k9_relat_1(k2_funct_1('#skF_7'), k2_relat_1('#skF_7'))=k2_relat_1(k2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_1337])).
% 6.61/2.31  tff(c_1467, plain, (k9_relat_1(k2_funct_1('#skF_7'), k2_relat_1('#skF_7'))=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_1341])).
% 6.61/2.31  tff(c_1617, plain, (k9_relat_1(k2_funct_1('#skF_7'), '#skF_6')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1467])).
% 6.61/2.31  tff(c_1896, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_relat_1('#skF_7') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1890, c_1617])).
% 6.61/2.31  tff(c_1916, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_172, c_166, c_1896])).
% 6.61/2.31  tff(c_2692, plain, (![A_291, B_292, C_293, D_294]: (k7_relset_1(A_291, B_292, C_293, D_294)=k9_relat_1(C_293, D_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 6.61/2.31  tff(c_2712, plain, (![D_294]: (k7_relset_1('#skF_5', '#skF_6', '#skF_7', D_294)=k9_relat_1('#skF_7', D_294))), inference(resolution, [status(thm)], [c_168, c_2692])).
% 6.61/2.31  tff(c_3500, plain, (![A_340, B_341, C_342]: (k7_relset_1(A_340, B_341, C_342, A_340)=k2_relset_1(A_340, B_341, C_342) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.61/2.31  tff(c_3512, plain, (k7_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_5')=k2_relset_1('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_168, c_3500])).
% 6.61/2.31  tff(c_3528, plain, (k9_relat_1('#skF_7', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2712, c_164, c_3512])).
% 6.61/2.31  tff(c_74, plain, (![B_55, A_54]: (r1_tarski(k10_relat_1(B_55, k9_relat_1(B_55, A_54)), A_54) | ~v2_funct_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.61/2.31  tff(c_3536, plain, (r1_tarski(k10_relat_1('#skF_7', '#skF_6'), '#skF_5') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3528, c_74])).
% 6.61/2.31  tff(c_3540, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_172, c_166, c_1916, c_3536])).
% 6.61/2.31  tff(c_3542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3428, c_3540])).
% 6.61/2.31  tff(c_3544, plain, (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(splitRight, [status(thm)], [c_745])).
% 6.61/2.31  tff(c_3645, plain, (![C_357, A_358, B_359]: (v1_relat_1(C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.61/2.31  tff(c_3660, plain, (v1_relat_1(k2_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_3544, c_3645])).
% 6.61/2.31  tff(c_3661, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_168, c_3645])).
% 6.61/2.31  tff(c_4218, plain, (![A_395]: (k4_relat_1(A_395)=k2_funct_1(A_395) | ~v2_funct_1(A_395) | ~v1_funct_1(A_395) | ~v1_relat_1(A_395))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.61/2.31  tff(c_4224, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_166, c_4218])).
% 6.61/2.31  tff(c_4228, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3661, c_172, c_4224])).
% 6.61/2.31  tff(c_4241, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4228, c_46])).
% 6.61/2.31  tff(c_4251, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3661, c_4241])).
% 6.61/2.31  tff(c_4414, plain, (![A_403, B_404, C_405]: (k2_relset_1(A_403, B_404, C_405)=k2_relat_1(C_405) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_403, B_404))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.61/2.31  tff(c_4426, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_168, c_4414])).
% 6.61/2.31  tff(c_4443, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_4426])).
% 6.61/2.31  tff(c_4238, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4228, c_48])).
% 6.61/2.31  tff(c_4249, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3661, c_4238])).
% 6.61/2.31  tff(c_4459, plain, (k1_relat_1(k2_funct_1('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4443, c_4249])).
% 6.61/2.31  tff(c_5311, plain, (![B_448, A_449]: (v1_funct_2(B_448, k1_relat_1(B_448), A_449) | ~r1_tarski(k2_relat_1(B_448), A_449) | ~v1_funct_1(B_448) | ~v1_relat_1(B_448))), inference(cnfTransformation, [status(thm)], [f_260])).
% 6.61/2.31  tff(c_5317, plain, (![A_449]: (v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', A_449) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_7')), A_449) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_4459, c_5311])).
% 6.61/2.31  tff(c_5332, plain, (![A_450]: (v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', A_450) | ~r1_tarski(k1_relat_1('#skF_7'), A_450))), inference(demodulation, [status(thm), theory('equality')], [c_3660, c_746, c_4251, c_5317])).
% 6.61/2.31  tff(c_3543, plain, (~v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_745])).
% 6.61/2.31  tff(c_5342, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_5332, c_3543])).
% 6.61/2.31  tff(c_4646, plain, (![B_424, A_425]: (k9_relat_1(k2_funct_1(B_424), A_425)=k10_relat_1(B_424, A_425) | ~v2_funct_1(B_424) | ~v1_funct_1(B_424) | ~v1_relat_1(B_424))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.61/2.31  tff(c_4495, plain, (k9_relat_1(k2_funct_1('#skF_7'), '#skF_6')=k2_relat_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4459, c_38])).
% 6.61/2.31  tff(c_4510, plain, (k9_relat_1(k2_funct_1('#skF_7'), '#skF_6')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3660, c_4251, c_4495])).
% 6.61/2.31  tff(c_4652, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_relat_1('#skF_7') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4646, c_4510])).
% 6.61/2.31  tff(c_4672, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3661, c_172, c_166, c_4652])).
% 6.61/2.31  tff(c_5393, plain, (![A_457, B_458, C_459, D_460]: (k7_relset_1(A_457, B_458, C_459, D_460)=k9_relat_1(C_459, D_460) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(A_457, B_458))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 6.61/2.31  tff(c_5417, plain, (![D_460]: (k7_relset_1('#skF_5', '#skF_6', '#skF_7', D_460)=k9_relat_1('#skF_7', D_460))), inference(resolution, [status(thm)], [c_168, c_5393])).
% 6.61/2.31  tff(c_5694, plain, (![A_486, B_487, C_488]: (k7_relset_1(A_486, B_487, C_488, A_486)=k2_relset_1(A_486, B_487, C_488) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.61/2.31  tff(c_5704, plain, (k7_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_5')=k2_relset_1('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_168, c_5694])).
% 6.61/2.31  tff(c_5720, plain, (k9_relat_1('#skF_7', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5417, c_164, c_5704])).
% 6.61/2.31  tff(c_5728, plain, (r1_tarski(k10_relat_1('#skF_7', '#skF_6'), '#skF_5') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5720, c_74])).
% 6.61/2.31  tff(c_5732, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3661, c_172, c_166, c_4672, c_5728])).
% 6.61/2.31  tff(c_5734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5342, c_5732])).
% 6.61/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.61/2.31  
% 6.61/2.31  Inference rules
% 6.61/2.31  ----------------------
% 6.61/2.31  #Ref     : 0
% 6.61/2.31  #Sup     : 1304
% 6.61/2.31  #Fact    : 0
% 6.61/2.31  #Define  : 0
% 6.61/2.31  #Split   : 21
% 6.61/2.31  #Chain   : 0
% 6.61/2.31  #Close   : 0
% 6.61/2.31  
% 6.61/2.31  Ordering : KBO
% 6.61/2.31  
% 6.61/2.31  Simplification rules
% 6.61/2.31  ----------------------
% 6.61/2.31  #Subsume      : 117
% 6.61/2.31  #Demod        : 1435
% 6.61/2.31  #Tautology    : 792
% 6.61/2.31  #SimpNegUnit  : 28
% 6.61/2.31  #BackRed      : 41
% 6.61/2.31  
% 6.61/2.31  #Partial instantiations: 0
% 6.61/2.31  #Strategies tried      : 1
% 6.61/2.31  
% 6.61/2.31  Timing (in seconds)
% 6.61/2.31  ----------------------
% 6.61/2.31  Preprocessing        : 0.45
% 6.61/2.31  Parsing              : 0.23
% 6.61/2.31  CNF conversion       : 0.04
% 6.61/2.31  Main loop            : 1.08
% 6.61/2.31  Inferencing          : 0.35
% 6.61/2.31  Reduction            : 0.42
% 6.61/2.31  Demodulation         : 0.32
% 6.61/2.31  BG Simplification    : 0.06
% 6.61/2.31  Subsumption          : 0.18
% 6.61/2.31  Abstraction          : 0.05
% 6.61/2.31  MUC search           : 0.00
% 6.61/2.31  Cooper               : 0.00
% 6.61/2.31  Total                : 1.58
% 6.61/2.31  Index Insertion      : 0.00
% 6.61/2.31  Index Deletion       : 0.00
% 6.61/2.31  Index Matching       : 0.00
% 6.61/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
