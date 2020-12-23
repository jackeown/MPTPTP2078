%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 302 expanded)
%              Number of leaves         :   28 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :  184 ( 700 expanded)
%              Number of equality atoms :    1 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [A_52,B_53] :
      ( v1_relat_1(A_52)
      | ~ v1_relat_1(B_53)
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_12,c_83])).

tff(c_97,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_105,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_97])).

tff(c_498,plain,(
    ! [A_131,B_132] :
      ( r1_tarski(k2_relat_1(A_131),k2_relat_1(B_132))
      | ~ r1_tarski(A_131,B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_15,B_16)),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_126,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(A_60,C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_60,B_16,A_15] :
      ( r1_tarski(A_60,B_16)
      | ~ r1_tarski(A_60,k2_relat_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(resolution,[status(thm)],[c_20,c_126])).

tff(c_508,plain,(
    ! [A_131,B_16,A_15] :
      ( r1_tarski(k2_relat_1(A_131),B_16)
      | ~ r1_tarski(A_131,k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(A_131) ) ),
    inference(resolution,[status(thm)],[c_498,c_136])).

tff(c_1028,plain,(
    ! [A_169,B_170,A_171] :
      ( r1_tarski(k2_relat_1(A_169),B_170)
      | ~ r1_tarski(A_169,k2_zfmisc_1(A_171,B_170))
      | ~ v1_relat_1(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_508])).

tff(c_1058,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_5')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1028])).

tff(c_1074,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1058])).

tff(c_1095,plain,(
    ! [C_172,A_173,B_174] :
      ( m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ r1_tarski(k2_relat_1(C_172),B_174)
      | ~ r1_tarski(k1_relat_1(C_172),A_173)
      | ~ v1_relat_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2768,plain,(
    ! [C_274,A_275,B_276] :
      ( r1_tarski(C_274,k2_zfmisc_1(A_275,B_276))
      | ~ r1_tarski(k2_relat_1(C_274),B_276)
      | ~ r1_tarski(k1_relat_1(C_274),A_275)
      | ~ v1_relat_1(C_274) ) ),
    inference(resolution,[status(thm)],[c_1095,c_10])).

tff(c_2787,plain,(
    ! [A_275] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_275,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_275)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1074,c_2768])).

tff(c_2857,plain,(
    ! [A_277] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_277,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2787])).

tff(c_2891,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_2857])).

tff(c_38,plain,(
    ! [A_25,B_26,C_27] :
      ( v1_finset_1('#skF_1'(A_25,B_26,C_27))
      | ~ r1_tarski(A_25,k2_zfmisc_1(B_26,C_27))
      | ~ v1_finset_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2909,plain,
    ( v1_finset_1('#skF_1'('#skF_3',k1_relat_1('#skF_3'),'#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2891,c_38])).

tff(c_2945,plain,(
    v1_finset_1('#skF_1'('#skF_3',k1_relat_1('#skF_3'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2909])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2949,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_5'))
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2891,c_8])).

tff(c_30,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(A_25,k2_zfmisc_1('#skF_1'(A_25,B_26,C_27),'#skF_2'(A_25,B_26,C_27)))
      | ~ r1_tarski(A_25,k2_zfmisc_1(B_26,C_27))
      | ~ v1_finset_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_13,B_14)),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    ! [A_43,B_44] :
      ( v1_finset_1(A_43)
      | ~ v1_finset_1(B_44)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_69,plain,(
    ! [A_13,B_14] :
      ( v1_finset_1(k1_relat_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_finset_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_56])).

tff(c_314,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k1_relat_1(A_84),k1_relat_1(B_85))
      | ~ r1_tarski(A_84,B_85)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,(
    ! [A_60,A_13,B_14] :
      ( r1_tarski(A_60,A_13)
      | ~ r1_tarski(A_60,k1_relat_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(resolution,[status(thm)],[c_18,c_126])).

tff(c_318,plain,(
    ! [A_84,A_13,B_14] :
      ( r1_tarski(k1_relat_1(A_84),A_13)
      | ~ r1_tarski(A_84,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_314,c_135])).

tff(c_551,plain,(
    ! [A_140,A_141,B_142] :
      ( r1_tarski(k1_relat_1(A_140),A_141)
      | ~ r1_tarski(A_140,k2_zfmisc_1(A_141,B_142))
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_318])).

tff(c_573,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_551])).

tff(c_586,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_573])).

tff(c_40,plain,(
    ! [D_31] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_31,'#skF_5'))
      | ~ r1_tarski(D_31,'#skF_4')
      | ~ v1_finset_1(D_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2922,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_4')
    | ~ v1_finset_1(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2891,c_40])).

tff(c_2956,plain,(
    ~ v1_finset_1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_2922])).

tff(c_24,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k1_relat_1(A_17),k1_relat_1(B_19))
      | ~ r1_tarski(A_17,B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2872,plain,(
    ! [B_19] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1(B_19),'#skF_5'))
      | ~ r1_tarski('#skF_3',B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_2857])).

tff(c_3126,plain,(
    ! [B_283] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1(B_283),'#skF_5'))
      | ~ r1_tarski('#skF_3',B_283)
      | ~ v1_relat_1(B_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2872])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( v1_finset_1(A_23)
      | ~ v1_finset_1(B_24)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1815,plain,(
    ! [A_218,B_219] :
      ( v1_finset_1(k1_relat_1(A_218))
      | ~ v1_finset_1(k1_relat_1(B_219))
      | ~ r1_tarski(A_218,B_219)
      | ~ v1_relat_1(B_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_314,c_28])).

tff(c_1821,plain,(
    ! [A_218,A_13,B_14] :
      ( v1_finset_1(k1_relat_1(A_218))
      | ~ r1_tarski(A_218,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_218)
      | ~ v1_finset_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_69,c_1815])).

tff(c_1830,plain,(
    ! [A_218,A_13,B_14] :
      ( v1_finset_1(k1_relat_1(A_218))
      | ~ r1_tarski(A_218,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_218)
      | ~ v1_finset_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1821])).

tff(c_3129,plain,(
    ! [B_283] :
      ( v1_finset_1(k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_finset_1(k1_relat_1(B_283))
      | ~ r1_tarski('#skF_3',B_283)
      | ~ v1_relat_1(B_283) ) ),
    inference(resolution,[status(thm)],[c_3126,c_1830])).

tff(c_3163,plain,(
    ! [B_283] :
      ( v1_finset_1(k1_relat_1('#skF_3'))
      | ~ v1_finset_1(k1_relat_1(B_283))
      | ~ r1_tarski('#skF_3',B_283)
      | ~ v1_relat_1(B_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_3129])).

tff(c_3264,plain,(
    ! [B_285] :
      ( ~ v1_finset_1(k1_relat_1(B_285))
      | ~ r1_tarski('#skF_3',B_285)
      | ~ v1_relat_1(B_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2956,c_3163])).

tff(c_3273,plain,(
    ! [A_13,B_14] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_finset_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_69,c_3264])).

tff(c_3283,plain,(
    ! [A_286,B_287] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(A_286,B_287))
      | ~ v1_finset_1(A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3273])).

tff(c_3297,plain,(
    ! [B_26,C_27] :
      ( ~ v1_finset_1('#skF_1'('#skF_3',B_26,C_27))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_26,C_27))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_3283])).

tff(c_3499,plain,(
    ! [B_301,C_302] :
      ( ~ v1_finset_1('#skF_1'('#skF_3',B_301,C_302))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_301,C_302)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3297])).

tff(c_3506,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_3',k1_relat_1('#skF_3'),'#skF_5'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2949,c_3499])).

tff(c_3525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2945,c_3506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.92  
% 5.10/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.93  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 5.10/1.93  
% 5.10/1.93  %Foreground sorts:
% 5.10/1.93  
% 5.10/1.93  
% 5.10/1.93  %Background operators:
% 5.10/1.93  
% 5.10/1.93  
% 5.10/1.93  %Foreground operators:
% 5.10/1.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.10/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.10/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.10/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.10/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.10/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.10/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.10/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.10/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.93  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 5.10/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.10/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.93  
% 5.10/1.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.10/1.95  tff(f_110, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_finset_1)).
% 5.10/1.95  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.10/1.95  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.10/1.95  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.10/1.95  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 5.10/1.95  tff(f_54, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 5.10/1.95  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.10/1.95  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.10/1.95  tff(f_96, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_finset_1)).
% 5.10/1.95  tff(f_52, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 5.10/1.95  tff(f_79, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_finset_1)).
% 5.10/1.95  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/1.95  tff(c_44, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.10/1.95  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.10/1.95  tff(c_42, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.10/1.95  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.10/1.95  tff(c_83, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.10/1.95  tff(c_88, plain, (![A_52, B_53]: (v1_relat_1(A_52) | ~v1_relat_1(B_53) | ~r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_12, c_83])).
% 5.10/1.95  tff(c_97, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_88])).
% 5.10/1.95  tff(c_105, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_97])).
% 5.10/1.95  tff(c_498, plain, (![A_131, B_132]: (r1_tarski(k2_relat_1(A_131), k2_relat_1(B_132)) | ~r1_tarski(A_131, B_132) | ~v1_relat_1(B_132) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.10/1.95  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_15, B_16)), B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.10/1.95  tff(c_126, plain, (![A_60, C_61, B_62]: (r1_tarski(A_60, C_61) | ~r1_tarski(B_62, C_61) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.10/1.95  tff(c_136, plain, (![A_60, B_16, A_15]: (r1_tarski(A_60, B_16) | ~r1_tarski(A_60, k2_relat_1(k2_zfmisc_1(A_15, B_16))))), inference(resolution, [status(thm)], [c_20, c_126])).
% 5.10/1.95  tff(c_508, plain, (![A_131, B_16, A_15]: (r1_tarski(k2_relat_1(A_131), B_16) | ~r1_tarski(A_131, k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(A_131))), inference(resolution, [status(thm)], [c_498, c_136])).
% 5.10/1.95  tff(c_1028, plain, (![A_169, B_170, A_171]: (r1_tarski(k2_relat_1(A_169), B_170) | ~r1_tarski(A_169, k2_zfmisc_1(A_171, B_170)) | ~v1_relat_1(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_508])).
% 5.10/1.95  tff(c_1058, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_5') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1028])).
% 5.10/1.95  tff(c_1074, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1058])).
% 5.10/1.95  tff(c_1095, plain, (![C_172, A_173, B_174]: (m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~r1_tarski(k2_relat_1(C_172), B_174) | ~r1_tarski(k1_relat_1(C_172), A_173) | ~v1_relat_1(C_172))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.10/1.95  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.10/1.95  tff(c_2768, plain, (![C_274, A_275, B_276]: (r1_tarski(C_274, k2_zfmisc_1(A_275, B_276)) | ~r1_tarski(k2_relat_1(C_274), B_276) | ~r1_tarski(k1_relat_1(C_274), A_275) | ~v1_relat_1(C_274))), inference(resolution, [status(thm)], [c_1095, c_10])).
% 5.10/1.95  tff(c_2787, plain, (![A_275]: (r1_tarski('#skF_3', k2_zfmisc_1(A_275, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_3'), A_275) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1074, c_2768])).
% 5.10/1.95  tff(c_2857, plain, (![A_277]: (r1_tarski('#skF_3', k2_zfmisc_1(A_277, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_3'), A_277))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2787])).
% 5.10/1.95  tff(c_2891, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_2857])).
% 5.10/1.95  tff(c_38, plain, (![A_25, B_26, C_27]: (v1_finset_1('#skF_1'(A_25, B_26, C_27)) | ~r1_tarski(A_25, k2_zfmisc_1(B_26, C_27)) | ~v1_finset_1(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.10/1.95  tff(c_2909, plain, (v1_finset_1('#skF_1'('#skF_3', k1_relat_1('#skF_3'), '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_2891, c_38])).
% 5.10/1.95  tff(c_2945, plain, (v1_finset_1('#skF_1'('#skF_3', k1_relat_1('#skF_3'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2909])).
% 5.10/1.95  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.10/1.95  tff(c_2949, plain, (![A_3]: (r1_tarski(A_3, k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_5')) | ~r1_tarski(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_2891, c_8])).
% 5.10/1.95  tff(c_30, plain, (![A_25, B_26, C_27]: (r1_tarski(A_25, k2_zfmisc_1('#skF_1'(A_25, B_26, C_27), '#skF_2'(A_25, B_26, C_27))) | ~r1_tarski(A_25, k2_zfmisc_1(B_26, C_27)) | ~v1_finset_1(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.10/1.95  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_13, B_14)), A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.10/1.95  tff(c_56, plain, (![A_43, B_44]: (v1_finset_1(A_43) | ~v1_finset_1(B_44) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.10/1.95  tff(c_69, plain, (![A_13, B_14]: (v1_finset_1(k1_relat_1(k2_zfmisc_1(A_13, B_14))) | ~v1_finset_1(A_13))), inference(resolution, [status(thm)], [c_18, c_56])).
% 5.10/1.95  tff(c_314, plain, (![A_84, B_85]: (r1_tarski(k1_relat_1(A_84), k1_relat_1(B_85)) | ~r1_tarski(A_84, B_85) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.10/1.95  tff(c_135, plain, (![A_60, A_13, B_14]: (r1_tarski(A_60, A_13) | ~r1_tarski(A_60, k1_relat_1(k2_zfmisc_1(A_13, B_14))))), inference(resolution, [status(thm)], [c_18, c_126])).
% 5.10/1.95  tff(c_318, plain, (![A_84, A_13, B_14]: (r1_tarski(k1_relat_1(A_84), A_13) | ~r1_tarski(A_84, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_314, c_135])).
% 5.10/1.95  tff(c_551, plain, (![A_140, A_141, B_142]: (r1_tarski(k1_relat_1(A_140), A_141) | ~r1_tarski(A_140, k2_zfmisc_1(A_141, B_142)) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_318])).
% 5.10/1.95  tff(c_573, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_551])).
% 5.10/1.95  tff(c_586, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_573])).
% 5.10/1.95  tff(c_40, plain, (![D_31]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_31, '#skF_5')) | ~r1_tarski(D_31, '#skF_4') | ~v1_finset_1(D_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.10/1.95  tff(c_2922, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_4') | ~v1_finset_1(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2891, c_40])).
% 5.10/1.95  tff(c_2956, plain, (~v1_finset_1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_2922])).
% 5.10/1.95  tff(c_24, plain, (![A_17, B_19]: (r1_tarski(k1_relat_1(A_17), k1_relat_1(B_19)) | ~r1_tarski(A_17, B_19) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.10/1.95  tff(c_2872, plain, (![B_19]: (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1(B_19), '#skF_5')) | ~r1_tarski('#skF_3', B_19) | ~v1_relat_1(B_19) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_2857])).
% 5.10/1.95  tff(c_3126, plain, (![B_283]: (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1(B_283), '#skF_5')) | ~r1_tarski('#skF_3', B_283) | ~v1_relat_1(B_283))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2872])).
% 5.10/1.95  tff(c_28, plain, (![A_23, B_24]: (v1_finset_1(A_23) | ~v1_finset_1(B_24) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.10/1.95  tff(c_1815, plain, (![A_218, B_219]: (v1_finset_1(k1_relat_1(A_218)) | ~v1_finset_1(k1_relat_1(B_219)) | ~r1_tarski(A_218, B_219) | ~v1_relat_1(B_219) | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_314, c_28])).
% 5.10/1.95  tff(c_1821, plain, (![A_218, A_13, B_14]: (v1_finset_1(k1_relat_1(A_218)) | ~r1_tarski(A_218, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_218) | ~v1_finset_1(A_13))), inference(resolution, [status(thm)], [c_69, c_1815])).
% 5.10/1.95  tff(c_1830, plain, (![A_218, A_13, B_14]: (v1_finset_1(k1_relat_1(A_218)) | ~r1_tarski(A_218, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_218) | ~v1_finset_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1821])).
% 5.10/1.95  tff(c_3129, plain, (![B_283]: (v1_finset_1(k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_finset_1(k1_relat_1(B_283)) | ~r1_tarski('#skF_3', B_283) | ~v1_relat_1(B_283))), inference(resolution, [status(thm)], [c_3126, c_1830])).
% 5.10/1.95  tff(c_3163, plain, (![B_283]: (v1_finset_1(k1_relat_1('#skF_3')) | ~v1_finset_1(k1_relat_1(B_283)) | ~r1_tarski('#skF_3', B_283) | ~v1_relat_1(B_283))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_3129])).
% 5.10/1.95  tff(c_3264, plain, (![B_285]: (~v1_finset_1(k1_relat_1(B_285)) | ~r1_tarski('#skF_3', B_285) | ~v1_relat_1(B_285))), inference(negUnitSimplification, [status(thm)], [c_2956, c_3163])).
% 5.10/1.95  tff(c_3273, plain, (![A_13, B_14]: (~r1_tarski('#skF_3', k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_finset_1(A_13))), inference(resolution, [status(thm)], [c_69, c_3264])).
% 5.10/1.95  tff(c_3283, plain, (![A_286, B_287]: (~r1_tarski('#skF_3', k2_zfmisc_1(A_286, B_287)) | ~v1_finset_1(A_286))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3273])).
% 5.10/1.95  tff(c_3297, plain, (![B_26, C_27]: (~v1_finset_1('#skF_1'('#skF_3', B_26, C_27)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_26, C_27)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_3283])).
% 5.10/1.95  tff(c_3499, plain, (![B_301, C_302]: (~v1_finset_1('#skF_1'('#skF_3', B_301, C_302)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_301, C_302)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3297])).
% 5.10/1.95  tff(c_3506, plain, (~v1_finset_1('#skF_1'('#skF_3', k1_relat_1('#skF_3'), '#skF_5')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2949, c_3499])).
% 5.10/1.95  tff(c_3525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2945, c_3506])).
% 5.10/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.95  
% 5.10/1.95  Inference rules
% 5.10/1.95  ----------------------
% 5.10/1.95  #Ref     : 0
% 5.10/1.95  #Sup     : 732
% 5.10/1.95  #Fact    : 0
% 5.10/1.95  #Define  : 0
% 5.10/1.95  #Split   : 12
% 5.10/1.95  #Chain   : 0
% 5.10/1.95  #Close   : 0
% 5.10/1.95  
% 5.10/1.95  Ordering : KBO
% 5.10/1.95  
% 5.10/1.95  Simplification rules
% 5.10/1.95  ----------------------
% 5.10/1.95  #Subsume      : 96
% 5.10/1.95  #Demod        : 165
% 5.10/1.95  #Tautology    : 55
% 5.10/1.95  #SimpNegUnit  : 2
% 5.10/1.95  #BackRed      : 0
% 5.10/1.95  
% 5.10/1.95  #Partial instantiations: 0
% 5.10/1.95  #Strategies tried      : 1
% 5.10/1.95  
% 5.10/1.95  Timing (in seconds)
% 5.10/1.95  ----------------------
% 5.10/1.95  Preprocessing        : 0.29
% 5.10/1.95  Parsing              : 0.17
% 5.10/1.95  CNF conversion       : 0.02
% 5.10/1.95  Main loop            : 0.88
% 5.10/1.95  Inferencing          : 0.31
% 5.10/1.95  Reduction            : 0.28
% 5.10/1.95  Demodulation         : 0.20
% 5.10/1.95  BG Simplification    : 0.03
% 5.10/1.95  Subsumption          : 0.20
% 5.10/1.95  Abstraction          : 0.03
% 5.10/1.95  MUC search           : 0.00
% 5.10/1.95  Cooper               : 0.00
% 5.10/1.95  Total                : 1.22
% 5.10/1.95  Index Insertion      : 0.00
% 5.10/1.95  Index Deletion       : 0.00
% 5.10/1.95  Index Matching       : 0.00
% 5.10/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
