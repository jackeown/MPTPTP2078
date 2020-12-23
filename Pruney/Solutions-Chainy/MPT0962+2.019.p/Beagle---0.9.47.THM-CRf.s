%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:54 EST 2020

% Result     : Theorem 11.01s
% Output     : CNFRefutation 11.01s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 515 expanded)
%              Number of leaves         :   36 ( 176 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 (1233 expanded)
%              Number of equality atoms :   52 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_17635,plain,(
    ! [C_471,A_472,B_473] :
      ( m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473)))
      | ~ r1_tarski(k2_relat_1(C_471),B_473)
      | ~ r1_tarski(k1_relat_1(C_471),A_472)
      | ~ v1_relat_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_312,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_316,plain,(
    ! [B_68,A_69,A_70] :
      ( ~ v1_xboole_0(B_68)
      | ~ r2_hidden(A_69,A_70)
      | ~ r1_tarski(A_70,B_68) ) ),
    inference(resolution,[status(thm)],[c_30,c_312])).

tff(c_320,plain,(
    ! [B_71,A_72] :
      ( ~ v1_xboole_0(B_71)
      | ~ r1_tarski(A_72,B_71)
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_316])).

tff(c_330,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_320])).

tff(c_334,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56])).

tff(c_79,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1261,plain,(
    ! [C_114,A_115,B_116] :
      ( m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ r1_tarski(k2_relat_1(C_114),B_116)
      | ~ r1_tarski(k1_relat_1(C_114),A_115)
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5189,plain,(
    ! [C_153,A_154,B_155] :
      ( r1_tarski(C_153,k2_zfmisc_1(A_154,B_155))
      | ~ r1_tarski(k2_relat_1(C_153),B_155)
      | ~ r1_tarski(k1_relat_1(C_153),A_154)
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_1261,c_28])).

tff(c_5191,plain,(
    ! [A_154] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_154,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_154)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_5189])).

tff(c_5199,plain,(
    ! [A_156] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_156,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5191])).

tff(c_5204,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_5199])).

tff(c_449,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_454,plain,(
    ! [A_79,B_80,A_17] :
      ( k1_relset_1(A_79,B_80,A_17) = k1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_30,c_449])).

tff(c_5213,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5204,c_454])).

tff(c_1850,plain,(
    ! [B_124,C_125,A_126] :
      ( k1_xboole_0 = B_124
      | v1_funct_2(C_125,A_126,B_124)
      | k1_relset_1(A_126,B_124,C_125) != A_126
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5310,plain,(
    ! [B_161,A_162,A_163] :
      ( k1_xboole_0 = B_161
      | v1_funct_2(A_162,A_163,B_161)
      | k1_relset_1(A_163,B_161,A_162) != A_163
      | ~ r1_tarski(A_162,k2_zfmisc_1(A_163,B_161)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1850])).

tff(c_5316,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5204,c_5310])).

tff(c_5328,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5213,c_5316])).

tff(c_5329,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_5328])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_217,plain,(
    ! [B_55,A_56] :
      ( ~ r1_xboole_0(B_55,A_56)
      | ~ r1_tarski(B_55,A_56)
      | v1_xboole_0(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_220,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_223,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_220])).

tff(c_5356,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5329,c_223])).

tff(c_5366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_5356])).

tff(c_5368,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5385,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5368,c_8])).

tff(c_5396,plain,(
    ! [A_11] : r1_tarski('#skF_2',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5385,c_18])).

tff(c_257,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_264,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_257])).

tff(c_283,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_5429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5396,c_283])).

tff(c_5430,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_38,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_relat_1(A_24))
      | ~ v1_relat_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5437,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5430,c_38])).

tff(c_5441,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5437])).

tff(c_5466,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5441])).

tff(c_6412,plain,(
    ! [C_214,A_215,B_216] :
      ( m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ r1_tarski(k2_relat_1(C_214),B_216)
      | ~ r1_tarski(k1_relat_1(C_214),A_215)
      | ~ v1_relat_1(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_9337,plain,(
    ! [C_250,A_251,B_252] :
      ( r1_tarski(C_250,k2_zfmisc_1(A_251,B_252))
      | ~ r1_tarski(k2_relat_1(C_250),B_252)
      | ~ r1_tarski(k1_relat_1(C_250),A_251)
      | ~ v1_relat_1(C_250) ) ),
    inference(resolution,[status(thm)],[c_6412,c_28])).

tff(c_9346,plain,(
    ! [C_253,A_254] :
      ( r1_tarski(C_253,k2_zfmisc_1(A_254,k2_relat_1(C_253)))
      | ~ r1_tarski(k1_relat_1(C_253),A_254)
      | ~ v1_relat_1(C_253) ) ),
    inference(resolution,[status(thm)],[c_14,c_9337])).

tff(c_9368,plain,(
    ! [A_254] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_254,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_254)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5430,c_9346])).

tff(c_9377,plain,(
    ! [A_255] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_255,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9368])).

tff(c_9387,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_9377])).

tff(c_5491,plain,(
    ! [A_173,B_174,C_175] :
      ( k1_relset_1(A_173,B_174,C_175) = k1_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5496,plain,(
    ! [A_173,B_174,A_17] :
      ( k1_relset_1(A_173,B_174,A_17) = k1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_173,B_174)) ) ),
    inference(resolution,[status(thm)],[c_30,c_5491])).

tff(c_9396,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9387,c_5496])).

tff(c_6840,plain,(
    ! [B_224,C_225,A_226] :
      ( k1_xboole_0 = B_224
      | v1_funct_2(C_225,A_226,B_224)
      | k1_relset_1(A_226,B_224,C_225) != A_226
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_9550,plain,(
    ! [B_270,A_271,A_272] :
      ( k1_xboole_0 = B_270
      | v1_funct_2(A_271,A_272,B_270)
      | k1_relset_1(A_272,B_270,A_271) != A_272
      | ~ r1_tarski(A_271,k2_zfmisc_1(A_272,B_270)) ) ),
    inference(resolution,[status(thm)],[c_30,c_6840])).

tff(c_9556,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9387,c_9550])).

tff(c_9571,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9396,c_9556])).

tff(c_9572,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_9571])).

tff(c_9602,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9572,c_223])).

tff(c_9612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5466,c_9602])).

tff(c_9613,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5441])).

tff(c_9628,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9613,c_8])).

tff(c_9614,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5441])).

tff(c_9642,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_9614,c_8])).

tff(c_9663,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9628,c_9642])).

tff(c_80,plain,(
    ! [A_40] :
      ( v1_xboole_0(k1_relat_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84,plain,(
    ! [A_40] :
      ( k1_relat_1(A_40) = k1_xboole_0
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_80,c_8])).

tff(c_9641,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9614,c_84])).

tff(c_9673,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9663,c_9628,c_9641])).

tff(c_9656,plain,(
    ! [A_11] : r1_tarski('#skF_3',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9628,c_18])).

tff(c_9790,plain,(
    ! [A_280,B_281,C_282] :
      ( k1_relset_1(A_280,B_281,C_282) = k1_relat_1(C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10034,plain,(
    ! [A_306,B_307,A_308] :
      ( k1_relset_1(A_306,B_307,A_308) = k1_relat_1(A_308)
      | ~ r1_tarski(A_308,k2_zfmisc_1(A_306,B_307)) ) ),
    inference(resolution,[status(thm)],[c_30,c_9790])).

tff(c_10038,plain,(
    ! [A_306,B_307] : k1_relset_1(A_306,B_307,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9656,c_10034])).

tff(c_10044,plain,(
    ! [A_306,B_307] : k1_relset_1(A_306,B_307,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9673,c_10038])).

tff(c_48,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_9906,plain,(
    ! [C_296,B_297] :
      ( v1_funct_2(C_296,'#skF_3',B_297)
      | k1_relset_1('#skF_3',B_297,C_296) != '#skF_3'
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_297))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9628,c_9628,c_9628,c_9628,c_48])).

tff(c_16572,plain,(
    ! [A_399,B_400] :
      ( v1_funct_2(A_399,'#skF_3',B_400)
      | k1_relset_1('#skF_3',B_400,A_399) != '#skF_3'
      | ~ r1_tarski(A_399,k2_zfmisc_1('#skF_3',B_400)) ) ),
    inference(resolution,[status(thm)],[c_30,c_9906])).

tff(c_16584,plain,(
    ! [B_400] :
      ( v1_funct_2('#skF_3','#skF_3',B_400)
      | k1_relset_1('#skF_3',B_400,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_9656,c_16572])).

tff(c_16593,plain,(
    ! [B_400] : v1_funct_2('#skF_3','#skF_3',B_400) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10044,c_16584])).

tff(c_9667,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9663,c_79])).

tff(c_9718,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9673,c_9667])).

tff(c_16736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16593,c_9718])).

tff(c_16737,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_17658,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_17635,c_16737])).

tff(c_17668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14,c_58,c_17658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:18:23 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.01/3.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.01/3.49  
% 11.01/3.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.01/3.50  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 11.01/3.50  
% 11.01/3.50  %Foreground sorts:
% 11.01/3.50  
% 11.01/3.50  
% 11.01/3.50  %Background operators:
% 11.01/3.50  
% 11.01/3.50  
% 11.01/3.50  %Foreground operators:
% 11.01/3.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.01/3.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.01/3.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.01/3.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.01/3.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.01/3.50  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 11.01/3.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.01/3.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.01/3.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.01/3.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.01/3.50  tff('#skF_2', type, '#skF_2': $i).
% 11.01/3.50  tff('#skF_3', type, '#skF_3': $i).
% 11.01/3.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.01/3.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.01/3.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.01/3.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.01/3.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.01/3.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.01/3.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.01/3.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.01/3.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.01/3.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.01/3.50  
% 11.01/3.52  tff(f_145, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 11.01/3.52  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.01/3.52  tff(f_114, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 11.01/3.52  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.01/3.52  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.01/3.52  tff(f_86, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 11.01/3.52  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.01/3.52  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.01/3.52  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.01/3.52  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 11.01/3.52  tff(f_67, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 11.01/3.52  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.01/3.52  tff(f_102, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 11.01/3.52  tff(f_94, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 11.01/3.52  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.01/3.52  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.01/3.52  tff(c_58, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.01/3.52  tff(c_17635, plain, (![C_471, A_472, B_473]: (m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))) | ~r1_tarski(k2_relat_1(C_471), B_473) | ~r1_tarski(k1_relat_1(C_471), A_472) | ~v1_relat_1(C_471))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.01/3.52  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.01/3.52  tff(c_30, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.01/3.52  tff(c_312, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.01/3.52  tff(c_316, plain, (![B_68, A_69, A_70]: (~v1_xboole_0(B_68) | ~r2_hidden(A_69, A_70) | ~r1_tarski(A_70, B_68))), inference(resolution, [status(thm)], [c_30, c_312])).
% 11.01/3.52  tff(c_320, plain, (![B_71, A_72]: (~v1_xboole_0(B_71) | ~r1_tarski(A_72, B_71) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_6, c_316])).
% 11.01/3.52  tff(c_330, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_320])).
% 11.01/3.52  tff(c_334, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_330])).
% 11.01/3.52  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.01/3.52  tff(c_56, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.01/3.52  tff(c_64, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56])).
% 11.01/3.52  tff(c_79, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 11.01/3.52  tff(c_1261, plain, (![C_114, A_115, B_116]: (m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~r1_tarski(k2_relat_1(C_114), B_116) | ~r1_tarski(k1_relat_1(C_114), A_115) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.01/3.52  tff(c_28, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.01/3.52  tff(c_5189, plain, (![C_153, A_154, B_155]: (r1_tarski(C_153, k2_zfmisc_1(A_154, B_155)) | ~r1_tarski(k2_relat_1(C_153), B_155) | ~r1_tarski(k1_relat_1(C_153), A_154) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_1261, c_28])).
% 11.01/3.52  tff(c_5191, plain, (![A_154]: (r1_tarski('#skF_3', k2_zfmisc_1(A_154, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_154) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_5189])).
% 11.01/3.52  tff(c_5199, plain, (![A_156]: (r1_tarski('#skF_3', k2_zfmisc_1(A_156, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5191])).
% 11.01/3.52  tff(c_5204, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_5199])).
% 11.01/3.52  tff(c_449, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.01/3.52  tff(c_454, plain, (![A_79, B_80, A_17]: (k1_relset_1(A_79, B_80, A_17)=k1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_79, B_80)))), inference(resolution, [status(thm)], [c_30, c_449])).
% 11.01/3.52  tff(c_5213, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5204, c_454])).
% 11.01/3.52  tff(c_1850, plain, (![B_124, C_125, A_126]: (k1_xboole_0=B_124 | v1_funct_2(C_125, A_126, B_124) | k1_relset_1(A_126, B_124, C_125)!=A_126 | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_124))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.01/3.52  tff(c_5310, plain, (![B_161, A_162, A_163]: (k1_xboole_0=B_161 | v1_funct_2(A_162, A_163, B_161) | k1_relset_1(A_163, B_161, A_162)!=A_163 | ~r1_tarski(A_162, k2_zfmisc_1(A_163, B_161)))), inference(resolution, [status(thm)], [c_30, c_1850])).
% 11.01/3.52  tff(c_5316, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5204, c_5310])).
% 11.01/3.52  tff(c_5328, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5213, c_5316])).
% 11.01/3.52  tff(c_5329, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_79, c_5328])).
% 11.01/3.52  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.01/3.52  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.01/3.52  tff(c_217, plain, (![B_55, A_56]: (~r1_xboole_0(B_55, A_56) | ~r1_tarski(B_55, A_56) | v1_xboole_0(B_55))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.01/3.52  tff(c_220, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_217])).
% 11.01/3.52  tff(c_223, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_220])).
% 11.01/3.52  tff(c_5356, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5329, c_223])).
% 11.01/3.52  tff(c_5366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_5356])).
% 11.01/3.52  tff(c_5368, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_330])).
% 11.01/3.52  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.01/3.52  tff(c_5385, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_5368, c_8])).
% 11.01/3.52  tff(c_5396, plain, (![A_11]: (r1_tarski('#skF_2', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_5385, c_18])).
% 11.01/3.52  tff(c_257, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.01/3.52  tff(c_264, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_257])).
% 11.01/3.52  tff(c_283, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_264])).
% 11.01/3.52  tff(c_5429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5396, c_283])).
% 11.01/3.52  tff(c_5430, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_264])).
% 11.01/3.52  tff(c_38, plain, (![A_24]: (~v1_xboole_0(k2_relat_1(A_24)) | ~v1_relat_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.01/3.52  tff(c_5437, plain, (~v1_xboole_0('#skF_2') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5430, c_38])).
% 11.01/3.52  tff(c_5441, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5437])).
% 11.01/3.52  tff(c_5466, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5441])).
% 11.01/3.52  tff(c_6412, plain, (![C_214, A_215, B_216]: (m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~r1_tarski(k2_relat_1(C_214), B_216) | ~r1_tarski(k1_relat_1(C_214), A_215) | ~v1_relat_1(C_214))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.01/3.52  tff(c_9337, plain, (![C_250, A_251, B_252]: (r1_tarski(C_250, k2_zfmisc_1(A_251, B_252)) | ~r1_tarski(k2_relat_1(C_250), B_252) | ~r1_tarski(k1_relat_1(C_250), A_251) | ~v1_relat_1(C_250))), inference(resolution, [status(thm)], [c_6412, c_28])).
% 11.01/3.52  tff(c_9346, plain, (![C_253, A_254]: (r1_tarski(C_253, k2_zfmisc_1(A_254, k2_relat_1(C_253))) | ~r1_tarski(k1_relat_1(C_253), A_254) | ~v1_relat_1(C_253))), inference(resolution, [status(thm)], [c_14, c_9337])).
% 11.01/3.52  tff(c_9368, plain, (![A_254]: (r1_tarski('#skF_3', k2_zfmisc_1(A_254, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_254) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5430, c_9346])).
% 11.01/3.52  tff(c_9377, plain, (![A_255]: (r1_tarski('#skF_3', k2_zfmisc_1(A_255, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_255))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9368])).
% 11.01/3.52  tff(c_9387, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_9377])).
% 11.01/3.52  tff(c_5491, plain, (![A_173, B_174, C_175]: (k1_relset_1(A_173, B_174, C_175)=k1_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.01/3.52  tff(c_5496, plain, (![A_173, B_174, A_17]: (k1_relset_1(A_173, B_174, A_17)=k1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_173, B_174)))), inference(resolution, [status(thm)], [c_30, c_5491])).
% 11.01/3.52  tff(c_9396, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_9387, c_5496])).
% 11.01/3.52  tff(c_6840, plain, (![B_224, C_225, A_226]: (k1_xboole_0=B_224 | v1_funct_2(C_225, A_226, B_224) | k1_relset_1(A_226, B_224, C_225)!=A_226 | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_224))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.01/3.52  tff(c_9550, plain, (![B_270, A_271, A_272]: (k1_xboole_0=B_270 | v1_funct_2(A_271, A_272, B_270) | k1_relset_1(A_272, B_270, A_271)!=A_272 | ~r1_tarski(A_271, k2_zfmisc_1(A_272, B_270)))), inference(resolution, [status(thm)], [c_30, c_6840])).
% 11.01/3.52  tff(c_9556, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_9387, c_9550])).
% 11.01/3.52  tff(c_9571, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9396, c_9556])).
% 11.01/3.52  tff(c_9572, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_79, c_9571])).
% 11.01/3.52  tff(c_9602, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9572, c_223])).
% 11.01/3.52  tff(c_9612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5466, c_9602])).
% 11.01/3.52  tff(c_9613, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_5441])).
% 11.01/3.52  tff(c_9628, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9613, c_8])).
% 11.01/3.52  tff(c_9614, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_5441])).
% 11.01/3.52  tff(c_9642, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_9614, c_8])).
% 11.01/3.52  tff(c_9663, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9628, c_9642])).
% 11.01/3.52  tff(c_80, plain, (![A_40]: (v1_xboole_0(k1_relat_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.01/3.52  tff(c_84, plain, (![A_40]: (k1_relat_1(A_40)=k1_xboole_0 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_80, c_8])).
% 11.01/3.52  tff(c_9641, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_9614, c_84])).
% 11.01/3.52  tff(c_9673, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9663, c_9628, c_9641])).
% 11.01/3.52  tff(c_9656, plain, (![A_11]: (r1_tarski('#skF_3', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_9628, c_18])).
% 11.01/3.52  tff(c_9790, plain, (![A_280, B_281, C_282]: (k1_relset_1(A_280, B_281, C_282)=k1_relat_1(C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.01/3.52  tff(c_10034, plain, (![A_306, B_307, A_308]: (k1_relset_1(A_306, B_307, A_308)=k1_relat_1(A_308) | ~r1_tarski(A_308, k2_zfmisc_1(A_306, B_307)))), inference(resolution, [status(thm)], [c_30, c_9790])).
% 11.01/3.52  tff(c_10038, plain, (![A_306, B_307]: (k1_relset_1(A_306, B_307, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_9656, c_10034])).
% 11.01/3.52  tff(c_10044, plain, (![A_306, B_307]: (k1_relset_1(A_306, B_307, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9673, c_10038])).
% 11.01/3.52  tff(c_48, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.01/3.52  tff(c_9906, plain, (![C_296, B_297]: (v1_funct_2(C_296, '#skF_3', B_297) | k1_relset_1('#skF_3', B_297, C_296)!='#skF_3' | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_297))))), inference(demodulation, [status(thm), theory('equality')], [c_9628, c_9628, c_9628, c_9628, c_48])).
% 11.01/3.52  tff(c_16572, plain, (![A_399, B_400]: (v1_funct_2(A_399, '#skF_3', B_400) | k1_relset_1('#skF_3', B_400, A_399)!='#skF_3' | ~r1_tarski(A_399, k2_zfmisc_1('#skF_3', B_400)))), inference(resolution, [status(thm)], [c_30, c_9906])).
% 11.01/3.52  tff(c_16584, plain, (![B_400]: (v1_funct_2('#skF_3', '#skF_3', B_400) | k1_relset_1('#skF_3', B_400, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_9656, c_16572])).
% 11.01/3.52  tff(c_16593, plain, (![B_400]: (v1_funct_2('#skF_3', '#skF_3', B_400))), inference(demodulation, [status(thm), theory('equality')], [c_10044, c_16584])).
% 11.01/3.52  tff(c_9667, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9663, c_79])).
% 11.01/3.52  tff(c_9718, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9673, c_9667])).
% 11.01/3.52  tff(c_16736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16593, c_9718])).
% 11.01/3.52  tff(c_16737, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_64])).
% 11.01/3.52  tff(c_17658, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_17635, c_16737])).
% 11.01/3.52  tff(c_17668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_14, c_58, c_17658])).
% 11.01/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.01/3.52  
% 11.01/3.52  Inference rules
% 11.01/3.52  ----------------------
% 11.01/3.52  #Ref     : 0
% 11.01/3.52  #Sup     : 5112
% 11.01/3.52  #Fact    : 0
% 11.01/3.52  #Define  : 0
% 11.01/3.52  #Split   : 33
% 11.01/3.52  #Chain   : 0
% 11.01/3.52  #Close   : 0
% 11.01/3.52  
% 11.01/3.52  Ordering : KBO
% 11.01/3.52  
% 11.01/3.52  Simplification rules
% 11.01/3.52  ----------------------
% 11.01/3.52  #Subsume      : 2385
% 11.01/3.52  #Demod        : 2678
% 11.01/3.52  #Tautology    : 842
% 11.01/3.52  #SimpNegUnit  : 9
% 11.01/3.52  #BackRed      : 97
% 11.01/3.52  
% 11.01/3.52  #Partial instantiations: 0
% 11.01/3.52  #Strategies tried      : 1
% 11.01/3.52  
% 11.01/3.52  Timing (in seconds)
% 11.01/3.52  ----------------------
% 11.01/3.52  Preprocessing        : 0.34
% 11.01/3.52  Parsing              : 0.18
% 11.01/3.52  CNF conversion       : 0.02
% 11.01/3.52  Main loop            : 2.41
% 11.01/3.52  Inferencing          : 0.64
% 11.01/3.52  Reduction            : 0.64
% 11.01/3.52  Demodulation         : 0.46
% 11.01/3.52  BG Simplification    : 0.10
% 11.32/3.52  Subsumption          : 0.89
% 11.32/3.52  Abstraction          : 0.13
% 11.32/3.52  MUC search           : 0.00
% 11.32/3.52  Cooper               : 0.00
% 11.32/3.52  Total                : 2.79
% 11.32/3.52  Index Insertion      : 0.00
% 11.32/3.52  Index Deletion       : 0.00
% 11.32/3.52  Index Matching       : 0.00
% 11.32/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
