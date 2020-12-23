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
% DateTime   : Thu Dec  3 10:13:41 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  172 (1359 expanded)
%              Number of leaves         :   37 ( 438 expanded)
%              Depth                    :   15
%              Number of atoms          :  290 (4489 expanded)
%              Number of equality atoms :   79 (1651 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_54,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_95,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_101,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_98])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_65,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1305,plain,(
    ! [A_241,B_242,C_243] :
      ( k1_relset_1(A_241,B_242,C_243) = k1_relat_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1319,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1305])).

tff(c_1497,plain,(
    ! [B_282,A_283,C_284] :
      ( k1_xboole_0 = B_282
      | k1_relset_1(A_283,B_282,C_284) = A_283
      | ~ v1_funct_2(C_284,A_283,B_282)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_283,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1506,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1497])).

tff(c_1518,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1319,c_1506])).

tff(c_1519,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1518])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1528,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1519,c_22])).

tff(c_1534,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1528])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1414,plain,(
    ! [A_275,B_276,C_277,D_278] :
      ( k2_partfun1(A_275,B_276,C_277,D_278) = k7_relat_1(C_277,D_278)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_1(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1420,plain,(
    ! [D_278] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_278) = k7_relat_1('#skF_4',D_278)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_1414])).

tff(c_1431,plain,(
    ! [D_278] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_278) = k7_relat_1('#skF_4',D_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1420])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_448,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k2_partfun1(A_146,B_147,C_148,D_149) = k7_relat_1(C_148,D_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_452,plain,(
    ! [D_149] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_149) = k7_relat_1('#skF_4',D_149)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_448])).

tff(c_460,plain,(
    ! [D_149] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_149) = k7_relat_1('#skF_4',D_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_452])).

tff(c_1073,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( m1_subset_1(k2_partfun1(A_216,B_217,C_218,D_219),k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_1(C_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1098,plain,(
    ! [D_149] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_1073])).

tff(c_1125,plain,(
    ! [D_221] : m1_subset_1(k7_relat_1('#skF_4',D_221),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1098])).

tff(c_24,plain,(
    ! [C_19,B_18,A_17] :
      ( v5_relat_1(C_19,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1163,plain,(
    ! [D_221] : v5_relat_1(k7_relat_1('#skF_4',D_221),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1125,c_24])).

tff(c_747,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( m1_subset_1(k2_partfun1(A_183,B_184,C_185,D_186),k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_772,plain,(
    ! [D_149] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_747])).

tff(c_806,plain,(
    ! [D_189] : m1_subset_1(k7_relat_1('#skF_4',D_189),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_772])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( v1_relat_1(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_828,plain,(
    ! [D_189] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_189))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_806,c_10])).

tff(c_848,plain,(
    ! [D_189] : v1_relat_1(k7_relat_1('#skF_4',D_189)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_828])).

tff(c_378,plain,(
    ! [C_131,A_132,B_133] :
      ( m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ r1_tarski(k2_relat_1(C_131),B_133)
      | ~ r1_tarski(k1_relat_1(C_131),A_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_239,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( v1_funct_1(k2_partfun1(A_84,B_85,C_86,D_87))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_241,plain,(
    ! [D_87] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_87))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_239])).

tff(c_248,plain,(
    ! [D_87] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_241])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_143])).

tff(c_252,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_255,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_404,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_378,c_255])).

tff(c_480,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_460,c_460,c_404])).

tff(c_481,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_481])).

tff(c_860,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_859,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_861,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_864,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_861])).

tff(c_867,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_864])).

tff(c_1182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_867])).

tff(c_1183,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_1204,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1183])).

tff(c_1208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1204])).

tff(c_1209,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_1441,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1209])).

tff(c_1210,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_1318,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1210,c_1305])).

tff(c_1436,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1431,c_1318])).

tff(c_1440,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1210])).

tff(c_1710,plain,(
    ! [B_296,C_297,A_298] :
      ( k1_xboole_0 = B_296
      | v1_funct_2(C_297,A_298,B_296)
      | k1_relset_1(A_298,B_296,C_297) != A_298
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_298,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1713,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1440,c_1710])).

tff(c_1727,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_1713])).

tff(c_1728,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1441,c_65,c_1727])).

tff(c_1737,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1534,c_1728])).

tff(c_1741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1737])).

tff(c_1742,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1758,plain,(
    ! [B_301] : k2_zfmisc_1('#skF_1',B_301) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_8])).

tff(c_1762,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1758,c_16])).

tff(c_1756,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_8])).

tff(c_1743,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1748,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1743])).

tff(c_1754,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_56])).

tff(c_1757,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_1754])).

tff(c_2063,plain,(
    ! [B_358,A_359] :
      ( v1_relat_1(B_358)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(A_359))
      | ~ v1_relat_1(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2066,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1757,c_2063])).

tff(c_2069,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_2066])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1767,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_6])).

tff(c_2119,plain,(
    ! [C_372,A_373,B_374] :
      ( v4_relat_1(C_372,A_373)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2126,plain,(
    ! [C_375,A_376] :
      ( v4_relat_1(C_375,A_376)
      | ~ m1_subset_1(C_375,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_2119])).

tff(c_2129,plain,(
    ! [A_376] : v4_relat_1('#skF_4',A_376) ),
    inference(resolution,[status(thm)],[c_1757,c_2126])).

tff(c_2162,plain,(
    ! [B_382,A_383] :
      ( k7_relat_1(B_382,A_383) = B_382
      | ~ v4_relat_1(B_382,A_383)
      | ~ v1_relat_1(B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2165,plain,(
    ! [A_376] :
      ( k7_relat_1('#skF_4',A_376) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2129,c_2162])).

tff(c_2168,plain,(
    ! [A_376] : k7_relat_1('#skF_4',A_376) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_2165])).

tff(c_2316,plain,(
    ! [A_414,B_415,C_416,D_417] :
      ( k2_partfun1(A_414,B_415,C_416,D_417) = k7_relat_1(C_416,D_417)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415)))
      | ~ v1_funct_1(C_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2328,plain,(
    ! [A_423,C_424,D_425] :
      ( k2_partfun1(A_423,'#skF_1',C_424,D_425) = k7_relat_1(C_424,D_425)
      | ~ m1_subset_1(C_424,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_424) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_2316])).

tff(c_2330,plain,(
    ! [A_423,D_425] :
      ( k2_partfun1(A_423,'#skF_1','#skF_4',D_425) = k7_relat_1('#skF_4',D_425)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1757,c_2328])).

tff(c_2333,plain,(
    ! [A_423,D_425] : k2_partfun1(A_423,'#skF_1','#skF_4',D_425) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2168,c_2330])).

tff(c_2046,plain,(
    ! [A_351,B_352,C_353,D_354] :
      ( v1_funct_1(k2_partfun1(A_351,B_352,C_353,D_354))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ v1_funct_1(C_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2051,plain,(
    ! [A_355,C_356,D_357] :
      ( v1_funct_1(k2_partfun1(A_355,'#skF_1',C_356,D_357))
      | ~ m1_subset_1(C_356,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_356) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_2046])).

tff(c_2053,plain,(
    ! [A_355,D_357] :
      ( v1_funct_1(k2_partfun1(A_355,'#skF_1','#skF_4',D_357))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1757,c_2051])).

tff(c_2056,plain,(
    ! [A_355,D_357] : v1_funct_1(k2_partfun1(A_355,'#skF_1','#skF_4',D_357)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2053])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1787,plain,(
    ! [A_303] :
      ( A_303 = '#skF_1'
      | ~ r1_tarski(A_303,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_2])).

tff(c_1791,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_1787])).

tff(c_1802,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_1748,c_1791,c_1791,c_1748,c_1748,c_1791,c_1767,c_1748,c_1748,c_50])).

tff(c_1803,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1802])).

tff(c_2059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1803])).

tff(c_2060,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1802])).

tff(c_2062,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2060])).

tff(c_2335,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2333,c_2062])).

tff(c_2339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_2335])).

tff(c_2341,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2060])).

tff(c_2382,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2341,c_10])).

tff(c_2385,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_2382])).

tff(c_2476,plain,(
    ! [C_449,A_450,B_451] :
      ( v4_relat_1(C_449,A_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2483,plain,(
    ! [C_452,A_453] :
      ( v4_relat_1(C_452,A_453)
      | ~ m1_subset_1(C_452,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_2476])).

tff(c_2497,plain,(
    ! [A_455] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_455) ),
    inference(resolution,[status(thm)],[c_2341,c_2483])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2500,plain,(
    ! [A_455] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_455) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2497,c_18])).

tff(c_2568,plain,(
    ! [A_464] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_464) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2385,c_2500])).

tff(c_2361,plain,(
    ! [B_430,A_431] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_430,A_431)),A_431)
      | ~ v1_relat_1(B_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1786,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_2])).

tff(c_2366,plain,(
    ! [B_430] :
      ( k1_relat_1(k7_relat_1(B_430,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_430) ) ),
    inference(resolution,[status(thm)],[c_2361,c_1786])).

tff(c_2574,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2568,c_2366])).

tff(c_2582,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2385,c_2574])).

tff(c_2561,plain,(
    ! [A_461,B_462,C_463] :
      ( k1_relset_1(A_461,B_462,C_463) = k1_relat_1(C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2596,plain,(
    ! [B_465,C_466] :
      ( k1_relset_1('#skF_1',B_465,C_466) = k1_relat_1(C_466)
      | ~ m1_subset_1(C_466,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_2561])).

tff(c_2598,plain,(
    ! [B_465] : k1_relset_1('#skF_1',B_465,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2341,c_2596])).

tff(c_2602,plain,(
    ! [B_465] : k1_relset_1('#skF_1',B_465,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_2598])).

tff(c_36,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_62,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_2697,plain,(
    ! [C_491,B_492] :
      ( v1_funct_2(C_491,'#skF_1',B_492)
      | k1_relset_1('#skF_1',B_492,C_491) != '#skF_1'
      | ~ m1_subset_1(C_491,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_1742,c_1742,c_62])).

tff(c_2699,plain,(
    ! [B_492] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_492)
      | k1_relset_1('#skF_1',B_492,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2341,c_2697])).

tff(c_2704,plain,(
    ! [B_492] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_492) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2602,c_2699])).

tff(c_2340,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2060])).

tff(c_2724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:18:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.79  
% 4.52/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.79  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.52/1.79  
% 4.52/1.79  %Foreground sorts:
% 4.52/1.79  
% 4.52/1.79  
% 4.52/1.79  %Background operators:
% 4.52/1.79  
% 4.52/1.79  
% 4.52/1.79  %Foreground operators:
% 4.52/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.52/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.52/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.52/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.52/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.52/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.52/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.52/1.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.52/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.52/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.52/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.79  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.52/1.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.52/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.52/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.79  
% 4.52/1.82  tff(f_136, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 4.52/1.82  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.52/1.82  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.52/1.82  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.52/1.82  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.52/1.82  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 4.52/1.82  tff(f_116, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.52/1.82  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 4.52/1.82  tff(f_110, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.52/1.82  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.52/1.82  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.52/1.82  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.52/1.82  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.52/1.82  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.52/1.82  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.52/1.82  tff(c_54, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.52/1.82  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.82  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.52/1.82  tff(c_95, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.82  tff(c_98, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_95])).
% 4.52/1.82  tff(c_101, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_98])).
% 4.52/1.82  tff(c_52, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.52/1.82  tff(c_65, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 4.52/1.82  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.52/1.82  tff(c_1305, plain, (![A_241, B_242, C_243]: (k1_relset_1(A_241, B_242, C_243)=k1_relat_1(C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.52/1.82  tff(c_1319, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1305])).
% 4.52/1.82  tff(c_1497, plain, (![B_282, A_283, C_284]: (k1_xboole_0=B_282 | k1_relset_1(A_283, B_282, C_284)=A_283 | ~v1_funct_2(C_284, A_283, B_282) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_283, B_282))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.52/1.82  tff(c_1506, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1497])).
% 4.52/1.82  tff(c_1518, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1319, c_1506])).
% 4.52/1.82  tff(c_1519, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_65, c_1518])).
% 4.52/1.82  tff(c_22, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.52/1.82  tff(c_1528, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1519, c_22])).
% 4.52/1.82  tff(c_1534, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1528])).
% 4.52/1.82  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.52/1.82  tff(c_1414, plain, (![A_275, B_276, C_277, D_278]: (k2_partfun1(A_275, B_276, C_277, D_278)=k7_relat_1(C_277, D_278) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_1(C_277))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.52/1.82  tff(c_1420, plain, (![D_278]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_278)=k7_relat_1('#skF_4', D_278) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_1414])).
% 4.52/1.82  tff(c_1431, plain, (![D_278]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_278)=k7_relat_1('#skF_4', D_278))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1420])).
% 4.52/1.82  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.52/1.82  tff(c_448, plain, (![A_146, B_147, C_148, D_149]: (k2_partfun1(A_146, B_147, C_148, D_149)=k7_relat_1(C_148, D_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_1(C_148))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.52/1.82  tff(c_452, plain, (![D_149]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)=k7_relat_1('#skF_4', D_149) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_448])).
% 4.52/1.82  tff(c_460, plain, (![D_149]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)=k7_relat_1('#skF_4', D_149))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_452])).
% 4.52/1.82  tff(c_1073, plain, (![A_216, B_217, C_218, D_219]: (m1_subset_1(k2_partfun1(A_216, B_217, C_218, D_219), k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_1(C_218))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.52/1.82  tff(c_1098, plain, (![D_149]: (m1_subset_1(k7_relat_1('#skF_4', D_149), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_460, c_1073])).
% 4.52/1.82  tff(c_1125, plain, (![D_221]: (m1_subset_1(k7_relat_1('#skF_4', D_221), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1098])).
% 4.52/1.82  tff(c_24, plain, (![C_19, B_18, A_17]: (v5_relat_1(C_19, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.52/1.82  tff(c_1163, plain, (![D_221]: (v5_relat_1(k7_relat_1('#skF_4', D_221), '#skF_2'))), inference(resolution, [status(thm)], [c_1125, c_24])).
% 4.52/1.82  tff(c_747, plain, (![A_183, B_184, C_185, D_186]: (m1_subset_1(k2_partfun1(A_183, B_184, C_185, D_186), k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.52/1.82  tff(c_772, plain, (![D_149]: (m1_subset_1(k7_relat_1('#skF_4', D_149), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_460, c_747])).
% 4.52/1.82  tff(c_806, plain, (![D_189]: (m1_subset_1(k7_relat_1('#skF_4', D_189), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_772])).
% 4.52/1.82  tff(c_10, plain, (![B_6, A_4]: (v1_relat_1(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.82  tff(c_828, plain, (![D_189]: (v1_relat_1(k7_relat_1('#skF_4', D_189)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_806, c_10])).
% 4.52/1.82  tff(c_848, plain, (![D_189]: (v1_relat_1(k7_relat_1('#skF_4', D_189)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_828])).
% 4.52/1.82  tff(c_378, plain, (![C_131, A_132, B_133]: (m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~r1_tarski(k2_relat_1(C_131), B_133) | ~r1_tarski(k1_relat_1(C_131), A_132) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.52/1.82  tff(c_239, plain, (![A_84, B_85, C_86, D_87]: (v1_funct_1(k2_partfun1(A_84, B_85, C_86, D_87)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.52/1.82  tff(c_241, plain, (![D_87]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_87)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_239])).
% 4.52/1.82  tff(c_248, plain, (![D_87]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_87)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_241])).
% 4.52/1.82  tff(c_50, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.52/1.82  tff(c_143, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 4.52/1.82  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_143])).
% 4.52/1.82  tff(c_252, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_50])).
% 4.52/1.82  tff(c_255, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_252])).
% 4.52/1.82  tff(c_404, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_378, c_255])).
% 4.52/1.82  tff(c_480, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_460, c_460, c_404])).
% 4.52/1.82  tff(c_481, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_480])).
% 4.52/1.82  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_848, c_481])).
% 4.52/1.82  tff(c_860, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_480])).
% 4.52/1.82  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.52/1.82  tff(c_859, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_480])).
% 4.52/1.82  tff(c_861, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_859])).
% 4.52/1.82  tff(c_864, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_861])).
% 4.52/1.82  tff(c_867, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_864])).
% 4.52/1.82  tff(c_1182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1163, c_867])).
% 4.52/1.82  tff(c_1183, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_859])).
% 4.52/1.82  tff(c_1204, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_1183])).
% 4.52/1.82  tff(c_1208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_1204])).
% 4.52/1.82  tff(c_1209, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_252])).
% 4.52/1.82  tff(c_1441, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1209])).
% 4.52/1.82  tff(c_1210, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_252])).
% 4.52/1.82  tff(c_1318, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1210, c_1305])).
% 4.52/1.82  tff(c_1436, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1431, c_1318])).
% 4.52/1.82  tff(c_1440, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1210])).
% 4.52/1.82  tff(c_1710, plain, (![B_296, C_297, A_298]: (k1_xboole_0=B_296 | v1_funct_2(C_297, A_298, B_296) | k1_relset_1(A_298, B_296, C_297)!=A_298 | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_298, B_296))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.52/1.82  tff(c_1713, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1440, c_1710])).
% 4.52/1.82  tff(c_1727, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_1713])).
% 4.52/1.82  tff(c_1728, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1441, c_65, c_1727])).
% 4.52/1.82  tff(c_1737, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1534, c_1728])).
% 4.52/1.82  tff(c_1741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1737])).
% 4.52/1.82  tff(c_1742, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 4.52/1.82  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.82  tff(c_1758, plain, (![B_301]: (k2_zfmisc_1('#skF_1', B_301)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_8])).
% 4.52/1.82  tff(c_1762, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1758, c_16])).
% 4.52/1.82  tff(c_1756, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_8])).
% 4.52/1.82  tff(c_1743, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 4.52/1.82  tff(c_1748, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1743])).
% 4.52/1.82  tff(c_1754, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_56])).
% 4.52/1.82  tff(c_1757, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_1754])).
% 4.52/1.82  tff(c_2063, plain, (![B_358, A_359]: (v1_relat_1(B_358) | ~m1_subset_1(B_358, k1_zfmisc_1(A_359)) | ~v1_relat_1(A_359))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.82  tff(c_2066, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1757, c_2063])).
% 4.52/1.82  tff(c_2069, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_2066])).
% 4.52/1.82  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.82  tff(c_1767, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_6])).
% 4.52/1.82  tff(c_2119, plain, (![C_372, A_373, B_374]: (v4_relat_1(C_372, A_373) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.52/1.82  tff(c_2126, plain, (![C_375, A_376]: (v4_relat_1(C_375, A_376) | ~m1_subset_1(C_375, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1767, c_2119])).
% 4.52/1.82  tff(c_2129, plain, (![A_376]: (v4_relat_1('#skF_4', A_376))), inference(resolution, [status(thm)], [c_1757, c_2126])).
% 4.52/1.82  tff(c_2162, plain, (![B_382, A_383]: (k7_relat_1(B_382, A_383)=B_382 | ~v4_relat_1(B_382, A_383) | ~v1_relat_1(B_382))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.52/1.82  tff(c_2165, plain, (![A_376]: (k7_relat_1('#skF_4', A_376)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2129, c_2162])).
% 4.52/1.82  tff(c_2168, plain, (![A_376]: (k7_relat_1('#skF_4', A_376)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_2165])).
% 4.52/1.82  tff(c_2316, plain, (![A_414, B_415, C_416, D_417]: (k2_partfun1(A_414, B_415, C_416, D_417)=k7_relat_1(C_416, D_417) | ~m1_subset_1(C_416, k1_zfmisc_1(k2_zfmisc_1(A_414, B_415))) | ~v1_funct_1(C_416))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.52/1.82  tff(c_2328, plain, (![A_423, C_424, D_425]: (k2_partfun1(A_423, '#skF_1', C_424, D_425)=k7_relat_1(C_424, D_425) | ~m1_subset_1(C_424, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_424))), inference(superposition, [status(thm), theory('equality')], [c_1767, c_2316])).
% 4.52/1.82  tff(c_2330, plain, (![A_423, D_425]: (k2_partfun1(A_423, '#skF_1', '#skF_4', D_425)=k7_relat_1('#skF_4', D_425) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1757, c_2328])).
% 4.52/1.82  tff(c_2333, plain, (![A_423, D_425]: (k2_partfun1(A_423, '#skF_1', '#skF_4', D_425)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2168, c_2330])).
% 4.52/1.82  tff(c_2046, plain, (![A_351, B_352, C_353, D_354]: (v1_funct_1(k2_partfun1(A_351, B_352, C_353, D_354)) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~v1_funct_1(C_353))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.52/1.82  tff(c_2051, plain, (![A_355, C_356, D_357]: (v1_funct_1(k2_partfun1(A_355, '#skF_1', C_356, D_357)) | ~m1_subset_1(C_356, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_356))), inference(superposition, [status(thm), theory('equality')], [c_1767, c_2046])).
% 4.52/1.82  tff(c_2053, plain, (![A_355, D_357]: (v1_funct_1(k2_partfun1(A_355, '#skF_1', '#skF_4', D_357)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1757, c_2051])).
% 4.52/1.82  tff(c_2056, plain, (![A_355, D_357]: (v1_funct_1(k2_partfun1(A_355, '#skF_1', '#skF_4', D_357)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2053])).
% 4.52/1.82  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.52/1.82  tff(c_1787, plain, (![A_303]: (A_303='#skF_1' | ~r1_tarski(A_303, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_2])).
% 4.52/1.82  tff(c_1791, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_54, c_1787])).
% 4.52/1.82  tff(c_1802, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1791, c_1748, c_1791, c_1791, c_1748, c_1748, c_1791, c_1767, c_1748, c_1748, c_50])).
% 4.52/1.82  tff(c_1803, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1802])).
% 4.52/1.82  tff(c_2059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1803])).
% 4.52/1.82  tff(c_2060, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1802])).
% 4.52/1.82  tff(c_2062, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2060])).
% 4.52/1.82  tff(c_2335, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2333, c_2062])).
% 4.52/1.82  tff(c_2339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1757, c_2335])).
% 4.52/1.82  tff(c_2341, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_2060])).
% 4.52/1.82  tff(c_2382, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2341, c_10])).
% 4.52/1.82  tff(c_2385, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_2382])).
% 4.52/1.82  tff(c_2476, plain, (![C_449, A_450, B_451]: (v4_relat_1(C_449, A_450) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.52/1.82  tff(c_2483, plain, (![C_452, A_453]: (v4_relat_1(C_452, A_453) | ~m1_subset_1(C_452, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1767, c_2476])).
% 4.52/1.82  tff(c_2497, plain, (![A_455]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_455))), inference(resolution, [status(thm)], [c_2341, c_2483])).
% 4.52/1.82  tff(c_18, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.52/1.82  tff(c_2500, plain, (![A_455]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_455)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_2497, c_18])).
% 4.52/1.82  tff(c_2568, plain, (![A_464]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_464)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2385, c_2500])).
% 4.52/1.82  tff(c_2361, plain, (![B_430, A_431]: (r1_tarski(k1_relat_1(k7_relat_1(B_430, A_431)), A_431) | ~v1_relat_1(B_430))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.52/1.82  tff(c_1786, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_2])).
% 4.52/1.82  tff(c_2366, plain, (![B_430]: (k1_relat_1(k7_relat_1(B_430, '#skF_1'))='#skF_1' | ~v1_relat_1(B_430))), inference(resolution, [status(thm)], [c_2361, c_1786])).
% 4.52/1.82  tff(c_2574, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2568, c_2366])).
% 4.52/1.82  tff(c_2582, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2385, c_2574])).
% 4.52/1.82  tff(c_2561, plain, (![A_461, B_462, C_463]: (k1_relset_1(A_461, B_462, C_463)=k1_relat_1(C_463) | ~m1_subset_1(C_463, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.52/1.82  tff(c_2596, plain, (![B_465, C_466]: (k1_relset_1('#skF_1', B_465, C_466)=k1_relat_1(C_466) | ~m1_subset_1(C_466, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1756, c_2561])).
% 4.52/1.82  tff(c_2598, plain, (![B_465]: (k1_relset_1('#skF_1', B_465, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_2341, c_2596])).
% 4.52/1.82  tff(c_2602, plain, (![B_465]: (k1_relset_1('#skF_1', B_465, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_2598])).
% 4.52/1.82  tff(c_36, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.52/1.82  tff(c_62, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 4.52/1.82  tff(c_2697, plain, (![C_491, B_492]: (v1_funct_2(C_491, '#skF_1', B_492) | k1_relset_1('#skF_1', B_492, C_491)!='#skF_1' | ~m1_subset_1(C_491, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_1742, c_1742, c_62])).
% 4.52/1.82  tff(c_2699, plain, (![B_492]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_492) | k1_relset_1('#skF_1', B_492, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_2341, c_2697])).
% 4.52/1.82  tff(c_2704, plain, (![B_492]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_492))), inference(demodulation, [status(thm), theory('equality')], [c_2602, c_2699])).
% 4.52/1.82  tff(c_2340, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2060])).
% 4.52/1.82  tff(c_2724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2340])).
% 4.52/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.82  
% 4.52/1.82  Inference rules
% 4.52/1.82  ----------------------
% 4.52/1.82  #Ref     : 0
% 4.52/1.82  #Sup     : 580
% 4.52/1.82  #Fact    : 0
% 4.52/1.82  #Define  : 0
% 4.52/1.82  #Split   : 22
% 4.52/1.82  #Chain   : 0
% 4.52/1.82  #Close   : 0
% 4.52/1.82  
% 4.52/1.82  Ordering : KBO
% 4.52/1.82  
% 4.52/1.82  Simplification rules
% 4.52/1.82  ----------------------
% 4.52/1.82  #Subsume      : 36
% 4.52/1.82  #Demod        : 415
% 4.52/1.82  #Tautology    : 247
% 4.52/1.82  #SimpNegUnit  : 17
% 4.52/1.82  #BackRed      : 33
% 4.52/1.82  
% 4.52/1.82  #Partial instantiations: 0
% 4.52/1.82  #Strategies tried      : 1
% 4.52/1.82  
% 4.52/1.82  Timing (in seconds)
% 4.52/1.82  ----------------------
% 4.52/1.82  Preprocessing        : 0.35
% 4.52/1.82  Parsing              : 0.18
% 4.52/1.82  CNF conversion       : 0.02
% 4.52/1.82  Main loop            : 0.69
% 4.52/1.82  Inferencing          : 0.26
% 4.52/1.82  Reduction            : 0.22
% 4.52/1.82  Demodulation         : 0.15
% 4.52/1.82  BG Simplification    : 0.03
% 4.52/1.82  Subsumption          : 0.11
% 4.52/1.82  Abstraction          : 0.03
% 4.52/1.82  MUC search           : 0.00
% 4.52/1.82  Cooper               : 0.00
% 4.52/1.82  Total                : 1.10
% 4.52/1.82  Index Insertion      : 0.00
% 4.52/1.82  Index Deletion       : 0.00
% 4.52/1.82  Index Matching       : 0.00
% 4.52/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
