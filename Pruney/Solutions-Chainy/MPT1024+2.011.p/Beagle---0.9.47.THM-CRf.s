%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:23 EST 2020

% Result     : Theorem 25.08s
% Output     : CNFRefutation 25.08s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 693 expanded)
%              Number of leaves         :   61 ( 251 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 (1506 expanded)
%              Number of equality atoms :   52 ( 304 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_subset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_301,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_202,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_223,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_190,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_163,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_270,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_151,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_92,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_142,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_317,plain,(
    ! [C_223,A_224,B_225] :
      ( v1_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_340,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_142,c_317])).

tff(c_146,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_90872,plain,(
    ! [A_2540,B_2541,C_2542,D_2543] :
      ( k7_relset_1(A_2540,B_2541,C_2542,D_2543) = k9_relat_1(C_2542,D_2543)
      | ~ m1_subset_1(C_2542,k1_zfmisc_1(k2_zfmisc_1(A_2540,B_2541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_90902,plain,(
    ! [D_2543] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_2543) = k9_relat_1('#skF_10',D_2543) ),
    inference(resolution,[status(thm)],[c_142,c_90872])).

tff(c_140,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_90935,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90902,c_140])).

tff(c_91367,plain,(
    ! [A_2562,B_2563,C_2564] :
      ( r2_hidden(k4_tarski('#skF_4'(A_2562,B_2563,C_2564),A_2562),C_2564)
      | ~ r2_hidden(A_2562,k9_relat_1(C_2564,B_2563))
      | ~ v1_relat_1(C_2564) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_82,plain,(
    ! [C_66,A_64,B_65] :
      ( k1_funct_1(C_66,A_64) = B_65
      | ~ r2_hidden(k4_tarski(A_64,B_65),C_66)
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_127644,plain,(
    ! [C_3153,A_3154,B_3155] :
      ( k1_funct_1(C_3153,'#skF_4'(A_3154,B_3155,C_3153)) = A_3154
      | ~ v1_funct_1(C_3153)
      | ~ r2_hidden(A_3154,k9_relat_1(C_3153,B_3155))
      | ~ v1_relat_1(C_3153) ) ),
    inference(resolution,[status(thm)],[c_91367,c_82])).

tff(c_127696,plain,
    ( k1_funct_1('#skF_10','#skF_4'('#skF_11','#skF_9','#skF_10')) = '#skF_11'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_90935,c_127644])).

tff(c_127765,plain,(
    k1_funct_1('#skF_10','#skF_4'('#skF_11','#skF_9','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_146,c_127696])).

tff(c_58,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden('#skF_4'(A_43,B_44,C_45),B_44)
      | ~ r2_hidden(A_43,k9_relat_1(C_45,B_44))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden(k4_tarski('#skF_4'(A_43,B_44,C_45),A_43),C_45)
      | ~ r2_hidden(A_43,k9_relat_1(C_45,B_44))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_87107,plain,(
    ! [C_2270,B_2271,A_2272] :
      ( ~ v1_xboole_0(C_2270)
      | ~ m1_subset_1(B_2271,k1_zfmisc_1(C_2270))
      | ~ r2_hidden(A_2272,B_2271) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_87133,plain,(
    ! [A_2272] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(A_2272,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_142,c_87107])).

tff(c_87217,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_87133])).

tff(c_87544,plain,(
    ! [A_2319,C_2320,B_2321] :
      ( m1_subset_1(A_2319,C_2320)
      | ~ m1_subset_1(B_2321,k1_zfmisc_1(C_2320))
      | ~ r2_hidden(A_2319,B_2321) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_87565,plain,(
    ! [A_2319] :
      ( m1_subset_1(A_2319,k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(A_2319,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_142,c_87544])).

tff(c_48,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_87532,plain,(
    ! [A_2315,C_2316,B_2317,D_2318] :
      ( r2_hidden(A_2315,C_2316)
      | ~ r2_hidden(k4_tarski(A_2315,B_2317),k2_zfmisc_1(C_2316,D_2318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_120312,plain,(
    ! [A_3016,C_3017,D_3018,B_3019] :
      ( r2_hidden(A_3016,C_3017)
      | v1_xboole_0(k2_zfmisc_1(C_3017,D_3018))
      | ~ m1_subset_1(k4_tarski(A_3016,B_3019),k2_zfmisc_1(C_3017,D_3018)) ) ),
    inference(resolution,[status(thm)],[c_48,c_87532])).

tff(c_120319,plain,(
    ! [A_3016,B_3019] :
      ( r2_hidden(A_3016,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_3016,B_3019),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_87565,c_120312])).

tff(c_120333,plain,(
    ! [A_3020,B_3021] :
      ( r2_hidden(A_3020,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_3020,B_3021),'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_87217,c_120319])).

tff(c_120345,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_4'(A_43,B_44,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_43,k9_relat_1('#skF_10',B_44))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_60,c_120333])).

tff(c_130383,plain,(
    ! [A_3185,B_3186] :
      ( r2_hidden('#skF_4'(A_3185,B_3186,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_3185,k9_relat_1('#skF_10',B_3186)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_120345])).

tff(c_138,plain,(
    ! [F_192] :
      ( k1_funct_1('#skF_10',F_192) != '#skF_11'
      | ~ r2_hidden(F_192,'#skF_9')
      | ~ r2_hidden(F_192,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_130923,plain,(
    ! [A_3192,B_3193] :
      ( k1_funct_1('#skF_10','#skF_4'(A_3192,B_3193,'#skF_10')) != '#skF_11'
      | ~ r2_hidden('#skF_4'(A_3192,B_3193,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_3192,k9_relat_1('#skF_10',B_3193)) ) ),
    inference(resolution,[status(thm)],[c_130383,c_138])).

tff(c_130927,plain,(
    ! [A_43] :
      ( k1_funct_1('#skF_10','#skF_4'(A_43,'#skF_9','#skF_10')) != '#skF_11'
      | ~ r2_hidden(A_43,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_58,c_130923])).

tff(c_132410,plain,(
    ! [A_3205] :
      ( k1_funct_1('#skF_10','#skF_4'(A_3205,'#skF_9','#skF_10')) != '#skF_11'
      | ~ r2_hidden(A_3205,k9_relat_1('#skF_10','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_130927])).

tff(c_132429,plain,(
    k1_funct_1('#skF_10','#skF_4'('#skF_11','#skF_9','#skF_10')) != '#skF_11' ),
    inference(resolution,[status(thm)],[c_90935,c_132410])).

tff(c_132459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127765,c_132429])).

tff(c_132460,plain,(
    ! [A_2272] : ~ r2_hidden(A_2272,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_87133])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132462,plain,(
    ! [A_3206] : ~ r2_hidden(A_3206,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_87133])).

tff(c_132482,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_132462])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132486,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_132482,c_6])).

tff(c_72,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_132507,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132486,c_132486,c_72])).

tff(c_204,plain,(
    ! [A_200,B_201] : v1_xboole_0('#skF_6'(A_200,B_201)) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_208,plain,(
    ! [A_200,B_201] : '#skF_6'(A_200,B_201) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_6])).

tff(c_122,plain,(
    ! [A_183,B_184] : v4_relat_1('#skF_6'(A_183,B_184),A_183) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_277,plain,(
    ! [A_183] : v4_relat_1(k1_xboole_0,A_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_122])).

tff(c_132494,plain,(
    ! [A_183] : v4_relat_1('#skF_10',A_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132486,c_277])).

tff(c_132754,plain,(
    ! [B_3232,A_3233] :
      ( k7_relat_1(B_3232,A_3233) = B_3232
      | ~ v4_relat_1(B_3232,A_3233)
      | ~ v1_relat_1(B_3232) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_132757,plain,(
    ! [A_183] :
      ( k7_relat_1('#skF_10',A_183) = '#skF_10'
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_132494,c_132754])).

tff(c_132784,plain,(
    ! [A_3234] : k7_relat_1('#skF_10',A_3234) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_132757])).

tff(c_64,plain,(
    ! [B_50,A_49] :
      ( k2_relat_1(k7_relat_1(B_50,A_49)) = k9_relat_1(B_50,A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_132789,plain,(
    ! [A_3234] :
      ( k9_relat_1('#skF_10',A_3234) = k2_relat_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132784,c_64])).

tff(c_132794,plain,(
    ! [A_3234] : k9_relat_1('#skF_10',A_3234) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_132507,c_132789])).

tff(c_44,plain,(
    ! [A_28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_132497,plain,(
    ! [A_28] : m1_subset_1('#skF_10',k1_zfmisc_1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132486,c_44])).

tff(c_136984,plain,(
    ! [A_3524,B_3525,C_3526,D_3527] :
      ( k7_relset_1(A_3524,B_3525,C_3526,D_3527) = k9_relat_1(C_3526,D_3527)
      | ~ m1_subset_1(C_3526,k1_zfmisc_1(k2_zfmisc_1(A_3524,B_3525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_136993,plain,(
    ! [A_3524,B_3525,D_3527] : k7_relset_1(A_3524,B_3525,'#skF_10',D_3527) = k9_relat_1('#skF_10',D_3527) ),
    inference(resolution,[status(thm)],[c_132497,c_136984])).

tff(c_137007,plain,(
    ! [A_3524,B_3525,D_3527] : k7_relset_1(A_3524,B_3525,'#skF_10',D_3527) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132794,c_136993])).

tff(c_132461,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_87133])).

tff(c_132739,plain,(
    ! [A_3231] :
      ( A_3231 = '#skF_10'
      | ~ v1_xboole_0(A_3231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132486,c_6])).

tff(c_132746,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_132461,c_132739])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k1_xboole_0 = B_18
      | k1_xboole_0 = A_17
      | k2_zfmisc_1(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_135166,plain,(
    ! [B_3401,A_3402] :
      ( B_3401 = '#skF_10'
      | A_3402 = '#skF_10'
      | k2_zfmisc_1(A_3402,B_3401) != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132486,c_132486,c_132486,c_22])).

tff(c_135176,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_132746,c_135166])).

tff(c_135181,plain,(
    '#skF_7' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_135176])).

tff(c_135214,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_10','#skF_8','#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135181,c_140])).

tff(c_137012,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137007,c_135214])).

tff(c_137016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132460,c_137012])).

tff(c_137017,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_135176])).

tff(c_137058,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137017,c_132482])).

tff(c_137033,plain,(
    ! [A_3234] : k9_relat_1('#skF_8',A_3234) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137017,c_137017,c_132794])).

tff(c_137042,plain,(
    ! [A_28] : m1_subset_1('#skF_8',k1_zfmisc_1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137017,c_132497])).

tff(c_138462,plain,(
    ! [A_3618,B_3619,C_3620,D_3621] :
      ( k7_relset_1(A_3618,B_3619,C_3620,D_3621) = k9_relat_1(C_3620,D_3621)
      | ~ m1_subset_1(C_3620,k1_zfmisc_1(k2_zfmisc_1(A_3618,B_3619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_138469,plain,(
    ! [A_3618,B_3619,D_3621] : k7_relset_1(A_3618,B_3619,'#skF_8',D_3621) = k9_relat_1('#skF_8',D_3621) ),
    inference(resolution,[status(thm)],[c_137042,c_138462])).

tff(c_138485,plain,(
    ! [A_3618,B_3619,D_3621] : k7_relset_1(A_3618,B_3619,'#skF_8',D_3621) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137033,c_138469])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ v1_xboole_0(B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_275,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_140,c_14])).

tff(c_137063,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_7','#skF_8','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137017,c_275])).

tff(c_138491,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138485,c_137063])).

tff(c_138495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137058,c_138491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.08/15.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.08/15.88  
% 25.08/15.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.08/15.88  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_subset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 25.08/15.88  
% 25.08/15.88  %Foreground sorts:
% 25.08/15.88  
% 25.08/15.88  
% 25.08/15.88  %Background operators:
% 25.08/15.88  
% 25.08/15.88  
% 25.08/15.88  %Foreground operators:
% 25.08/15.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 25.08/15.88  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 25.08/15.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 25.08/15.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.08/15.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.08/15.88  tff('#skF_11', type, '#skF_11': $i).
% 25.08/15.88  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 25.08/15.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 25.08/15.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 25.08/15.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.08/15.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 25.08/15.88  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 25.08/15.88  tff('#skF_7', type, '#skF_7': $i).
% 25.08/15.88  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 25.08/15.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.08/15.88  tff('#skF_10', type, '#skF_10': $i).
% 25.08/15.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.08/15.88  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 25.08/15.88  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 25.08/15.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 25.08/15.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 25.08/15.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 25.08/15.88  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 25.08/15.88  tff('#skF_9', type, '#skF_9': $i).
% 25.08/15.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 25.08/15.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 25.08/15.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.08/15.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 25.08/15.88  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 25.08/15.88  tff('#skF_8', type, '#skF_8': $i).
% 25.08/15.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.08/15.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.08/15.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.08/15.88  tff('#skF_3', type, '#skF_3': $i > $i).
% 25.08/15.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 25.08/15.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.08/15.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 25.08/15.88  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 25.08/15.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 25.08/15.88  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 25.08/15.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.08/15.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.08/15.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.08/15.88  
% 25.08/15.90  tff(f_301, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 25.08/15.90  tff(f_202, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 25.08/15.90  tff(f_223, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 25.08/15.90  tff(f_135, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 25.08/15.90  tff(f_190, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 25.08/15.90  tff(f_115, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 25.08/15.90  tff(f_108, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 25.08/15.90  tff(f_102, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 25.08/15.90  tff(f_64, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 25.08/15.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 25.08/15.90  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 25.08/15.90  tff(f_163, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 25.08/15.90  tff(f_270, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 25.08/15.90  tff(f_151, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 25.08/15.90  tff(f_139, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 25.08/15.90  tff(f_92, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 25.08/15.90  tff(f_70, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 25.08/15.90  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 25.08/15.90  tff(c_142, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_301])).
% 25.08/15.90  tff(c_317, plain, (![C_223, A_224, B_225]: (v1_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_202])).
% 25.08/15.90  tff(c_340, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_142, c_317])).
% 25.08/15.90  tff(c_146, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_301])).
% 25.08/15.90  tff(c_90872, plain, (![A_2540, B_2541, C_2542, D_2543]: (k7_relset_1(A_2540, B_2541, C_2542, D_2543)=k9_relat_1(C_2542, D_2543) | ~m1_subset_1(C_2542, k1_zfmisc_1(k2_zfmisc_1(A_2540, B_2541))))), inference(cnfTransformation, [status(thm)], [f_223])).
% 25.08/15.90  tff(c_90902, plain, (![D_2543]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_2543)=k9_relat_1('#skF_10', D_2543))), inference(resolution, [status(thm)], [c_142, c_90872])).
% 25.08/15.90  tff(c_140, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_301])).
% 25.08/15.90  tff(c_90935, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_90902, c_140])).
% 25.08/15.90  tff(c_91367, plain, (![A_2562, B_2563, C_2564]: (r2_hidden(k4_tarski('#skF_4'(A_2562, B_2563, C_2564), A_2562), C_2564) | ~r2_hidden(A_2562, k9_relat_1(C_2564, B_2563)) | ~v1_relat_1(C_2564))), inference(cnfTransformation, [status(thm)], [f_135])).
% 25.08/15.90  tff(c_82, plain, (![C_66, A_64, B_65]: (k1_funct_1(C_66, A_64)=B_65 | ~r2_hidden(k4_tarski(A_64, B_65), C_66) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_190])).
% 25.08/15.90  tff(c_127644, plain, (![C_3153, A_3154, B_3155]: (k1_funct_1(C_3153, '#skF_4'(A_3154, B_3155, C_3153))=A_3154 | ~v1_funct_1(C_3153) | ~r2_hidden(A_3154, k9_relat_1(C_3153, B_3155)) | ~v1_relat_1(C_3153))), inference(resolution, [status(thm)], [c_91367, c_82])).
% 25.08/15.90  tff(c_127696, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_11', '#skF_9', '#skF_10'))='#skF_11' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_90935, c_127644])).
% 25.08/15.90  tff(c_127765, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_11', '#skF_9', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_340, c_146, c_127696])).
% 25.08/15.90  tff(c_58, plain, (![A_43, B_44, C_45]: (r2_hidden('#skF_4'(A_43, B_44, C_45), B_44) | ~r2_hidden(A_43, k9_relat_1(C_45, B_44)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_135])).
% 25.08/15.90  tff(c_60, plain, (![A_43, B_44, C_45]: (r2_hidden(k4_tarski('#skF_4'(A_43, B_44, C_45), A_43), C_45) | ~r2_hidden(A_43, k9_relat_1(C_45, B_44)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_135])).
% 25.08/15.90  tff(c_87107, plain, (![C_2270, B_2271, A_2272]: (~v1_xboole_0(C_2270) | ~m1_subset_1(B_2271, k1_zfmisc_1(C_2270)) | ~r2_hidden(A_2272, B_2271))), inference(cnfTransformation, [status(thm)], [f_115])).
% 25.08/15.90  tff(c_87133, plain, (![A_2272]: (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(A_2272, '#skF_10'))), inference(resolution, [status(thm)], [c_142, c_87107])).
% 25.08/15.90  tff(c_87217, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_87133])).
% 25.08/15.90  tff(c_87544, plain, (![A_2319, C_2320, B_2321]: (m1_subset_1(A_2319, C_2320) | ~m1_subset_1(B_2321, k1_zfmisc_1(C_2320)) | ~r2_hidden(A_2319, B_2321))), inference(cnfTransformation, [status(thm)], [f_108])).
% 25.08/15.90  tff(c_87565, plain, (![A_2319]: (m1_subset_1(A_2319, k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(A_2319, '#skF_10'))), inference(resolution, [status(thm)], [c_142, c_87544])).
% 25.08/15.90  tff(c_48, plain, (![A_31, B_32]: (r2_hidden(A_31, B_32) | v1_xboole_0(B_32) | ~m1_subset_1(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_102])).
% 25.08/15.90  tff(c_87532, plain, (![A_2315, C_2316, B_2317, D_2318]: (r2_hidden(A_2315, C_2316) | ~r2_hidden(k4_tarski(A_2315, B_2317), k2_zfmisc_1(C_2316, D_2318)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 25.08/15.90  tff(c_120312, plain, (![A_3016, C_3017, D_3018, B_3019]: (r2_hidden(A_3016, C_3017) | v1_xboole_0(k2_zfmisc_1(C_3017, D_3018)) | ~m1_subset_1(k4_tarski(A_3016, B_3019), k2_zfmisc_1(C_3017, D_3018)))), inference(resolution, [status(thm)], [c_48, c_87532])).
% 25.08/15.90  tff(c_120319, plain, (![A_3016, B_3019]: (r2_hidden(A_3016, '#skF_7') | v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(k4_tarski(A_3016, B_3019), '#skF_10'))), inference(resolution, [status(thm)], [c_87565, c_120312])).
% 25.08/15.90  tff(c_120333, plain, (![A_3020, B_3021]: (r2_hidden(A_3020, '#skF_7') | ~r2_hidden(k4_tarski(A_3020, B_3021), '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_87217, c_120319])).
% 25.08/15.90  tff(c_120345, plain, (![A_43, B_44]: (r2_hidden('#skF_4'(A_43, B_44, '#skF_10'), '#skF_7') | ~r2_hidden(A_43, k9_relat_1('#skF_10', B_44)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_60, c_120333])).
% 25.08/15.90  tff(c_130383, plain, (![A_3185, B_3186]: (r2_hidden('#skF_4'(A_3185, B_3186, '#skF_10'), '#skF_7') | ~r2_hidden(A_3185, k9_relat_1('#skF_10', B_3186)))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_120345])).
% 25.08/15.90  tff(c_138, plain, (![F_192]: (k1_funct_1('#skF_10', F_192)!='#skF_11' | ~r2_hidden(F_192, '#skF_9') | ~r2_hidden(F_192, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_301])).
% 25.08/15.90  tff(c_130923, plain, (![A_3192, B_3193]: (k1_funct_1('#skF_10', '#skF_4'(A_3192, B_3193, '#skF_10'))!='#skF_11' | ~r2_hidden('#skF_4'(A_3192, B_3193, '#skF_10'), '#skF_9') | ~r2_hidden(A_3192, k9_relat_1('#skF_10', B_3193)))), inference(resolution, [status(thm)], [c_130383, c_138])).
% 25.08/15.90  tff(c_130927, plain, (![A_43]: (k1_funct_1('#skF_10', '#skF_4'(A_43, '#skF_9', '#skF_10'))!='#skF_11' | ~r2_hidden(A_43, k9_relat_1('#skF_10', '#skF_9')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_58, c_130923])).
% 25.08/15.90  tff(c_132410, plain, (![A_3205]: (k1_funct_1('#skF_10', '#skF_4'(A_3205, '#skF_9', '#skF_10'))!='#skF_11' | ~r2_hidden(A_3205, k9_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_130927])).
% 25.08/15.90  tff(c_132429, plain, (k1_funct_1('#skF_10', '#skF_4'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11'), inference(resolution, [status(thm)], [c_90935, c_132410])).
% 25.08/15.90  tff(c_132459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127765, c_132429])).
% 25.08/15.90  tff(c_132460, plain, (![A_2272]: (~r2_hidden(A_2272, '#skF_10'))), inference(splitRight, [status(thm)], [c_87133])).
% 25.08/15.90  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 25.08/15.90  tff(c_132462, plain, (![A_3206]: (~r2_hidden(A_3206, '#skF_10'))), inference(splitRight, [status(thm)], [c_87133])).
% 25.08/15.90  tff(c_132482, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_132462])).
% 25.08/15.90  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.08/15.90  tff(c_132486, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_132482, c_6])).
% 25.08/15.90  tff(c_72, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_163])).
% 25.08/15.90  tff(c_132507, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_132486, c_132486, c_72])).
% 25.08/15.90  tff(c_204, plain, (![A_200, B_201]: (v1_xboole_0('#skF_6'(A_200, B_201)))), inference(cnfTransformation, [status(thm)], [f_270])).
% 25.08/15.90  tff(c_208, plain, (![A_200, B_201]: ('#skF_6'(A_200, B_201)=k1_xboole_0)), inference(resolution, [status(thm)], [c_204, c_6])).
% 25.08/15.90  tff(c_122, plain, (![A_183, B_184]: (v4_relat_1('#skF_6'(A_183, B_184), A_183))), inference(cnfTransformation, [status(thm)], [f_270])).
% 25.08/15.90  tff(c_277, plain, (![A_183]: (v4_relat_1(k1_xboole_0, A_183))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_122])).
% 25.08/15.90  tff(c_132494, plain, (![A_183]: (v4_relat_1('#skF_10', A_183))), inference(demodulation, [status(thm), theory('equality')], [c_132486, c_277])).
% 25.08/15.90  tff(c_132754, plain, (![B_3232, A_3233]: (k7_relat_1(B_3232, A_3233)=B_3232 | ~v4_relat_1(B_3232, A_3233) | ~v1_relat_1(B_3232))), inference(cnfTransformation, [status(thm)], [f_151])).
% 25.08/15.90  tff(c_132757, plain, (![A_183]: (k7_relat_1('#skF_10', A_183)='#skF_10' | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_132494, c_132754])).
% 25.08/15.90  tff(c_132784, plain, (![A_3234]: (k7_relat_1('#skF_10', A_3234)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_132757])).
% 25.08/15.90  tff(c_64, plain, (![B_50, A_49]: (k2_relat_1(k7_relat_1(B_50, A_49))=k9_relat_1(B_50, A_49) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_139])).
% 25.08/15.90  tff(c_132789, plain, (![A_3234]: (k9_relat_1('#skF_10', A_3234)=k2_relat_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_132784, c_64])).
% 25.08/15.90  tff(c_132794, plain, (![A_3234]: (k9_relat_1('#skF_10', A_3234)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_132507, c_132789])).
% 25.08/15.90  tff(c_44, plain, (![A_28]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 25.08/15.90  tff(c_132497, plain, (![A_28]: (m1_subset_1('#skF_10', k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_132486, c_44])).
% 25.08/15.90  tff(c_136984, plain, (![A_3524, B_3525, C_3526, D_3527]: (k7_relset_1(A_3524, B_3525, C_3526, D_3527)=k9_relat_1(C_3526, D_3527) | ~m1_subset_1(C_3526, k1_zfmisc_1(k2_zfmisc_1(A_3524, B_3525))))), inference(cnfTransformation, [status(thm)], [f_223])).
% 25.08/15.90  tff(c_136993, plain, (![A_3524, B_3525, D_3527]: (k7_relset_1(A_3524, B_3525, '#skF_10', D_3527)=k9_relat_1('#skF_10', D_3527))), inference(resolution, [status(thm)], [c_132497, c_136984])).
% 25.08/15.90  tff(c_137007, plain, (![A_3524, B_3525, D_3527]: (k7_relset_1(A_3524, B_3525, '#skF_10', D_3527)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_132794, c_136993])).
% 25.08/15.90  tff(c_132461, plain, (v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_87133])).
% 25.08/15.90  tff(c_132739, plain, (![A_3231]: (A_3231='#skF_10' | ~v1_xboole_0(A_3231))), inference(demodulation, [status(thm), theory('equality')], [c_132486, c_6])).
% 25.08/15.90  tff(c_132746, plain, (k2_zfmisc_1('#skF_7', '#skF_8')='#skF_10'), inference(resolution, [status(thm)], [c_132461, c_132739])).
% 25.08/15.90  tff(c_22, plain, (![B_18, A_17]: (k1_xboole_0=B_18 | k1_xboole_0=A_17 | k2_zfmisc_1(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 25.08/15.90  tff(c_135166, plain, (![B_3401, A_3402]: (B_3401='#skF_10' | A_3402='#skF_10' | k2_zfmisc_1(A_3402, B_3401)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_132486, c_132486, c_132486, c_22])).
% 25.08/15.90  tff(c_135176, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_132746, c_135166])).
% 25.08/15.90  tff(c_135181, plain, ('#skF_7'='#skF_10'), inference(splitLeft, [status(thm)], [c_135176])).
% 25.08/15.90  tff(c_135214, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_10', '#skF_8', '#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_135181, c_140])).
% 25.08/15.90  tff(c_137012, plain, (r2_hidden('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_137007, c_135214])).
% 25.08/15.90  tff(c_137016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132460, c_137012])).
% 25.08/15.90  tff(c_137017, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_135176])).
% 25.08/15.90  tff(c_137058, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_137017, c_132482])).
% 25.08/15.90  tff(c_137033, plain, (![A_3234]: (k9_relat_1('#skF_8', A_3234)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_137017, c_137017, c_132794])).
% 25.08/15.90  tff(c_137042, plain, (![A_28]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_137017, c_132497])).
% 25.08/15.90  tff(c_138462, plain, (![A_3618, B_3619, C_3620, D_3621]: (k7_relset_1(A_3618, B_3619, C_3620, D_3621)=k9_relat_1(C_3620, D_3621) | ~m1_subset_1(C_3620, k1_zfmisc_1(k2_zfmisc_1(A_3618, B_3619))))), inference(cnfTransformation, [status(thm)], [f_223])).
% 25.08/15.90  tff(c_138469, plain, (![A_3618, B_3619, D_3621]: (k7_relset_1(A_3618, B_3619, '#skF_8', D_3621)=k9_relat_1('#skF_8', D_3621))), inference(resolution, [status(thm)], [c_137042, c_138462])).
% 25.08/15.90  tff(c_138485, plain, (![A_3618, B_3619, D_3621]: (k7_relset_1(A_3618, B_3619, '#skF_8', D_3621)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_137033, c_138469])).
% 25.08/15.90  tff(c_14, plain, (![B_12, A_11]: (~v1_xboole_0(B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.08/15.90  tff(c_275, plain, (~v1_xboole_0(k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_140, c_14])).
% 25.08/15.90  tff(c_137063, plain, (~v1_xboole_0(k7_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_137017, c_275])).
% 25.08/15.90  tff(c_138491, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_138485, c_137063])).
% 25.08/15.90  tff(c_138495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137058, c_138491])).
% 25.08/15.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.08/15.90  
% 25.08/15.90  Inference rules
% 25.08/15.90  ----------------------
% 25.08/15.90  #Ref     : 0
% 25.08/15.90  #Sup     : 31204
% 25.08/15.90  #Fact    : 0
% 25.08/15.90  #Define  : 0
% 25.08/15.90  #Split   : 84
% 25.08/15.90  #Chain   : 0
% 25.08/15.90  #Close   : 0
% 25.08/15.90  
% 25.08/15.90  Ordering : KBO
% 25.08/15.90  
% 25.08/15.90  Simplification rules
% 25.08/15.90  ----------------------
% 25.08/15.90  #Subsume      : 7290
% 25.08/15.90  #Demod        : 40333
% 25.08/15.90  #Tautology    : 16732
% 25.08/15.90  #SimpNegUnit  : 535
% 25.08/15.90  #BackRed      : 606
% 25.08/15.90  
% 25.08/15.90  #Partial instantiations: 0
% 25.08/15.90  #Strategies tried      : 1
% 25.08/15.90  
% 25.08/15.90  Timing (in seconds)
% 25.08/15.90  ----------------------
% 25.08/15.90  Preprocessing        : 0.44
% 25.08/15.90  Parsing              : 0.23
% 25.08/15.90  CNF conversion       : 0.04
% 25.08/15.90  Main loop            : 14.63
% 25.08/15.90  Inferencing          : 2.90
% 25.08/15.90  Reduction            : 5.72
% 25.08/15.90  Demodulation         : 4.36
% 25.08/15.90  BG Simplification    : 0.26
% 25.08/15.90  Subsumption          : 4.99
% 25.08/15.90  Abstraction          : 0.46
% 25.08/15.90  MUC search           : 0.00
% 25.08/15.90  Cooper               : 0.00
% 25.08/15.90  Total                : 15.11
% 25.08/15.90  Index Insertion      : 0.00
% 25.08/15.90  Index Deletion       : 0.00
% 25.27/15.90  Index Matching       : 0.00
% 25.27/15.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
