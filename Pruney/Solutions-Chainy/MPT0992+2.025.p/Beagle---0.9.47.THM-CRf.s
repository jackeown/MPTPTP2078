%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:35 EST 2020

% Result     : Theorem 31.92s
% Output     : CNFRefutation 32.27s
% Verified   : 
% Statistics : Number of formulae       :  246 (5981 expanded)
%              Number of leaves         :   42 (1703 expanded)
%              Depth                    :   18
%              Number of atoms          :  401 (18291 expanded)
%              Number of equality atoms :   98 (6999 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_148,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
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

tff(f_70,axiom,(
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

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_120,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_128,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_120])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_103979,plain,(
    ! [A_3152,B_3153,C_3154] :
      ( k1_relset_1(A_3152,B_3153,C_3154) = k1_relat_1(C_3154)
      | ~ m1_subset_1(C_3154,k1_zfmisc_1(k2_zfmisc_1(A_3152,B_3153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103993,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_103979])).

tff(c_104203,plain,(
    ! [B_3192,A_3193,C_3194] :
      ( k1_xboole_0 = B_3192
      | k1_relset_1(A_3193,B_3192,C_3194) = A_3193
      | ~ v1_funct_2(C_3194,A_3193,B_3192)
      | ~ m1_subset_1(C_3194,k1_zfmisc_1(k2_zfmisc_1(A_3193,B_3192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_104212,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_104203])).

tff(c_104225,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_103993,c_104212])).

tff(c_104226,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_104225])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( k1_relat_1(k7_relat_1(B_19,A_18)) = A_18
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_104244,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104226,c_32])).

tff(c_104256,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_104244])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_104130,plain,(
    ! [A_3185,B_3186,C_3187,D_3188] :
      ( k2_partfun1(A_3185,B_3186,C_3187,D_3188) = k7_relat_1(C_3187,D_3188)
      | ~ m1_subset_1(C_3187,k1_zfmisc_1(k2_zfmisc_1(A_3185,B_3186)))
      | ~ v1_funct_1(C_3187) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_104136,plain,(
    ! [D_3188] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_3188) = k7_relat_1('#skF_5',D_3188)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_104130])).

tff(c_104147,plain,(
    ! [D_3188] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_3188) = k7_relat_1('#skF_5',D_3188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_104136])).

tff(c_12281,plain,(
    ! [A_1194,B_1195,C_1196,D_1197] :
      ( k2_partfun1(A_1194,B_1195,C_1196,D_1197) = k7_relat_1(C_1196,D_1197)
      | ~ m1_subset_1(C_1196,k1_zfmisc_1(k2_zfmisc_1(A_1194,B_1195)))
      | ~ v1_funct_1(C_1196) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12285,plain,(
    ! [D_1197] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_1197) = k7_relat_1('#skF_5',D_1197)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_12281])).

tff(c_12293,plain,(
    ! [D_1197] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_1197) = k7_relat_1('#skF_5',D_1197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12285])).

tff(c_12621,plain,(
    ! [A_1217,B_1218,C_1219,D_1220] :
      ( m1_subset_1(k2_partfun1(A_1217,B_1218,C_1219,D_1220),k1_zfmisc_1(k2_zfmisc_1(A_1217,B_1218)))
      | ~ m1_subset_1(C_1219,k1_zfmisc_1(k2_zfmisc_1(A_1217,B_1218)))
      | ~ v1_funct_1(C_1219) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12648,plain,(
    ! [D_1197] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_1197),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12293,c_12621])).

tff(c_12669,plain,(
    ! [D_1222] : m1_subset_1(k7_relat_1('#skF_5',D_1222),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_12648])).

tff(c_34,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12710,plain,(
    ! [D_1222] : v1_relat_1(k7_relat_1('#skF_5',D_1222)) ),
    inference(resolution,[status(thm)],[c_12669,c_34])).

tff(c_36,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12708,plain,(
    ! [D_1222] : v5_relat_1(k7_relat_1('#skF_5',D_1222),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12669,c_36])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8181,plain,(
    ! [A_860,B_861,C_862,D_863] :
      ( v1_funct_1(k2_partfun1(A_860,B_861,C_862,D_863))
      | ~ m1_subset_1(C_862,k1_zfmisc_1(k2_zfmisc_1(A_860,B_861)))
      | ~ v1_funct_1(C_862) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8183,plain,(
    ! [D_863] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_863))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_8181])).

tff(c_8190,plain,(
    ! [D_863] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_863)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8183])).

tff(c_12295,plain,(
    ! [D_863] : v1_funct_1(k7_relat_1('#skF_5',D_863)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12293,c_8190])).

tff(c_8020,plain,(
    ! [A_838,B_839,C_840] :
      ( k1_relset_1(A_838,B_839,C_840) = k1_relat_1(C_840)
      | ~ m1_subset_1(C_840,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8030,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_8020])).

tff(c_12307,plain,(
    ! [B_1202,A_1203,C_1204] :
      ( k1_xboole_0 = B_1202
      | k1_relset_1(A_1203,B_1202,C_1204) = A_1203
      | ~ v1_funct_2(C_1204,A_1203,B_1202)
      | ~ m1_subset_1(C_1204,k1_zfmisc_1(k2_zfmisc_1(A_1203,B_1202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12313,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_12307])).

tff(c_12323,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8030,c_12313])).

tff(c_12324,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_12323])).

tff(c_12339,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12324,c_32])).

tff(c_12402,plain,(
    ! [A_1207] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1207)) = A_1207
      | ~ r1_tarski(A_1207,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_12339])).

tff(c_60,plain,(
    ! [B_41,A_40] :
      ( m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41),A_40)))
      | ~ r1_tarski(k2_relat_1(B_41),A_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_12411,plain,(
    ! [A_1207,A_40] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_1207),k1_zfmisc_1(k2_zfmisc_1(A_1207,A_40)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_1207)),A_40)
      | ~ v1_funct_1(k7_relat_1('#skF_5',A_1207))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_1207))
      | ~ r1_tarski(A_1207,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12402,c_60])).

tff(c_12448,plain,(
    ! [A_1207,A_40] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_1207),k1_zfmisc_1(k2_zfmisc_1(A_1207,A_40)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_1207)),A_40)
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_1207))
      | ~ r1_tarski(A_1207,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12295,c_12411])).

tff(c_103675,plain,(
    ! [A_3124,A_3125] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_3124),k1_zfmisc_1(k2_zfmisc_1(A_3124,A_3125)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_3124)),A_3125)
      | ~ r1_tarski(A_3124,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12710,c_12448])).

tff(c_357,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( v1_funct_1(k2_partfun1(A_110,B_111,C_112,D_113))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_359,plain,(
    ! [D_113] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_113))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_357])).

tff(c_366,plain,(
    ! [D_113] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_359])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_164,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_164])).

tff(c_370,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5415,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_12296,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12293,c_5415])).

tff(c_103709,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_103675,c_12296])).

tff(c_103775,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_103709])).

tff(c_103803,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_103775])).

tff(c_103814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12710,c_12708,c_103803])).

tff(c_103815,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_104155,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104147,c_103815])).

tff(c_103816,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_103992,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) = k1_relat_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_103816,c_103979])).

tff(c_104150,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) = k1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104147,c_104147,c_103992])).

tff(c_104154,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104147,c_103816])).

tff(c_104375,plain,(
    ! [B_3198,C_3199,A_3200] :
      ( k1_xboole_0 = B_3198
      | v1_funct_2(C_3199,A_3200,B_3198)
      | k1_relset_1(A_3200,B_3198,C_3199) != A_3200
      | ~ m1_subset_1(C_3199,k1_zfmisc_1(k2_zfmisc_1(A_3200,B_3198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_104378,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_104154,c_104375])).

tff(c_104392,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104150,c_104378])).

tff(c_104393,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_104155,c_106,c_104392])).

tff(c_104402,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104256,c_104393])).

tff(c_104406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_104402])).

tff(c_104408,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_104407,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_104417,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104408,c_104407])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104411,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104407,c_16])).

tff(c_104430,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_104411])).

tff(c_104424,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_70])).

tff(c_106237,plain,(
    ! [B_3497,A_3498] :
      ( B_3497 = A_3498
      | ~ r1_tarski(B_3497,A_3498)
      | ~ r1_tarski(A_3498,B_3497) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106243,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_104424,c_106237])).

tff(c_106250,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104430,c_106243])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104412,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104407,c_8])).

tff(c_104429,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_104412])).

tff(c_106266,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106250,c_104429])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104409,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104407,c_104407,c_20])).

tff(c_104432,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_104417,c_104409])).

tff(c_104422,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_72])).

tff(c_104456,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104432,c_104422])).

tff(c_106260,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106250,c_104456])).

tff(c_106437,plain,(
    ! [C_3524,B_3525,A_3526] :
      ( ~ v1_xboole_0(C_3524)
      | ~ m1_subset_1(B_3525,k1_zfmisc_1(C_3524))
      | ~ r2_hidden(A_3526,B_3525) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_106441,plain,(
    ! [A_3526] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_3526,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106260,c_106437])).

tff(c_106448,plain,(
    ! [A_3527] : ~ r2_hidden(A_3527,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106266,c_106441])).

tff(c_106454,plain,(
    ! [B_3528] : r1_tarski('#skF_5',B_3528) ),
    inference(resolution,[status(thm)],[c_6,c_106448])).

tff(c_106247,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_104430,c_106237])).

tff(c_106324,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106250,c_106250,c_106247])).

tff(c_106461,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_106454,c_106324])).

tff(c_104423,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_74])).

tff(c_106263,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106250,c_106250,c_104423])).

tff(c_106472,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106461,c_106263])).

tff(c_105249,plain,(
    ! [B_3328,A_3329] :
      ( B_3328 = A_3329
      | ~ r1_tarski(B_3328,A_3329)
      | ~ r1_tarski(A_3329,B_3328) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105255,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_104424,c_105249])).

tff(c_105262,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104430,c_105255])).

tff(c_105275,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105262,c_104429])).

tff(c_105269,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105262,c_104456])).

tff(c_105475,plain,(
    ! [C_3362,B_3363,A_3364] :
      ( ~ v1_xboole_0(C_3362)
      | ~ m1_subset_1(B_3363,k1_zfmisc_1(C_3362))
      | ~ r2_hidden(A_3364,B_3363) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105477,plain,(
    ! [A_3364] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_3364,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_105269,c_105475])).

tff(c_105481,plain,(
    ! [A_3365] : ~ r2_hidden(A_3365,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105275,c_105477])).

tff(c_105489,plain,(
    ! [B_3367] : r1_tarski('#skF_5',B_3367) ),
    inference(resolution,[status(thm)],[c_6,c_105481])).

tff(c_105259,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_104430,c_105249])).

tff(c_105333,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105262,c_105262,c_105259])).

tff(c_105496,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105489,c_105333])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104410,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104407,c_104407,c_22])).

tff(c_104440,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_104417,c_104410])).

tff(c_105270,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105262,c_105262,c_104440])).

tff(c_105447,plain,(
    ! [C_3355,B_3356,A_3357] :
      ( v5_relat_1(C_3355,B_3356)
      | ~ m1_subset_1(C_3355,k1_zfmisc_1(k2_zfmisc_1(A_3357,B_3356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_105471,plain,(
    ! [C_3360,B_3361] :
      ( v5_relat_1(C_3360,B_3361)
      | ~ m1_subset_1(C_3360,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105270,c_105447])).

tff(c_105474,plain,(
    ! [B_3361] : v5_relat_1('#skF_5',B_3361) ),
    inference(resolution,[status(thm)],[c_105269,c_105471])).

tff(c_105499,plain,(
    ! [B_3361] : v5_relat_1('#skF_4',B_3361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105496,c_105474])).

tff(c_105506,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105496,c_76])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k7_relat_1(B_17,A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_105334,plain,(
    ! [A_3335] :
      ( A_3335 = '#skF_4'
      | ~ r1_tarski(A_3335,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105262,c_105262,c_105259])).

tff(c_105349,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_4',A_16) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_105334])).

tff(c_105359,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_105349])).

tff(c_105404,plain,(
    ! [C_3347,B_3348,A_3349] :
      ( ~ v1_xboole_0(C_3347)
      | ~ m1_subset_1(B_3348,k1_zfmisc_1(C_3347))
      | ~ r2_hidden(A_3349,B_3348) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105406,plain,(
    ! [A_3349] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_3349,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_105269,c_105404])).

tff(c_105410,plain,(
    ! [A_3350] : ~ r2_hidden(A_3350,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105275,c_105406])).

tff(c_105423,plain,(
    ! [B_3354] : r1_tarski('#skF_5',B_3354) ),
    inference(resolution,[status(thm)],[c_6,c_105410])).

tff(c_105430,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105423,c_105333])).

tff(c_105239,plain,(
    ! [C_3324,A_3325,B_3326] :
      ( v1_relat_1(C_3324)
      | ~ m1_subset_1(C_3324,k1_zfmisc_1(k2_zfmisc_1(A_3325,B_3326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_105244,plain,(
    ! [C_3327] :
      ( v1_relat_1(C_3327)
      | ~ m1_subset_1(C_3327,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104440,c_105239])).

tff(c_105248,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_104456,c_105244])).

tff(c_105440,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105430,c_105248])).

tff(c_105444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105359,c_105440])).

tff(c_105445,plain,(
    ! [A_16] : k7_relat_1('#skF_4',A_16) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_105349])).

tff(c_105503,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105496,c_105269])).

tff(c_105271,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105262,c_105262,c_104432])).

tff(c_106094,plain,(
    ! [A_3450,B_3451,C_3452,D_3453] :
      ( k2_partfun1(A_3450,B_3451,C_3452,D_3453) = k7_relat_1(C_3452,D_3453)
      | ~ m1_subset_1(C_3452,k1_zfmisc_1(k2_zfmisc_1(A_3450,B_3451)))
      | ~ v1_funct_1(C_3452) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_106185,plain,(
    ! [A_3485,C_3486,D_3487] :
      ( k2_partfun1(A_3485,'#skF_4',C_3486,D_3487) = k7_relat_1(C_3486,D_3487)
      | ~ m1_subset_1(C_3486,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_3486) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105271,c_106094])).

tff(c_106189,plain,(
    ! [A_3485,D_3487] :
      ( k2_partfun1(A_3485,'#skF_4','#skF_4',D_3487) = k7_relat_1('#skF_4',D_3487)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105503,c_106185])).

tff(c_106193,plain,(
    ! [A_3485,D_3487] : k2_partfun1(A_3485,'#skF_4','#skF_4',D_3487) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105506,c_105445,c_106189])).

tff(c_105446,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_105349])).

tff(c_106146,plain,(
    ! [B_3472,C_3473,D_3474] :
      ( k2_partfun1('#skF_4',B_3472,C_3473,D_3474) = k7_relat_1(C_3473,D_3474)
      | ~ m1_subset_1(C_3473,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_3473) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105270,c_106094])).

tff(c_106150,plain,(
    ! [B_3472,D_3474] :
      ( k2_partfun1('#skF_4',B_3472,'#skF_4',D_3474) = k7_relat_1('#skF_4',D_3474)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105503,c_106146])).

tff(c_106154,plain,(
    ! [B_3472,D_3474] : k2_partfun1('#skF_4',B_3472,'#skF_4',D_3474) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105506,c_105445,c_106150])).

tff(c_105942,plain,(
    ! [A_3425,B_3426,C_3427,D_3428] :
      ( v1_funct_1(k2_partfun1(A_3425,B_3426,C_3427,D_3428))
      | ~ m1_subset_1(C_3427,k1_zfmisc_1(k2_zfmisc_1(A_3425,B_3426)))
      | ~ v1_funct_1(C_3427) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_105947,plain,(
    ! [A_3429,C_3430,D_3431] :
      ( v1_funct_1(k2_partfun1(A_3429,'#skF_4',C_3430,D_3431))
      | ~ m1_subset_1(C_3430,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_3430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105271,c_105942])).

tff(c_105949,plain,(
    ! [A_3429,D_3431] :
      ( v1_funct_1(k2_partfun1(A_3429,'#skF_4','#skF_4',D_3431))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105503,c_105947])).

tff(c_105952,plain,(
    ! [A_3429,D_3431] : v1_funct_1(k2_partfun1(A_3429,'#skF_4','#skF_4',D_3431)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105506,c_105949])).

tff(c_105961,plain,(
    ! [B_3437,A_3438] :
      ( m1_subset_1(B_3437,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_3437),A_3438)))
      | ~ r1_tarski(k2_relat_1(B_3437),A_3438)
      | ~ v1_funct_1(B_3437)
      | ~ v1_relat_1(B_3437) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_106027,plain,(
    ! [B_3444] :
      ( m1_subset_1(B_3444,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_3444),'#skF_4')
      | ~ v1_funct_1(B_3444)
      | ~ v1_relat_1(B_3444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105271,c_105961])).

tff(c_106043,plain,(
    ! [B_3445] :
      ( m1_subset_1(B_3445,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_3445)
      | ~ v5_relat_1(B_3445,'#skF_4')
      | ~ v1_relat_1(B_3445) ) ),
    inference(resolution,[status(thm)],[c_28,c_106027])).

tff(c_104480,plain,(
    ! [B_3212,A_3213] :
      ( B_3212 = A_3213
      | ~ r1_tarski(B_3212,A_3213)
      | ~ r1_tarski(A_3213,B_3212) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104486,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_104424,c_104480])).

tff(c_104493,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104430,c_104486])).

tff(c_104511,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104493,c_104429])).

tff(c_104505,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104493,c_104456])).

tff(c_104729,plain,(
    ! [C_3262,B_3263,A_3264] :
      ( ~ v1_xboole_0(C_3262)
      | ~ m1_subset_1(B_3263,k1_zfmisc_1(C_3262))
      | ~ r2_hidden(A_3264,B_3263) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104731,plain,(
    ! [A_3264] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_3264,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_104505,c_104729])).

tff(c_104735,plain,(
    ! [A_3265] : ~ r2_hidden(A_3265,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104511,c_104731])).

tff(c_104741,plain,(
    ! [B_3266] : r1_tarski('#skF_5',B_3266) ),
    inference(resolution,[status(thm)],[c_6,c_104735])).

tff(c_104490,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_104430,c_104480])).

tff(c_104564,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104493,c_104493,c_104490])).

tff(c_104748,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_104741,c_104564])).

tff(c_104759,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104748,c_76])).

tff(c_104757,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104748,c_104505])).

tff(c_104507,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104493,c_104493,c_104432])).

tff(c_105175,plain,(
    ! [A_3311,B_3312,C_3313,D_3314] :
      ( v1_funct_1(k2_partfun1(A_3311,B_3312,C_3313,D_3314))
      | ~ m1_subset_1(C_3313,k1_zfmisc_1(k2_zfmisc_1(A_3311,B_3312)))
      | ~ v1_funct_1(C_3313) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_105180,plain,(
    ! [A_3315,C_3316,D_3317] :
      ( v1_funct_1(k2_partfun1(A_3315,'#skF_4',C_3316,D_3317))
      | ~ m1_subset_1(C_3316,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_3316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104507,c_105175])).

tff(c_105182,plain,(
    ! [A_3315,D_3317] :
      ( v1_funct_1(k2_partfun1(A_3315,'#skF_4','#skF_4',D_3317))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_104757,c_105180])).

tff(c_105185,plain,(
    ! [A_3315,D_3317] : v1_funct_1(k2_partfun1(A_3315,'#skF_4','#skF_4',D_3317)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104759,c_105182])).

tff(c_104458,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104417,c_104417,c_104432,c_104417,c_66])).

tff(c_104459,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_104458])).

tff(c_104504,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104493,c_104493,c_104459])).

tff(c_104756,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104748,c_104504])).

tff(c_105227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105185,c_104756])).

tff(c_105228,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_104458])).

tff(c_105231,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_105228])).

tff(c_105352,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105262,c_105262,c_105262,c_105231])).

tff(c_105501,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105496,c_105352])).

tff(c_106056,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_106043,c_105501])).

tff(c_106073,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105952,c_106056])).

tff(c_106110,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_106073])).

tff(c_106155,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106154,c_106110])).

tff(c_106160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105446,c_106155])).

tff(c_106161,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_106073])).

tff(c_106207,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106193,c_106161])).

tff(c_106213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105499,c_106207])).

tff(c_106215,plain,(
    m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_105228])).

tff(c_106258,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106250,c_106250,c_106250,c_106215])).

tff(c_106439,plain,(
    ! [A_3526] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_3526,k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_106258,c_106437])).

tff(c_106444,plain,(
    ! [A_3526] : ~ r2_hidden(A_3526,k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106266,c_106439])).

tff(c_106512,plain,(
    ! [A_3534] : ~ r2_hidden(A_3534,k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106461,c_106444])).

tff(c_106534,plain,(
    ! [B_3543] : r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),B_3543) ),
    inference(resolution,[status(thm)],[c_6,c_106512])).

tff(c_106541,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_106534,c_106324])).

tff(c_106214,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_105228])).

tff(c_106255,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106250,c_106250,c_106250,c_106214])).

tff(c_106466,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106461,c_106255])).

tff(c_106545,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106541,c_106466])).

tff(c_106553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106472,c_106545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:09:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.92/21.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.92/21.42  
% 31.92/21.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.92/21.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 31.92/21.43  
% 31.92/21.43  %Foreground sorts:
% 31.92/21.43  
% 31.92/21.43  
% 31.92/21.43  %Background operators:
% 31.92/21.43  
% 31.92/21.43  
% 31.92/21.43  %Foreground operators:
% 31.92/21.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 31.92/21.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.92/21.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.92/21.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 31.92/21.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.92/21.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.92/21.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 31.92/21.43  tff('#skF_5', type, '#skF_5': $i).
% 31.92/21.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 31.92/21.43  tff('#skF_2', type, '#skF_2': $i).
% 31.92/21.43  tff('#skF_3', type, '#skF_3': $i).
% 31.92/21.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 31.92/21.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 31.92/21.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.92/21.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.92/21.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 31.92/21.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 31.92/21.43  tff('#skF_4', type, '#skF_4': $i).
% 31.92/21.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.92/21.43  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 31.92/21.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 31.92/21.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 31.92/21.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 31.92/21.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 31.92/21.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.92/21.43  
% 32.27/21.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 32.27/21.46  tff(f_148, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 32.27/21.46  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 32.27/21.46  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 32.27/21.46  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 32.27/21.46  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 32.27/21.46  tff(f_116, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 32.27/21.46  tff(f_110, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 32.27/21.46  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 32.27/21.46  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 32.27/21.46  tff(f_128, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 32.27/21.46  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 32.27/21.46  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.27/21.46  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 32.27/21.46  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 32.27/21.46  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 32.27/21.46  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 32.27/21.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 32.27/21.46  tff(c_70, plain, (r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 32.27/21.46  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 32.27/21.46  tff(c_120, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 32.27/21.46  tff(c_128, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_120])).
% 32.27/21.46  tff(c_68, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_148])).
% 32.27/21.46  tff(c_106, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_68])).
% 32.27/21.46  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 32.27/21.46  tff(c_103979, plain, (![A_3152, B_3153, C_3154]: (k1_relset_1(A_3152, B_3153, C_3154)=k1_relat_1(C_3154) | ~m1_subset_1(C_3154, k1_zfmisc_1(k2_zfmisc_1(A_3152, B_3153))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 32.27/21.46  tff(c_103993, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_103979])).
% 32.27/21.46  tff(c_104203, plain, (![B_3192, A_3193, C_3194]: (k1_xboole_0=B_3192 | k1_relset_1(A_3193, B_3192, C_3194)=A_3193 | ~v1_funct_2(C_3194, A_3193, B_3192) | ~m1_subset_1(C_3194, k1_zfmisc_1(k2_zfmisc_1(A_3193, B_3192))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 32.27/21.46  tff(c_104212, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_104203])).
% 32.27/21.46  tff(c_104225, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_103993, c_104212])).
% 32.27/21.46  tff(c_104226, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_106, c_104225])).
% 32.27/21.46  tff(c_32, plain, (![B_19, A_18]: (k1_relat_1(k7_relat_1(B_19, A_18))=A_18 | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 32.27/21.46  tff(c_104244, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_5', A_18))=A_18 | ~r1_tarski(A_18, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_104226, c_32])).
% 32.27/21.46  tff(c_104256, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_5', A_18))=A_18 | ~r1_tarski(A_18, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_104244])).
% 32.27/21.46  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 32.27/21.46  tff(c_104130, plain, (![A_3185, B_3186, C_3187, D_3188]: (k2_partfun1(A_3185, B_3186, C_3187, D_3188)=k7_relat_1(C_3187, D_3188) | ~m1_subset_1(C_3187, k1_zfmisc_1(k2_zfmisc_1(A_3185, B_3186))) | ~v1_funct_1(C_3187))), inference(cnfTransformation, [status(thm)], [f_116])).
% 32.27/21.46  tff(c_104136, plain, (![D_3188]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_3188)=k7_relat_1('#skF_5', D_3188) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_104130])).
% 32.27/21.46  tff(c_104147, plain, (![D_3188]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_3188)=k7_relat_1('#skF_5', D_3188))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_104136])).
% 32.27/21.46  tff(c_12281, plain, (![A_1194, B_1195, C_1196, D_1197]: (k2_partfun1(A_1194, B_1195, C_1196, D_1197)=k7_relat_1(C_1196, D_1197) | ~m1_subset_1(C_1196, k1_zfmisc_1(k2_zfmisc_1(A_1194, B_1195))) | ~v1_funct_1(C_1196))), inference(cnfTransformation, [status(thm)], [f_116])).
% 32.27/21.46  tff(c_12285, plain, (![D_1197]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_1197)=k7_relat_1('#skF_5', D_1197) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_12281])).
% 32.27/21.46  tff(c_12293, plain, (![D_1197]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_1197)=k7_relat_1('#skF_5', D_1197))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12285])).
% 32.27/21.46  tff(c_12621, plain, (![A_1217, B_1218, C_1219, D_1220]: (m1_subset_1(k2_partfun1(A_1217, B_1218, C_1219, D_1220), k1_zfmisc_1(k2_zfmisc_1(A_1217, B_1218))) | ~m1_subset_1(C_1219, k1_zfmisc_1(k2_zfmisc_1(A_1217, B_1218))) | ~v1_funct_1(C_1219))), inference(cnfTransformation, [status(thm)], [f_110])).
% 32.27/21.46  tff(c_12648, plain, (![D_1197]: (m1_subset_1(k7_relat_1('#skF_5', D_1197), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12293, c_12621])).
% 32.27/21.46  tff(c_12669, plain, (![D_1222]: (m1_subset_1(k7_relat_1('#skF_5', D_1222), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_12648])).
% 32.27/21.46  tff(c_34, plain, (![C_22, A_20, B_21]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 32.27/21.46  tff(c_12710, plain, (![D_1222]: (v1_relat_1(k7_relat_1('#skF_5', D_1222)))), inference(resolution, [status(thm)], [c_12669, c_34])).
% 32.27/21.46  tff(c_36, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 32.27/21.46  tff(c_12708, plain, (![D_1222]: (v5_relat_1(k7_relat_1('#skF_5', D_1222), '#skF_3'))), inference(resolution, [status(thm)], [c_12669, c_36])).
% 32.27/21.46  tff(c_28, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 32.27/21.46  tff(c_8181, plain, (![A_860, B_861, C_862, D_863]: (v1_funct_1(k2_partfun1(A_860, B_861, C_862, D_863)) | ~m1_subset_1(C_862, k1_zfmisc_1(k2_zfmisc_1(A_860, B_861))) | ~v1_funct_1(C_862))), inference(cnfTransformation, [status(thm)], [f_110])).
% 32.27/21.46  tff(c_8183, plain, (![D_863]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_863)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_8181])).
% 32.27/21.46  tff(c_8190, plain, (![D_863]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_863)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8183])).
% 32.27/21.46  tff(c_12295, plain, (![D_863]: (v1_funct_1(k7_relat_1('#skF_5', D_863)))), inference(demodulation, [status(thm), theory('equality')], [c_12293, c_8190])).
% 32.27/21.46  tff(c_8020, plain, (![A_838, B_839, C_840]: (k1_relset_1(A_838, B_839, C_840)=k1_relat_1(C_840) | ~m1_subset_1(C_840, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 32.27/21.46  tff(c_8030, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_8020])).
% 32.27/21.46  tff(c_12307, plain, (![B_1202, A_1203, C_1204]: (k1_xboole_0=B_1202 | k1_relset_1(A_1203, B_1202, C_1204)=A_1203 | ~v1_funct_2(C_1204, A_1203, B_1202) | ~m1_subset_1(C_1204, k1_zfmisc_1(k2_zfmisc_1(A_1203, B_1202))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 32.27/21.46  tff(c_12313, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_12307])).
% 32.27/21.46  tff(c_12323, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8030, c_12313])).
% 32.27/21.46  tff(c_12324, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_106, c_12323])).
% 32.27/21.46  tff(c_12339, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_5', A_18))=A_18 | ~r1_tarski(A_18, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12324, c_32])).
% 32.27/21.46  tff(c_12402, plain, (![A_1207]: (k1_relat_1(k7_relat_1('#skF_5', A_1207))=A_1207 | ~r1_tarski(A_1207, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_12339])).
% 32.27/21.46  tff(c_60, plain, (![B_41, A_40]: (m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41), A_40))) | ~r1_tarski(k2_relat_1(B_41), A_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_128])).
% 32.27/21.46  tff(c_12411, plain, (![A_1207, A_40]: (m1_subset_1(k7_relat_1('#skF_5', A_1207), k1_zfmisc_1(k2_zfmisc_1(A_1207, A_40))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_1207)), A_40) | ~v1_funct_1(k7_relat_1('#skF_5', A_1207)) | ~v1_relat_1(k7_relat_1('#skF_5', A_1207)) | ~r1_tarski(A_1207, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12402, c_60])).
% 32.27/21.46  tff(c_12448, plain, (![A_1207, A_40]: (m1_subset_1(k7_relat_1('#skF_5', A_1207), k1_zfmisc_1(k2_zfmisc_1(A_1207, A_40))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_1207)), A_40) | ~v1_relat_1(k7_relat_1('#skF_5', A_1207)) | ~r1_tarski(A_1207, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12295, c_12411])).
% 32.27/21.46  tff(c_103675, plain, (![A_3124, A_3125]: (m1_subset_1(k7_relat_1('#skF_5', A_3124), k1_zfmisc_1(k2_zfmisc_1(A_3124, A_3125))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_3124)), A_3125) | ~r1_tarski(A_3124, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12710, c_12448])).
% 32.27/21.46  tff(c_357, plain, (![A_110, B_111, C_112, D_113]: (v1_funct_1(k2_partfun1(A_110, B_111, C_112, D_113)) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_110])).
% 32.27/21.46  tff(c_359, plain, (![D_113]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_113)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_357])).
% 32.27/21.46  tff(c_366, plain, (![D_113]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_113)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_359])).
% 32.27/21.46  tff(c_66, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 32.27/21.46  tff(c_164, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 32.27/21.46  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_366, c_164])).
% 32.27/21.46  tff(c_370, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 32.27/21.46  tff(c_5415, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_370])).
% 32.27/21.46  tff(c_12296, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12293, c_5415])).
% 32.27/21.46  tff(c_103709, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3') | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_103675, c_12296])).
% 32.27/21.46  tff(c_103775, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_103709])).
% 32.27/21.46  tff(c_103803, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_103775])).
% 32.27/21.46  tff(c_103814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12710, c_12708, c_103803])).
% 32.27/21.46  tff(c_103815, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_370])).
% 32.27/21.46  tff(c_104155, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104147, c_103815])).
% 32.27/21.46  tff(c_103816, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_370])).
% 32.27/21.46  tff(c_103992, plain, (k1_relset_1('#skF_4', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_103816, c_103979])).
% 32.27/21.46  tff(c_104150, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104147, c_104147, c_103992])).
% 32.27/21.46  tff(c_104154, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_104147, c_103816])).
% 32.27/21.46  tff(c_104375, plain, (![B_3198, C_3199, A_3200]: (k1_xboole_0=B_3198 | v1_funct_2(C_3199, A_3200, B_3198) | k1_relset_1(A_3200, B_3198, C_3199)!=A_3200 | ~m1_subset_1(C_3199, k1_zfmisc_1(k2_zfmisc_1(A_3200, B_3198))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 32.27/21.46  tff(c_104378, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_104154, c_104375])).
% 32.27/21.46  tff(c_104392, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104150, c_104378])).
% 32.27/21.46  tff(c_104393, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_104155, c_106, c_104392])).
% 32.27/21.46  tff(c_104402, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_104256, c_104393])).
% 32.27/21.46  tff(c_104406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_104402])).
% 32.27/21.46  tff(c_104408, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_68])).
% 32.27/21.46  tff(c_104407, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 32.27/21.46  tff(c_104417, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104408, c_104407])).
% 32.27/21.46  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 32.27/21.46  tff(c_104411, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_104407, c_16])).
% 32.27/21.46  tff(c_104430, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_104411])).
% 32.27/21.46  tff(c_104424, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_70])).
% 32.27/21.46  tff(c_106237, plain, (![B_3497, A_3498]: (B_3497=A_3498 | ~r1_tarski(B_3497, A_3498) | ~r1_tarski(A_3498, B_3497))), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.27/21.46  tff(c_106243, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_104424, c_106237])).
% 32.27/21.46  tff(c_106250, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104430, c_106243])).
% 32.27/21.46  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 32.27/21.46  tff(c_104412, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104407, c_8])).
% 32.27/21.46  tff(c_104429, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_104412])).
% 32.27/21.46  tff(c_106266, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106250, c_104429])).
% 32.27/21.46  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 32.27/21.46  tff(c_104409, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104407, c_104407, c_20])).
% 32.27/21.46  tff(c_104432, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_104417, c_104409])).
% 32.27/21.46  tff(c_104422, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_72])).
% 32.27/21.46  tff(c_104456, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104432, c_104422])).
% 32.27/21.46  tff(c_106260, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106250, c_104456])).
% 32.27/21.46  tff(c_106437, plain, (![C_3524, B_3525, A_3526]: (~v1_xboole_0(C_3524) | ~m1_subset_1(B_3525, k1_zfmisc_1(C_3524)) | ~r2_hidden(A_3526, B_3525))), inference(cnfTransformation, [status(thm)], [f_54])).
% 32.27/21.46  tff(c_106441, plain, (![A_3526]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_3526, '#skF_5'))), inference(resolution, [status(thm)], [c_106260, c_106437])).
% 32.27/21.46  tff(c_106448, plain, (![A_3527]: (~r2_hidden(A_3527, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_106266, c_106441])).
% 32.27/21.46  tff(c_106454, plain, (![B_3528]: (r1_tarski('#skF_5', B_3528))), inference(resolution, [status(thm)], [c_6, c_106448])).
% 32.27/21.46  tff(c_106247, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_104430, c_106237])).
% 32.27/21.46  tff(c_106324, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106250, c_106250, c_106247])).
% 32.27/21.46  tff(c_106461, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_106454, c_106324])).
% 32.27/21.46  tff(c_104423, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_74])).
% 32.27/21.46  tff(c_106263, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106250, c_106250, c_104423])).
% 32.27/21.46  tff(c_106472, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106461, c_106263])).
% 32.27/21.46  tff(c_105249, plain, (![B_3328, A_3329]: (B_3328=A_3329 | ~r1_tarski(B_3328, A_3329) | ~r1_tarski(A_3329, B_3328))), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.27/21.46  tff(c_105255, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_104424, c_105249])).
% 32.27/21.46  tff(c_105262, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104430, c_105255])).
% 32.27/21.46  tff(c_105275, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105262, c_104429])).
% 32.27/21.46  tff(c_105269, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105262, c_104456])).
% 32.27/21.46  tff(c_105475, plain, (![C_3362, B_3363, A_3364]: (~v1_xboole_0(C_3362) | ~m1_subset_1(B_3363, k1_zfmisc_1(C_3362)) | ~r2_hidden(A_3364, B_3363))), inference(cnfTransformation, [status(thm)], [f_54])).
% 32.27/21.46  tff(c_105477, plain, (![A_3364]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_3364, '#skF_5'))), inference(resolution, [status(thm)], [c_105269, c_105475])).
% 32.27/21.46  tff(c_105481, plain, (![A_3365]: (~r2_hidden(A_3365, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_105275, c_105477])).
% 32.27/21.46  tff(c_105489, plain, (![B_3367]: (r1_tarski('#skF_5', B_3367))), inference(resolution, [status(thm)], [c_6, c_105481])).
% 32.27/21.46  tff(c_105259, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_104430, c_105249])).
% 32.27/21.46  tff(c_105333, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105262, c_105262, c_105259])).
% 32.27/21.46  tff(c_105496, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_105489, c_105333])).
% 32.27/21.46  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 32.27/21.46  tff(c_104410, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104407, c_104407, c_22])).
% 32.27/21.46  tff(c_104440, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_104417, c_104410])).
% 32.27/21.46  tff(c_105270, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105262, c_105262, c_104440])).
% 32.27/21.46  tff(c_105447, plain, (![C_3355, B_3356, A_3357]: (v5_relat_1(C_3355, B_3356) | ~m1_subset_1(C_3355, k1_zfmisc_1(k2_zfmisc_1(A_3357, B_3356))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 32.27/21.46  tff(c_105471, plain, (![C_3360, B_3361]: (v5_relat_1(C_3360, B_3361) | ~m1_subset_1(C_3360, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_105270, c_105447])).
% 32.27/21.46  tff(c_105474, plain, (![B_3361]: (v5_relat_1('#skF_5', B_3361))), inference(resolution, [status(thm)], [c_105269, c_105471])).
% 32.27/21.46  tff(c_105499, plain, (![B_3361]: (v5_relat_1('#skF_4', B_3361))), inference(demodulation, [status(thm), theory('equality')], [c_105496, c_105474])).
% 32.27/21.46  tff(c_105506, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105496, c_76])).
% 32.27/21.46  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k7_relat_1(B_17, A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 32.27/21.46  tff(c_105334, plain, (![A_3335]: (A_3335='#skF_4' | ~r1_tarski(A_3335, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105262, c_105262, c_105259])).
% 32.27/21.46  tff(c_105349, plain, (![A_16]: (k7_relat_1('#skF_4', A_16)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_105334])).
% 32.27/21.46  tff(c_105359, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_105349])).
% 32.27/21.46  tff(c_105404, plain, (![C_3347, B_3348, A_3349]: (~v1_xboole_0(C_3347) | ~m1_subset_1(B_3348, k1_zfmisc_1(C_3347)) | ~r2_hidden(A_3349, B_3348))), inference(cnfTransformation, [status(thm)], [f_54])).
% 32.27/21.46  tff(c_105406, plain, (![A_3349]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_3349, '#skF_5'))), inference(resolution, [status(thm)], [c_105269, c_105404])).
% 32.27/21.46  tff(c_105410, plain, (![A_3350]: (~r2_hidden(A_3350, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_105275, c_105406])).
% 32.27/21.46  tff(c_105423, plain, (![B_3354]: (r1_tarski('#skF_5', B_3354))), inference(resolution, [status(thm)], [c_6, c_105410])).
% 32.27/21.46  tff(c_105430, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_105423, c_105333])).
% 32.27/21.46  tff(c_105239, plain, (![C_3324, A_3325, B_3326]: (v1_relat_1(C_3324) | ~m1_subset_1(C_3324, k1_zfmisc_1(k2_zfmisc_1(A_3325, B_3326))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 32.27/21.46  tff(c_105244, plain, (![C_3327]: (v1_relat_1(C_3327) | ~m1_subset_1(C_3327, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_104440, c_105239])).
% 32.27/21.46  tff(c_105248, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_104456, c_105244])).
% 32.27/21.46  tff(c_105440, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105430, c_105248])).
% 32.27/21.46  tff(c_105444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105359, c_105440])).
% 32.27/21.46  tff(c_105445, plain, (![A_16]: (k7_relat_1('#skF_4', A_16)='#skF_4')), inference(splitRight, [status(thm)], [c_105349])).
% 32.27/21.46  tff(c_105503, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105496, c_105269])).
% 32.27/21.46  tff(c_105271, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105262, c_105262, c_104432])).
% 32.27/21.46  tff(c_106094, plain, (![A_3450, B_3451, C_3452, D_3453]: (k2_partfun1(A_3450, B_3451, C_3452, D_3453)=k7_relat_1(C_3452, D_3453) | ~m1_subset_1(C_3452, k1_zfmisc_1(k2_zfmisc_1(A_3450, B_3451))) | ~v1_funct_1(C_3452))), inference(cnfTransformation, [status(thm)], [f_116])).
% 32.27/21.46  tff(c_106185, plain, (![A_3485, C_3486, D_3487]: (k2_partfun1(A_3485, '#skF_4', C_3486, D_3487)=k7_relat_1(C_3486, D_3487) | ~m1_subset_1(C_3486, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_3486))), inference(superposition, [status(thm), theory('equality')], [c_105271, c_106094])).
% 32.27/21.46  tff(c_106189, plain, (![A_3485, D_3487]: (k2_partfun1(A_3485, '#skF_4', '#skF_4', D_3487)=k7_relat_1('#skF_4', D_3487) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_105503, c_106185])).
% 32.27/21.46  tff(c_106193, plain, (![A_3485, D_3487]: (k2_partfun1(A_3485, '#skF_4', '#skF_4', D_3487)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105506, c_105445, c_106189])).
% 32.27/21.46  tff(c_105446, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_105349])).
% 32.27/21.46  tff(c_106146, plain, (![B_3472, C_3473, D_3474]: (k2_partfun1('#skF_4', B_3472, C_3473, D_3474)=k7_relat_1(C_3473, D_3474) | ~m1_subset_1(C_3473, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_3473))), inference(superposition, [status(thm), theory('equality')], [c_105270, c_106094])).
% 32.27/21.46  tff(c_106150, plain, (![B_3472, D_3474]: (k2_partfun1('#skF_4', B_3472, '#skF_4', D_3474)=k7_relat_1('#skF_4', D_3474) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_105503, c_106146])).
% 32.27/21.46  tff(c_106154, plain, (![B_3472, D_3474]: (k2_partfun1('#skF_4', B_3472, '#skF_4', D_3474)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105506, c_105445, c_106150])).
% 32.27/21.46  tff(c_105942, plain, (![A_3425, B_3426, C_3427, D_3428]: (v1_funct_1(k2_partfun1(A_3425, B_3426, C_3427, D_3428)) | ~m1_subset_1(C_3427, k1_zfmisc_1(k2_zfmisc_1(A_3425, B_3426))) | ~v1_funct_1(C_3427))), inference(cnfTransformation, [status(thm)], [f_110])).
% 32.27/21.46  tff(c_105947, plain, (![A_3429, C_3430, D_3431]: (v1_funct_1(k2_partfun1(A_3429, '#skF_4', C_3430, D_3431)) | ~m1_subset_1(C_3430, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_3430))), inference(superposition, [status(thm), theory('equality')], [c_105271, c_105942])).
% 32.27/21.46  tff(c_105949, plain, (![A_3429, D_3431]: (v1_funct_1(k2_partfun1(A_3429, '#skF_4', '#skF_4', D_3431)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_105503, c_105947])).
% 32.27/21.46  tff(c_105952, plain, (![A_3429, D_3431]: (v1_funct_1(k2_partfun1(A_3429, '#skF_4', '#skF_4', D_3431)))), inference(demodulation, [status(thm), theory('equality')], [c_105506, c_105949])).
% 32.27/21.46  tff(c_105961, plain, (![B_3437, A_3438]: (m1_subset_1(B_3437, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_3437), A_3438))) | ~r1_tarski(k2_relat_1(B_3437), A_3438) | ~v1_funct_1(B_3437) | ~v1_relat_1(B_3437))), inference(cnfTransformation, [status(thm)], [f_128])).
% 32.27/21.46  tff(c_106027, plain, (![B_3444]: (m1_subset_1(B_3444, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_3444), '#skF_4') | ~v1_funct_1(B_3444) | ~v1_relat_1(B_3444))), inference(superposition, [status(thm), theory('equality')], [c_105271, c_105961])).
% 32.27/21.46  tff(c_106043, plain, (![B_3445]: (m1_subset_1(B_3445, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_3445) | ~v5_relat_1(B_3445, '#skF_4') | ~v1_relat_1(B_3445))), inference(resolution, [status(thm)], [c_28, c_106027])).
% 32.27/21.46  tff(c_104480, plain, (![B_3212, A_3213]: (B_3212=A_3213 | ~r1_tarski(B_3212, A_3213) | ~r1_tarski(A_3213, B_3212))), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.27/21.46  tff(c_104486, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_104424, c_104480])).
% 32.27/21.46  tff(c_104493, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104430, c_104486])).
% 32.27/21.46  tff(c_104511, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104493, c_104429])).
% 32.27/21.46  tff(c_104505, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104493, c_104456])).
% 32.27/21.46  tff(c_104729, plain, (![C_3262, B_3263, A_3264]: (~v1_xboole_0(C_3262) | ~m1_subset_1(B_3263, k1_zfmisc_1(C_3262)) | ~r2_hidden(A_3264, B_3263))), inference(cnfTransformation, [status(thm)], [f_54])).
% 32.27/21.46  tff(c_104731, plain, (![A_3264]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_3264, '#skF_5'))), inference(resolution, [status(thm)], [c_104505, c_104729])).
% 32.27/21.46  tff(c_104735, plain, (![A_3265]: (~r2_hidden(A_3265, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_104511, c_104731])).
% 32.27/21.46  tff(c_104741, plain, (![B_3266]: (r1_tarski('#skF_5', B_3266))), inference(resolution, [status(thm)], [c_6, c_104735])).
% 32.27/21.46  tff(c_104490, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_104430, c_104480])).
% 32.27/21.46  tff(c_104564, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104493, c_104493, c_104490])).
% 32.27/21.46  tff(c_104748, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_104741, c_104564])).
% 32.27/21.46  tff(c_104759, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104748, c_76])).
% 32.27/21.46  tff(c_104757, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104748, c_104505])).
% 32.27/21.46  tff(c_104507, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104493, c_104493, c_104432])).
% 32.27/21.46  tff(c_105175, plain, (![A_3311, B_3312, C_3313, D_3314]: (v1_funct_1(k2_partfun1(A_3311, B_3312, C_3313, D_3314)) | ~m1_subset_1(C_3313, k1_zfmisc_1(k2_zfmisc_1(A_3311, B_3312))) | ~v1_funct_1(C_3313))), inference(cnfTransformation, [status(thm)], [f_110])).
% 32.27/21.46  tff(c_105180, plain, (![A_3315, C_3316, D_3317]: (v1_funct_1(k2_partfun1(A_3315, '#skF_4', C_3316, D_3317)) | ~m1_subset_1(C_3316, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_3316))), inference(superposition, [status(thm), theory('equality')], [c_104507, c_105175])).
% 32.27/21.46  tff(c_105182, plain, (![A_3315, D_3317]: (v1_funct_1(k2_partfun1(A_3315, '#skF_4', '#skF_4', D_3317)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_104757, c_105180])).
% 32.27/21.46  tff(c_105185, plain, (![A_3315, D_3317]: (v1_funct_1(k2_partfun1(A_3315, '#skF_4', '#skF_4', D_3317)))), inference(demodulation, [status(thm), theory('equality')], [c_104759, c_105182])).
% 32.27/21.46  tff(c_104458, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3')) | ~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104417, c_104417, c_104432, c_104417, c_66])).
% 32.27/21.46  tff(c_104459, plain, (~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_104458])).
% 32.27/21.46  tff(c_104504, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104493, c_104493, c_104459])).
% 32.27/21.46  tff(c_104756, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104748, c_104504])).
% 32.27/21.46  tff(c_105227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105185, c_104756])).
% 32.27/21.46  tff(c_105228, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_104458])).
% 32.27/21.46  tff(c_105231, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_105228])).
% 32.27/21.46  tff(c_105352, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105262, c_105262, c_105262, c_105231])).
% 32.27/21.46  tff(c_105501, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105496, c_105352])).
% 32.27/21.46  tff(c_106056, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_106043, c_105501])).
% 32.27/21.46  tff(c_106073, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105952, c_106056])).
% 32.27/21.46  tff(c_106110, plain, (~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_106073])).
% 32.27/21.46  tff(c_106155, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106154, c_106110])).
% 32.27/21.46  tff(c_106160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105446, c_106155])).
% 32.27/21.46  tff(c_106161, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_106073])).
% 32.27/21.46  tff(c_106207, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106193, c_106161])).
% 32.27/21.46  tff(c_106213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105499, c_106207])).
% 32.27/21.46  tff(c_106215, plain, (m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_105228])).
% 32.27/21.46  tff(c_106258, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106250, c_106250, c_106250, c_106215])).
% 32.27/21.46  tff(c_106439, plain, (![A_3526]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_3526, k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_106258, c_106437])).
% 32.27/21.46  tff(c_106444, plain, (![A_3526]: (~r2_hidden(A_3526, k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_106266, c_106439])).
% 32.27/21.46  tff(c_106512, plain, (![A_3534]: (~r2_hidden(A_3534, k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_106461, c_106444])).
% 32.27/21.46  tff(c_106534, plain, (![B_3543]: (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), B_3543))), inference(resolution, [status(thm)], [c_6, c_106512])).
% 32.27/21.46  tff(c_106541, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_106534, c_106324])).
% 32.27/21.46  tff(c_106214, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_105228])).
% 32.27/21.46  tff(c_106255, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106250, c_106250, c_106250, c_106214])).
% 32.27/21.46  tff(c_106466, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106461, c_106255])).
% 32.27/21.46  tff(c_106545, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106541, c_106466])).
% 32.27/21.46  tff(c_106553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106472, c_106545])).
% 32.27/21.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.27/21.46  
% 32.27/21.46  Inference rules
% 32.27/21.46  ----------------------
% 32.27/21.46  #Ref     : 0
% 32.27/21.46  #Sup     : 22509
% 32.27/21.46  #Fact    : 0
% 32.27/21.46  #Define  : 0
% 32.27/21.46  #Split   : 106
% 32.27/21.46  #Chain   : 0
% 32.27/21.46  #Close   : 0
% 32.27/21.46  
% 32.27/21.46  Ordering : KBO
% 32.27/21.46  
% 32.27/21.46  Simplification rules
% 32.27/21.46  ----------------------
% 32.27/21.46  #Subsume      : 6863
% 32.27/21.46  #Demod        : 39855
% 32.27/21.46  #Tautology    : 6545
% 32.27/21.46  #SimpNegUnit  : 258
% 32.27/21.46  #BackRed      : 289
% 32.27/21.46  
% 32.27/21.46  #Partial instantiations: 0
% 32.27/21.46  #Strategies tried      : 1
% 32.27/21.46  
% 32.27/21.46  Timing (in seconds)
% 32.27/21.46  ----------------------
% 32.27/21.46  Preprocessing        : 0.35
% 32.27/21.46  Parsing              : 0.18
% 32.27/21.46  CNF conversion       : 0.02
% 32.27/21.46  Main loop            : 20.31
% 32.27/21.46  Inferencing          : 3.42
% 32.27/21.46  Reduction            : 9.02
% 32.27/21.46  Demodulation         : 7.50
% 32.27/21.46  BG Simplification    : 0.35
% 32.27/21.46  Subsumption          : 6.56
% 32.27/21.46  Abstraction          : 0.59
% 32.27/21.46  MUC search           : 0.00
% 32.27/21.46  Cooper               : 0.00
% 32.27/21.46  Total                : 20.73
% 32.27/21.46  Index Insertion      : 0.00
% 32.27/21.46  Index Deletion       : 0.00
% 32.27/21.46  Index Matching       : 0.00
% 32.27/21.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
