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
% DateTime   : Thu Dec  3 10:11:39 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 314 expanded)
%              Number of leaves         :   36 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 ( 991 expanded)
%              Number of equality atoms :   59 ( 276 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3347,plain,(
    ! [A_360,B_361,D_362] :
      ( r2_relset_1(A_360,B_361,D_362,D_362)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3360,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_3347])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_987,plain,(
    ! [A_143,B_144,D_145] :
      ( r2_relset_1(A_143,B_144,D_145,D_145)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1004,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_987])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_174,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_194,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_174])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1119,plain,(
    ! [A_163,B_164,C_165] :
      ( k1_relset_1(A_163,B_164,C_165) = k1_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1141,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1119])).

tff(c_1298,plain,(
    ! [B_189,A_190,C_191] :
      ( k1_xboole_0 = B_189
      | k1_relset_1(A_190,B_189,C_191) = A_190
      | ~ v1_funct_2(C_191,A_190,B_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1308,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1298])).

tff(c_1323,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1141,c_1308])).

tff(c_1328,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1323])).

tff(c_195,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_174])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1142,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1119])).

tff(c_1311,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1298])).

tff(c_1326,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1142,c_1311])).

tff(c_1334,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1326])).

tff(c_1480,plain,(
    ! [A_210,B_211] :
      ( r2_hidden('#skF_3'(A_210,B_211),k1_relat_1(A_210))
      | B_211 = A_210
      | k1_relat_1(B_211) != k1_relat_1(A_210)
      | ~ v1_funct_1(B_211)
      | ~ v1_relat_1(B_211)
      | ~ v1_funct_1(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1490,plain,(
    ! [B_211] :
      ( r2_hidden('#skF_3'('#skF_6',B_211),'#skF_4')
      | B_211 = '#skF_6'
      | k1_relat_1(B_211) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_211)
      | ~ v1_relat_1(B_211)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_1480])).

tff(c_2522,plain,(
    ! [B_315] :
      ( r2_hidden('#skF_3'('#skF_6',B_315),'#skF_4')
      | B_315 = '#skF_6'
      | k1_relat_1(B_315) != '#skF_4'
      | ~ v1_funct_1(B_315)
      | ~ v1_relat_1(B_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_68,c_1334,c_1490])).

tff(c_56,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_7',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2681,plain,(
    ! [B_328] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_328)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_328))
      | B_328 = '#skF_6'
      | k1_relat_1(B_328) != '#skF_4'
      | ~ v1_funct_1(B_328)
      | ~ v1_relat_1(B_328) ) ),
    inference(resolution,[status(thm)],[c_2522,c_56])).

tff(c_28,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_3'(A_18,B_22)) != k1_funct_1(A_18,'#skF_3'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2688,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2681,c_28])).

tff(c_2695,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_62,c_1328,c_195,c_68,c_1334,c_1328,c_2688])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2718,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2695,c_54])).

tff(c_2729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_2718])).

tff(c_2730,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1326])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2758,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_12])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2755,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_2730,c_18])).

tff(c_860,plain,(
    ! [C_135,B_136,A_137] :
      ( ~ v1_xboole_0(C_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(C_135))
      | ~ r2_hidden(A_137,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_876,plain,(
    ! [A_137] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_137,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_860])).

tff(c_878,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_2932,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2755,c_878])).

tff(c_2939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2758,c_2932])).

tff(c_2940,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1323])).

tff(c_2968,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_12])).

tff(c_2965,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_2940,c_18])).

tff(c_3080,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2965,c_878])).

tff(c_3087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_3080])).

tff(c_3090,plain,(
    ! [A_348] : ~ r2_hidden(A_348,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_3100,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_3090])).

tff(c_3089,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3109,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3100,c_14])).

tff(c_3376,plain,(
    ! [A_363] :
      ( A_363 = '#skF_7'
      | ~ v1_xboole_0(A_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_14])).

tff(c_3387,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3089,c_3376])).

tff(c_3471,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3387,c_64])).

tff(c_26,plain,(
    ! [C_17,B_16,A_15] :
      ( ~ v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3490,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_15,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3471,c_26])).

tff(c_3499,plain,(
    ! [A_368] : ~ r2_hidden(A_368,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_3490])).

tff(c_3509,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_3499])).

tff(c_3117,plain,(
    ! [A_10] :
      ( A_10 = '#skF_7'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_14])).

tff(c_3516,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3509,c_3117])).

tff(c_3536,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3516,c_54])).

tff(c_3545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3360,c_3536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.69  
% 7.16/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.70  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 7.16/2.70  
% 7.16/2.70  %Foreground sorts:
% 7.16/2.70  
% 7.16/2.70  
% 7.16/2.70  %Background operators:
% 7.16/2.70  
% 7.16/2.70  
% 7.16/2.70  %Foreground operators:
% 7.16/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.16/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.16/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.16/2.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.16/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.16/2.70  tff('#skF_7', type, '#skF_7': $i).
% 7.16/2.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.16/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.16/2.70  tff('#skF_5', type, '#skF_5': $i).
% 7.16/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.16/2.70  tff('#skF_6', type, '#skF_6': $i).
% 7.16/2.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.16/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.16/2.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.16/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.16/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.16/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.16/2.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.16/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.16/2.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.16/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.16/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.16/2.70  
% 7.37/2.72  tff(f_135, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 7.37/2.72  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.37/2.72  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.37/2.72  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.37/2.72  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.37/2.72  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.37/2.72  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 7.37/2.72  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.37/2.72  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.37/2.72  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.37/2.72  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.37/2.72  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_3347, plain, (![A_360, B_361, D_362]: (r2_relset_1(A_360, B_361, D_362, D_362) | ~m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.37/2.72  tff(c_3360, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_3347])).
% 7.37/2.72  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.37/2.72  tff(c_987, plain, (![A_143, B_144, D_145]: (r2_relset_1(A_143, B_144, D_145, D_145) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.37/2.72  tff(c_1004, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_987])).
% 7.37/2.72  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_174, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.37/2.72  tff(c_194, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_174])).
% 7.37/2.72  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_1119, plain, (![A_163, B_164, C_165]: (k1_relset_1(A_163, B_164, C_165)=k1_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.37/2.72  tff(c_1141, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1119])).
% 7.37/2.72  tff(c_1298, plain, (![B_189, A_190, C_191]: (k1_xboole_0=B_189 | k1_relset_1(A_190, B_189, C_191)=A_190 | ~v1_funct_2(C_191, A_190, B_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.37/2.72  tff(c_1308, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1298])).
% 7.37/2.72  tff(c_1323, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1141, c_1308])).
% 7.37/2.72  tff(c_1328, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1323])).
% 7.37/2.72  tff(c_195, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_174])).
% 7.37/2.72  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_1142, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1119])).
% 7.37/2.72  tff(c_1311, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_1298])).
% 7.37/2.72  tff(c_1326, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1142, c_1311])).
% 7.37/2.72  tff(c_1334, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1326])).
% 7.37/2.72  tff(c_1480, plain, (![A_210, B_211]: (r2_hidden('#skF_3'(A_210, B_211), k1_relat_1(A_210)) | B_211=A_210 | k1_relat_1(B_211)!=k1_relat_1(A_210) | ~v1_funct_1(B_211) | ~v1_relat_1(B_211) | ~v1_funct_1(A_210) | ~v1_relat_1(A_210))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.37/2.72  tff(c_1490, plain, (![B_211]: (r2_hidden('#skF_3'('#skF_6', B_211), '#skF_4') | B_211='#skF_6' | k1_relat_1(B_211)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_211) | ~v1_relat_1(B_211) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1334, c_1480])).
% 7.37/2.72  tff(c_2522, plain, (![B_315]: (r2_hidden('#skF_3'('#skF_6', B_315), '#skF_4') | B_315='#skF_6' | k1_relat_1(B_315)!='#skF_4' | ~v1_funct_1(B_315) | ~v1_relat_1(B_315))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_68, c_1334, c_1490])).
% 7.37/2.72  tff(c_56, plain, (![E_42]: (k1_funct_1('#skF_7', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_2681, plain, (![B_328]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_328))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_328)) | B_328='#skF_6' | k1_relat_1(B_328)!='#skF_4' | ~v1_funct_1(B_328) | ~v1_relat_1(B_328))), inference(resolution, [status(thm)], [c_2522, c_56])).
% 7.37/2.72  tff(c_28, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_3'(A_18, B_22))!=k1_funct_1(A_18, '#skF_3'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.37/2.72  tff(c_2688, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2681, c_28])).
% 7.37/2.72  tff(c_2695, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_62, c_1328, c_195, c_68, c_1334, c_1328, c_2688])).
% 7.37/2.72  tff(c_54, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.72  tff(c_2718, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2695, c_54])).
% 7.37/2.72  tff(c_2729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1004, c_2718])).
% 7.37/2.72  tff(c_2730, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1326])).
% 7.37/2.72  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.37/2.72  tff(c_2758, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2730, c_12])).
% 7.37/2.72  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.37/2.72  tff(c_2755, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2730, c_2730, c_18])).
% 7.37/2.72  tff(c_860, plain, (![C_135, B_136, A_137]: (~v1_xboole_0(C_135) | ~m1_subset_1(B_136, k1_zfmisc_1(C_135)) | ~r2_hidden(A_137, B_136))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.37/2.72  tff(c_876, plain, (![A_137]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_137, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_860])).
% 7.37/2.72  tff(c_878, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_876])).
% 7.37/2.72  tff(c_2932, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2755, c_878])).
% 7.37/2.72  tff(c_2939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2758, c_2932])).
% 7.37/2.72  tff(c_2940, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1323])).
% 7.37/2.72  tff(c_2968, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_12])).
% 7.37/2.72  tff(c_2965, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_2940, c_18])).
% 7.37/2.72  tff(c_3080, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2965, c_878])).
% 7.37/2.72  tff(c_3087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2968, c_3080])).
% 7.37/2.72  tff(c_3090, plain, (![A_348]: (~r2_hidden(A_348, '#skF_7'))), inference(splitRight, [status(thm)], [c_876])).
% 7.37/2.72  tff(c_3100, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_3090])).
% 7.37/2.72  tff(c_3089, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_876])).
% 7.37/2.72  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.37/2.72  tff(c_3109, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_3100, c_14])).
% 7.37/2.72  tff(c_3376, plain, (![A_363]: (A_363='#skF_7' | ~v1_xboole_0(A_363))), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_14])).
% 7.37/2.72  tff(c_3387, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_3089, c_3376])).
% 7.37/2.72  tff(c_3471, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3387, c_64])).
% 7.37/2.72  tff(c_26, plain, (![C_17, B_16, A_15]: (~v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.37/2.72  tff(c_3490, plain, (![A_15]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_15, '#skF_6'))), inference(resolution, [status(thm)], [c_3471, c_26])).
% 7.37/2.72  tff(c_3499, plain, (![A_368]: (~r2_hidden(A_368, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_3490])).
% 7.37/2.72  tff(c_3509, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_3499])).
% 7.37/2.72  tff(c_3117, plain, (![A_10]: (A_10='#skF_7' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_14])).
% 7.37/2.72  tff(c_3516, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_3509, c_3117])).
% 7.37/2.72  tff(c_3536, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3516, c_54])).
% 7.37/2.72  tff(c_3545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3360, c_3536])).
% 7.37/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.72  
% 7.37/2.72  Inference rules
% 7.37/2.72  ----------------------
% 7.37/2.72  #Ref     : 1
% 7.37/2.72  #Sup     : 725
% 7.37/2.72  #Fact    : 0
% 7.37/2.72  #Define  : 0
% 7.37/2.72  #Split   : 11
% 7.37/2.72  #Chain   : 0
% 7.37/2.72  #Close   : 0
% 7.37/2.72  
% 7.37/2.72  Ordering : KBO
% 7.37/2.72  
% 7.37/2.72  Simplification rules
% 7.37/2.72  ----------------------
% 7.37/2.72  #Subsume      : 150
% 7.37/2.72  #Demod        : 761
% 7.37/2.72  #Tautology    : 394
% 7.37/2.72  #SimpNegUnit  : 18
% 7.37/2.72  #BackRed      : 172
% 7.37/2.72  
% 7.37/2.72  #Partial instantiations: 0
% 7.37/2.72  #Strategies tried      : 1
% 7.37/2.72  
% 7.37/2.72  Timing (in seconds)
% 7.37/2.72  ----------------------
% 7.37/2.73  Preprocessing        : 0.52
% 7.37/2.73  Parsing              : 0.27
% 7.37/2.73  CNF conversion       : 0.04
% 7.37/2.73  Main loop            : 1.40
% 7.37/2.73  Inferencing          : 0.48
% 7.37/2.73  Reduction            : 0.49
% 7.37/2.73  Demodulation         : 0.35
% 7.37/2.73  BG Simplification    : 0.05
% 7.37/2.73  Subsumption          : 0.26
% 7.37/2.73  Abstraction          : 0.05
% 7.37/2.73  MUC search           : 0.00
% 7.37/2.73  Cooper               : 0.00
% 7.37/2.73  Total                : 1.98
% 7.37/2.73  Index Insertion      : 0.00
% 7.37/2.73  Index Deletion       : 0.00
% 7.37/2.73  Index Matching       : 0.00
% 7.37/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
