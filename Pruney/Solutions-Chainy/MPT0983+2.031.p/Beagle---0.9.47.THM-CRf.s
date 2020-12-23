%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:05 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 326 expanded)
%              Number of leaves         :   42 ( 136 expanded)
%              Depth                    :   10
%              Number of atoms          :  203 (1002 expanded)
%              Number of equality atoms :   38 ( 108 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_116,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_40,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_64,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_36,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_63,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_343,plain,(
    ! [D_82,C_83,A_84,B_85] :
      ( D_82 = C_83
      | ~ r2_relset_1(A_84,B_85,C_83,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_349,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_343])).

tff(c_360,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_349])).

tff(c_388,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_594,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_388])).

tff(c_598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_594])).

tff(c_599,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_882,plain,(
    ! [D_173,B_172,E_174,A_171,C_175] :
      ( k1_xboole_0 = C_175
      | v2_funct_1(D_173)
      | ~ v2_funct_1(k1_partfun1(A_171,B_172,B_172,C_175,D_173,E_174))
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(B_172,C_175)))
      | ~ v1_funct_2(E_174,B_172,C_175)
      | ~ v1_funct_1(E_174)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(D_173,A_171,B_172)
      | ~ v1_funct_1(D_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_884,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_882])).

tff(c_886,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_64,c_884])).

tff(c_887,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_886])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_916,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_2])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_913,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_887,c_10])).

tff(c_175,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_193,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_175])).

tff(c_195,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_1019,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_195])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_1019])).

tff(c_1024,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_117,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | B_48 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_120,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_1031,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1024,c_120])).

tff(c_94,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_14])).

tff(c_111,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_64])).

tff(c_1056,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_111])).

tff(c_1064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_1056])).

tff(c_1065,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1092,plain,(
    ! [C_192,A_193,B_194] :
      ( v1_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1107,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1092])).

tff(c_1184,plain,(
    ! [C_205,B_206,A_207] :
      ( v5_relat_1(C_205,B_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1201,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1184])).

tff(c_1245,plain,(
    ! [A_216,B_217,D_218] :
      ( r2_relset_1(A_216,B_217,D_218,D_218)
      | ~ m1_subset_1(D_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1256,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_63,c_1245])).

tff(c_1263,plain,(
    ! [A_221,B_222,C_223] :
      ( k2_relset_1(A_221,B_222,C_223) = k2_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1280,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1263])).

tff(c_1475,plain,(
    ! [B_259,F_258,A_256,D_255,E_260,C_257] :
      ( m1_subset_1(k1_partfun1(A_256,B_259,C_257,D_255,E_260,F_258),k1_zfmisc_1(k2_zfmisc_1(A_256,D_255)))
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(C_257,D_255)))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(A_256,B_259)))
      | ~ v1_funct_1(E_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1321,plain,(
    ! [D_227,C_228,A_229,B_230] :
      ( D_227 = C_228
      | ~ r2_relset_1(A_229,B_230,C_228,D_227)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1331,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_1321])).

tff(c_1350,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1331])).

tff(c_1373,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1350])).

tff(c_1478,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1475,c_1373])).

tff(c_1510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_1478])).

tff(c_1511,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1350])).

tff(c_1955,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( k2_relset_1(A_384,B_385,C_386) = B_385
      | ~ r2_relset_1(B_385,B_385,k1_partfun1(B_385,A_384,A_384,B_385,D_387,C_386),k6_partfun1(B_385))
      | ~ m1_subset_1(D_387,k1_zfmisc_1(k2_zfmisc_1(B_385,A_384)))
      | ~ v1_funct_2(D_387,B_385,A_384)
      | ~ v1_funct_1(D_387)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ v1_funct_2(C_386,A_384,B_385)
      | ~ v1_funct_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1958,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1511,c_1955])).

tff(c_1963,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_1256,c_1280,c_1958])).

tff(c_32,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1969,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_32])).

tff(c_1973,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1201,c_1963,c_1969])).

tff(c_1975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_1973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  
% 4.55/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.55/1.80  
% 4.55/1.80  %Foreground sorts:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Background operators:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Foreground operators:
% 4.55/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.55/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.80  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.55/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/1.80  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.80  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.55/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.55/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.80  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.80  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.55/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.55/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.80  
% 4.80/1.82  tff(f_155, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.80/1.82  tff(f_96, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.80/1.82  tff(f_50, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.80/1.82  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.80/1.82  tff(f_74, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.80/1.82  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.80/1.82  tff(f_135, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.80/1.82  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.80/1.82  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.80/1.82  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.80/1.82  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.80/1.82  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.80/1.82  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.80/1.82  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.80/1.82  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.80/1.82  tff(f_113, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.80/1.82  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.80/1.82  tff(c_48, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_116, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 4.80/1.82  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_40, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.80/1.82  tff(c_16, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.80/1.82  tff(c_64, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 4.80/1.82  tff(c_36, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.80/1.82  tff(c_30, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.80/1.82  tff(c_63, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 4.80/1.82  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.80/1.82  tff(c_343, plain, (![D_82, C_83, A_84, B_85]: (D_82=C_83 | ~r2_relset_1(A_84, B_85, C_83, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.80/1.82  tff(c_349, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_343])).
% 4.80/1.82  tff(c_360, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_349])).
% 4.80/1.82  tff(c_388, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_360])).
% 4.80/1.82  tff(c_594, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_388])).
% 4.80/1.82  tff(c_598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_594])).
% 4.80/1.82  tff(c_599, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_360])).
% 4.80/1.82  tff(c_882, plain, (![D_173, B_172, E_174, A_171, C_175]: (k1_xboole_0=C_175 | v2_funct_1(D_173) | ~v2_funct_1(k1_partfun1(A_171, B_172, B_172, C_175, D_173, E_174)) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(B_172, C_175))) | ~v1_funct_2(E_174, B_172, C_175) | ~v1_funct_1(E_174) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(D_173, A_171, B_172) | ~v1_funct_1(D_173))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.80/1.82  tff(c_884, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_599, c_882])).
% 4.80/1.82  tff(c_886, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_64, c_884])).
% 4.80/1.82  tff(c_887, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_116, c_886])).
% 4.80/1.82  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.80/1.82  tff(c_916, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_887, c_2])).
% 4.80/1.82  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.80/1.82  tff(c_913, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_887, c_887, c_10])).
% 4.80/1.82  tff(c_175, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/1.82  tff(c_193, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_175])).
% 4.80/1.82  tff(c_195, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_193])).
% 4.80/1.82  tff(c_1019, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_913, c_195])).
% 4.80/1.82  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_916, c_1019])).
% 4.80/1.82  tff(c_1024, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_193])).
% 4.80/1.82  tff(c_117, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | B_48=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.80/1.82  tff(c_120, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_2, c_117])).
% 4.80/1.82  tff(c_1031, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1024, c_120])).
% 4.80/1.82  tff(c_94, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.80/1.82  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.80/1.82  tff(c_100, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_14])).
% 4.80/1.82  tff(c_111, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_64])).
% 4.80/1.82  tff(c_1056, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_111])).
% 4.80/1.82  tff(c_1064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_1056])).
% 4.80/1.82  tff(c_1065, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.80/1.82  tff(c_1092, plain, (![C_192, A_193, B_194]: (v1_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.80/1.82  tff(c_1107, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1092])).
% 4.80/1.82  tff(c_1184, plain, (![C_205, B_206, A_207]: (v5_relat_1(C_205, B_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.80/1.82  tff(c_1201, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_1184])).
% 4.80/1.82  tff(c_1245, plain, (![A_216, B_217, D_218]: (r2_relset_1(A_216, B_217, D_218, D_218) | ~m1_subset_1(D_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.80/1.82  tff(c_1256, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_63, c_1245])).
% 4.80/1.82  tff(c_1263, plain, (![A_221, B_222, C_223]: (k2_relset_1(A_221, B_222, C_223)=k2_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.80/1.82  tff(c_1280, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1263])).
% 4.80/1.82  tff(c_1475, plain, (![B_259, F_258, A_256, D_255, E_260, C_257]: (m1_subset_1(k1_partfun1(A_256, B_259, C_257, D_255, E_260, F_258), k1_zfmisc_1(k2_zfmisc_1(A_256, D_255))) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(C_257, D_255))) | ~v1_funct_1(F_258) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(A_256, B_259))) | ~v1_funct_1(E_260))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.80/1.82  tff(c_1321, plain, (![D_227, C_228, A_229, B_230]: (D_227=C_228 | ~r2_relset_1(A_229, B_230, C_228, D_227) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.80/1.82  tff(c_1331, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_1321])).
% 4.80/1.82  tff(c_1350, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1331])).
% 4.80/1.82  tff(c_1373, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1350])).
% 4.80/1.82  tff(c_1478, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1475, c_1373])).
% 4.80/1.82  tff(c_1510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_1478])).
% 4.80/1.82  tff(c_1511, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1350])).
% 4.80/1.82  tff(c_1955, plain, (![A_384, B_385, C_386, D_387]: (k2_relset_1(A_384, B_385, C_386)=B_385 | ~r2_relset_1(B_385, B_385, k1_partfun1(B_385, A_384, A_384, B_385, D_387, C_386), k6_partfun1(B_385)) | ~m1_subset_1(D_387, k1_zfmisc_1(k2_zfmisc_1(B_385, A_384))) | ~v1_funct_2(D_387, B_385, A_384) | ~v1_funct_1(D_387) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~v1_funct_2(C_386, A_384, B_385) | ~v1_funct_1(C_386))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.80/1.82  tff(c_1958, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1511, c_1955])).
% 4.80/1.82  tff(c_1963, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_1256, c_1280, c_1958])).
% 4.80/1.82  tff(c_32, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.80/1.82  tff(c_1969, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1963, c_32])).
% 4.80/1.82  tff(c_1973, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1201, c_1963, c_1969])).
% 4.80/1.82  tff(c_1975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1065, c_1973])).
% 4.80/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.82  
% 4.80/1.82  Inference rules
% 4.80/1.82  ----------------------
% 4.80/1.82  #Ref     : 0
% 4.80/1.82  #Sup     : 431
% 4.80/1.82  #Fact    : 0
% 4.80/1.82  #Define  : 0
% 4.80/1.82  #Split   : 15
% 4.80/1.82  #Chain   : 0
% 4.80/1.82  #Close   : 0
% 4.80/1.82  
% 4.80/1.82  Ordering : KBO
% 4.80/1.82  
% 4.80/1.82  Simplification rules
% 4.80/1.82  ----------------------
% 4.80/1.82  #Subsume      : 28
% 4.80/1.82  #Demod        : 379
% 4.80/1.82  #Tautology    : 143
% 4.80/1.82  #SimpNegUnit  : 5
% 4.80/1.82  #BackRed      : 77
% 4.80/1.82  
% 4.80/1.82  #Partial instantiations: 0
% 4.80/1.82  #Strategies tried      : 1
% 4.80/1.82  
% 4.80/1.82  Timing (in seconds)
% 4.80/1.82  ----------------------
% 4.80/1.83  Preprocessing        : 0.36
% 4.80/1.83  Parsing              : 0.19
% 4.80/1.83  CNF conversion       : 0.03
% 4.80/1.83  Main loop            : 0.69
% 4.80/1.83  Inferencing          : 0.25
% 4.80/1.83  Reduction            : 0.23
% 4.80/1.83  Demodulation         : 0.17
% 4.80/1.83  BG Simplification    : 0.03
% 4.80/1.83  Subsumption          : 0.11
% 4.80/1.83  Abstraction          : 0.03
% 4.80/1.83  MUC search           : 0.00
% 4.80/1.83  Cooper               : 0.00
% 4.80/1.83  Total                : 1.09
% 4.80/1.83  Index Insertion      : 0.00
% 4.80/1.83  Index Deletion       : 0.00
% 4.80/1.83  Index Matching       : 0.00
% 4.80/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
