%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:07 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 275 expanded)
%              Number of leaves         :   41 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 838 expanded)
%              Number of equality atoms :   34 (  73 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_148,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_124,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_xboole_0(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_136,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_124])).

tff(c_138,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_44,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_79,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_28,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1(k1_partfun1(A_22,B_23,C_24,D_25,E_26,F_27),k1_zfmisc_1(k2_zfmisc_1(A_22,D_25)))
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(C_24,D_25)))
      | ~ v1_funct_1(F_27)
      | ~ m1_subset_1(E_26,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_1(E_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_348,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r2_relset_1(A_79,B_80,C_78,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_356,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_348])).

tff(c_371,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_356])).

tff(c_814,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_817,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_814])).

tff(c_821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_817])).

tff(c_822,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_855,plain,(
    ! [A_119,E_122,D_121,C_120,B_123] :
      ( k1_xboole_0 = C_120
      | v2_funct_1(D_121)
      | ~ v2_funct_1(k1_partfun1(A_119,B_123,B_123,C_120,D_121,E_122))
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(B_123,C_120)))
      | ~ v1_funct_2(E_122,B_123,C_120)
      | ~ v1_funct_1(E_122)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_123)))
      | ~ v1_funct_2(D_121,A_119,B_123)
      | ~ v1_funct_1(D_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_857,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_855])).

tff(c_859,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_59,c_857])).

tff(c_860,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_859])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_891,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_2])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_891])).

tff(c_895,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_903,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_895,c_4])).

tff(c_894,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_899,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_894,c_4])).

tff(c_911,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_899])).

tff(c_922,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_79])).

tff(c_944,plain,(
    ! [A_128] :
      ( v1_xboole_0(k6_partfun1(A_128))
      | ~ v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_904,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_4])).

tff(c_937,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_904])).

tff(c_949,plain,(
    ! [A_129] :
      ( k6_partfun1(A_129) = '#skF_1'
      | ~ v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_944,c_937])).

tff(c_957,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_895,c_949])).

tff(c_975,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_59])).

tff(c_984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_922,c_975])).

tff(c_985,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_988,plain,(
    ! [C_131,A_132,B_133] :
      ( v1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1000,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_988])).

tff(c_1015,plain,(
    ! [C_137,B_138,A_139] :
      ( v5_relat_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1026,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1015])).

tff(c_1105,plain,(
    ! [A_150,B_151,D_152] :
      ( r2_relset_1(A_150,B_151,D_152,D_152)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1112,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_34,c_1105])).

tff(c_1199,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1214,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1199])).

tff(c_1234,plain,(
    ! [D_159,C_160,A_161,B_162] :
      ( D_159 = C_160
      | ~ r2_relset_1(A_161,B_162,C_160,D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1242,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_1234])).

tff(c_1257,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1242])).

tff(c_1670,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1257])).

tff(c_1673,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1670])).

tff(c_1677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_1673])).

tff(c_1678,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1257])).

tff(c_1913,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k2_relset_1(A_211,B_212,C_213) = B_212
      | ~ r2_relset_1(B_212,B_212,k1_partfun1(B_212,A_211,A_211,B_212,D_214,C_213),k6_partfun1(B_212))
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(B_212,A_211)))
      | ~ v1_funct_2(D_214,B_212,A_211)
      | ~ v1_funct_1(D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212)))
      | ~ v1_funct_2(C_213,A_211,B_212)
      | ~ v1_funct_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1916,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_1913])).

tff(c_1924,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58,c_56,c_54,c_1112,c_1214,c_1916])).

tff(c_24,plain,(
    ! [B_21] :
      ( v2_funct_2(B_21,k2_relat_1(B_21))
      | ~ v5_relat_1(B_21,k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1929,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1924,c_24])).

tff(c_1933,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1026,c_1924,c_1929])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_985,c_1933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.77  
% 4.16/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.77  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.16/1.77  
% 4.16/1.77  %Foreground sorts:
% 4.16/1.77  
% 4.16/1.77  
% 4.16/1.77  %Background operators:
% 4.16/1.77  
% 4.16/1.77  
% 4.16/1.77  %Foreground operators:
% 4.16/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.16/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.16/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.77  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.16/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.77  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.16/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.77  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.16/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.16/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.77  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.16/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.16/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.16/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.77  
% 4.59/1.79  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.59/1.79  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.59/1.79  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.59/1.79  tff(f_34, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.59/1.79  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.59/1.79  tff(f_87, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.59/1.79  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.59/1.79  tff(f_128, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.59/1.79  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.59/1.79  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.59/1.79  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.59/1.79  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.59/1.79  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.59/1.79  tff(f_106, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.59/1.79  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.59/1.79  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_124, plain, (![C_60, A_61, B_62]: (v1_xboole_0(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.59/1.79  tff(c_136, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_124])).
% 4.59/1.79  tff(c_138, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_136])).
% 4.59/1.79  tff(c_44, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_79, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 4.59/1.79  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_36, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.59/1.79  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.59/1.79  tff(c_59, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 4.59/1.79  tff(c_28, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1(k1_partfun1(A_22, B_23, C_24, D_25, E_26, F_27), k1_zfmisc_1(k2_zfmisc_1(A_22, D_25))) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(C_24, D_25))) | ~v1_funct_1(F_27) | ~m1_subset_1(E_26, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_1(E_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.59/1.79  tff(c_34, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.59/1.79  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.79  tff(c_348, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r2_relset_1(A_79, B_80, C_78, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.59/1.79  tff(c_356, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_348])).
% 4.59/1.79  tff(c_371, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_356])).
% 4.59/1.79  tff(c_814, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_371])).
% 4.59/1.79  tff(c_817, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_814])).
% 4.59/1.79  tff(c_821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_817])).
% 4.59/1.79  tff(c_822, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_371])).
% 4.59/1.79  tff(c_855, plain, (![A_119, E_122, D_121, C_120, B_123]: (k1_xboole_0=C_120 | v2_funct_1(D_121) | ~v2_funct_1(k1_partfun1(A_119, B_123, B_123, C_120, D_121, E_122)) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(B_123, C_120))) | ~v1_funct_2(E_122, B_123, C_120) | ~v1_funct_1(E_122) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_123))) | ~v1_funct_2(D_121, A_119, B_123) | ~v1_funct_1(D_121))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.59/1.79  tff(c_857, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_822, c_855])).
% 4.59/1.79  tff(c_859, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_48, c_59, c_857])).
% 4.59/1.79  tff(c_860, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_859])).
% 4.59/1.79  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.59/1.79  tff(c_891, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_2])).
% 4.59/1.79  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_891])).
% 4.59/1.79  tff(c_895, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_136])).
% 4.59/1.79  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.59/1.79  tff(c_903, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_895, c_4])).
% 4.59/1.79  tff(c_894, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_136])).
% 4.59/1.79  tff(c_899, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_894, c_4])).
% 4.59/1.79  tff(c_911, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_903, c_899])).
% 4.59/1.79  tff(c_922, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_911, c_79])).
% 4.59/1.79  tff(c_944, plain, (![A_128]: (v1_xboole_0(k6_partfun1(A_128)) | ~v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_34, c_124])).
% 4.59/1.79  tff(c_904, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_4])).
% 4.59/1.79  tff(c_937, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_911, c_904])).
% 4.59/1.79  tff(c_949, plain, (![A_129]: (k6_partfun1(A_129)='#skF_1' | ~v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_944, c_937])).
% 4.59/1.79  tff(c_957, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_895, c_949])).
% 4.59/1.79  tff(c_975, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_957, c_59])).
% 4.59/1.79  tff(c_984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_922, c_975])).
% 4.59/1.79  tff(c_985, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.59/1.79  tff(c_988, plain, (![C_131, A_132, B_133]: (v1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.59/1.79  tff(c_1000, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_988])).
% 4.59/1.79  tff(c_1015, plain, (![C_137, B_138, A_139]: (v5_relat_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.59/1.79  tff(c_1026, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1015])).
% 4.59/1.79  tff(c_1105, plain, (![A_150, B_151, D_152]: (r2_relset_1(A_150, B_151, D_152, D_152) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.59/1.79  tff(c_1112, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_34, c_1105])).
% 4.59/1.79  tff(c_1199, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.59/1.79  tff(c_1214, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1199])).
% 4.59/1.79  tff(c_1234, plain, (![D_159, C_160, A_161, B_162]: (D_159=C_160 | ~r2_relset_1(A_161, B_162, C_160, D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.59/1.79  tff(c_1242, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_1234])).
% 4.59/1.79  tff(c_1257, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1242])).
% 4.59/1.79  tff(c_1670, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1257])).
% 4.59/1.79  tff(c_1673, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1670])).
% 4.59/1.79  tff(c_1677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_1673])).
% 4.59/1.79  tff(c_1678, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1257])).
% 4.59/1.79  tff(c_1913, plain, (![A_211, B_212, C_213, D_214]: (k2_relset_1(A_211, B_212, C_213)=B_212 | ~r2_relset_1(B_212, B_212, k1_partfun1(B_212, A_211, A_211, B_212, D_214, C_213), k6_partfun1(B_212)) | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(B_212, A_211))) | ~v1_funct_2(D_214, B_212, A_211) | ~v1_funct_1(D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))) | ~v1_funct_2(C_213, A_211, B_212) | ~v1_funct_1(C_213))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.59/1.79  tff(c_1916, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1678, c_1913])).
% 4.59/1.79  tff(c_1924, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58, c_56, c_54, c_1112, c_1214, c_1916])).
% 4.59/1.79  tff(c_24, plain, (![B_21]: (v2_funct_2(B_21, k2_relat_1(B_21)) | ~v5_relat_1(B_21, k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.59/1.79  tff(c_1929, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1924, c_24])).
% 4.59/1.79  tff(c_1933, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1026, c_1924, c_1929])).
% 4.59/1.79  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_985, c_1933])).
% 4.59/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.79  
% 4.59/1.79  Inference rules
% 4.59/1.79  ----------------------
% 4.59/1.79  #Ref     : 0
% 4.59/1.79  #Sup     : 430
% 4.59/1.79  #Fact    : 0
% 4.59/1.79  #Define  : 0
% 4.59/1.79  #Split   : 14
% 4.59/1.79  #Chain   : 0
% 4.59/1.79  #Close   : 0
% 4.59/1.79  
% 4.59/1.79  Ordering : KBO
% 4.59/1.79  
% 4.59/1.79  Simplification rules
% 4.59/1.79  ----------------------
% 4.59/1.79  #Subsume      : 56
% 4.59/1.79  #Demod        : 456
% 4.59/1.79  #Tautology    : 195
% 4.59/1.79  #SimpNegUnit  : 4
% 4.59/1.79  #BackRed      : 48
% 4.59/1.79  
% 4.59/1.79  #Partial instantiations: 0
% 4.59/1.79  #Strategies tried      : 1
% 4.59/1.79  
% 4.59/1.79  Timing (in seconds)
% 4.59/1.80  ----------------------
% 4.59/1.80  Preprocessing        : 0.35
% 4.59/1.80  Parsing              : 0.19
% 4.59/1.80  CNF conversion       : 0.02
% 4.59/1.80  Main loop            : 0.69
% 4.59/1.80  Inferencing          : 0.25
% 4.59/1.80  Reduction            : 0.24
% 4.59/1.80  Demodulation         : 0.17
% 4.59/1.80  BG Simplification    : 0.03
% 4.59/1.80  Subsumption          : 0.12
% 4.59/1.80  Abstraction          : 0.03
% 4.59/1.80  MUC search           : 0.00
% 4.59/1.80  Cooper               : 0.00
% 4.59/1.80  Total                : 1.09
% 4.59/1.80  Index Insertion      : 0.00
% 4.59/1.80  Index Deletion       : 0.00
% 4.59/1.80  Index Matching       : 0.00
% 4.59/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
