%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:42 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  175 (23989 expanded)
%              Number of leaves         :   48 (8343 expanded)
%              Depth                    :   26
%              Number of atoms          :  450 (68656 expanded)
%              Number of equality atoms :   92 (14844 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_159,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_62,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_179,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_75,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_83,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_75])).

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_82,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_109,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_82,c_62])).

tff(c_115,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_118,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_109,c_115])).

tff(c_121,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_118])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_122,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_126,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_109,c_122])).

tff(c_169,plain,(
    ! [B_59,A_60] :
      ( k1_relat_1(B_59) = A_60
      | ~ v1_partfun1(B_59,A_60)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_172,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_169])).

tff(c_175,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_172])).

tff(c_176,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_192,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_196,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_192])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_110,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_82,c_60])).

tff(c_197,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_110])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_64])).

tff(c_93,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_84])).

tff(c_207,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_93])).

tff(c_205,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_109])).

tff(c_273,plain,(
    ! [B_69,C_70,A_71] :
      ( k1_xboole_0 = B_69
      | v1_partfun1(C_70,A_71)
      | ~ v1_funct_2(C_70,A_71,B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_69)))
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_276,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_205,c_273])).

tff(c_279,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_207,c_276])).

tff(c_280,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_279])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_95,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_95])).

tff(c_105,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_101])).

tff(c_106,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_105])).

tff(c_206,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_106])).

tff(c_286,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_206])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_286])).

tff(c_291,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_296,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_109])).

tff(c_362,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_366,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_296,c_362])).

tff(c_295,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_110])).

tff(c_367,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_295])).

tff(c_298,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_93])).

tff(c_375,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_298])).

tff(c_374,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_296])).

tff(c_699,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( r2_funct_2(A_110,B_111,C_112,C_112)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_2(D_113,A_110,B_111)
      | ~ v1_funct_1(D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_2(C_112,A_110,B_111)
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_703,plain,(
    ! [C_112] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_112,C_112)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_112,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_374,c_699])).

tff(c_834,plain,(
    ! [C_123] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_123,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_123,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_703])).

tff(c_839,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_834])).

tff(c_843,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_839])).

tff(c_26,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_372,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_366])).

tff(c_486,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_funct_1(k2_funct_1(C_89))
      | k2_relset_1(A_90,B_91,C_89) != B_91
      | ~ v2_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_2(C_89,A_90,B_91)
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_489,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_486])).

tff(c_492,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_58,c_372,c_489])).

tff(c_599,plain,(
    ! [C_96,B_97,A_98] :
      ( v1_funct_2(k2_funct_1(C_96),B_97,A_98)
      | k2_relset_1(A_98,B_97,C_96) != B_97
      | ~ v2_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97)))
      | ~ v1_funct_2(C_96,A_98,B_97)
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_602,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_599])).

tff(c_605,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_58,c_372,c_602])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_645,plain,(
    ! [C_104,B_105,A_106] :
      ( m1_subset_1(k2_funct_1(C_104),k1_zfmisc_1(k2_zfmisc_1(B_105,A_106)))
      | k2_relset_1(A_106,B_105,C_104) != B_105
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_104,A_106,B_105)
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_673,plain,(
    ! [C_104,B_105,A_106] :
      ( v1_relat_1(k2_funct_1(C_104))
      | ~ v1_relat_1(k2_zfmisc_1(B_105,A_106))
      | k2_relset_1(A_106,B_105,C_104) != B_105
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_104,A_106,B_105)
      | ~ v1_funct_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_645,c_4])).

tff(c_688,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(k2_funct_1(C_107))
      | k2_relset_1(A_108,B_109,C_107) != B_109
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_673])).

tff(c_694,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_688])).

tff(c_698,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_58,c_372,c_694])).

tff(c_30,plain,(
    ! [C_16,A_14,B_15] :
      ( v4_relat_1(C_16,A_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_719,plain,(
    ! [C_117,B_118,A_119] :
      ( v4_relat_1(k2_funct_1(C_117),B_118)
      | k2_relset_1(A_119,B_118,C_117) != B_118
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118)))
      | ~ v1_funct_2(C_117,A_119,B_118)
      | ~ v1_funct_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_645,c_30])).

tff(c_725,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_719])).

tff(c_729,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_58,c_372,c_725])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_327,plain,(
    ! [A_72] :
      ( k1_relat_1(k2_funct_1(A_72)) = k2_relat_1(A_72)
      | ~ v2_funct_1(A_72)
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [B_21] :
      ( v1_partfun1(B_21,k1_relat_1(B_21))
      | ~ v4_relat_1(B_21,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_476,plain,(
    ! [A_88] :
      ( v1_partfun1(k2_funct_1(A_88),k1_relat_1(k2_funct_1(A_88)))
      | ~ v4_relat_1(k2_funct_1(A_88),k2_relat_1(A_88))
      | ~ v1_relat_1(k2_funct_1(A_88))
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_34])).

tff(c_479,plain,(
    ! [A_11] :
      ( v1_partfun1(k2_funct_1(A_11),k2_relat_1(A_11))
      | ~ v4_relat_1(k2_funct_1(A_11),k2_relat_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_476])).

tff(c_732,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_729,c_479])).

tff(c_738,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_58,c_698,c_732])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(B_21) = A_20
      | ~ v1_partfun1(B_21,A_20)
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_735,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_729,c_36])).

tff(c_741,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_735])).

tff(c_743,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_741])).

tff(c_16,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_450,plain,(
    ! [A_83,B_84] :
      ( v2_funct_1(A_83)
      | k2_relat_1(B_84) != k1_relat_1(A_83)
      | ~ v2_funct_1(k5_relat_1(B_84,A_83))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_456,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k1_relat_1(k2_funct_1(A_12)) != k2_relat_1(A_12)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_12)))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_450])).

tff(c_460,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | k1_relat_1(k2_funct_1(A_12)) != k2_relat_1(A_12)
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_456])).

tff(c_393,plain,(
    ! [A_76] :
      ( k5_relat_1(A_76,k2_funct_1(A_76)) = k6_relat_1(k1_relat_1(A_76))
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_402,plain,(
    ! [A_13] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_13))) = k5_relat_1(k2_funct_1(A_13),A_13)
      | ~ v2_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_393])).

tff(c_747,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_402])).

tff(c_763,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_58,c_698,c_492,c_747])).

tff(c_775,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_778,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_460,c_775])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_58,c_698,c_492,c_743,c_778])).

tff(c_787,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_788,plain,(
    ! [B_120,A_121,C_122] :
      ( k2_relset_1(B_120,A_121,k2_funct_1(C_122)) = k2_relat_1(k2_funct_1(C_122))
      | k2_relset_1(A_121,B_120,C_122) != B_120
      | ~ v2_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120)))
      | ~ v1_funct_2(C_122,A_121,B_120)
      | ~ v1_funct_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_645,c_32])).

tff(c_794,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_788])).

tff(c_798,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_58,c_372,c_794])).

tff(c_48,plain,(
    ! [C_31,A_29,B_30] :
      ( v1_funct_1(k2_funct_1(C_31))
      | k2_relset_1(A_29,B_30,C_31) != B_30
      | ~ v2_funct_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1109,plain,(
    ! [C_141,B_142,A_143] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_141)))
      | k2_relset_1(B_142,A_143,k2_funct_1(C_141)) != A_143
      | ~ v2_funct_1(k2_funct_1(C_141))
      | ~ v1_funct_2(k2_funct_1(C_141),B_142,A_143)
      | ~ v1_funct_1(k2_funct_1(C_141))
      | k2_relset_1(A_143,B_142,C_141) != B_142
      | ~ v2_funct_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142)))
      | ~ v1_funct_2(C_141,A_143,B_142)
      | ~ v1_funct_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_645,c_48])).

tff(c_1115,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_1109])).

tff(c_1119,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_58,c_372,c_492,c_605,c_787,c_798,c_1115])).

tff(c_1120,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1119])).

tff(c_1123,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1120])).

tff(c_1127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_58,c_1123])).

tff(c_1129,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1119])).

tff(c_1135,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_798])).

tff(c_54,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_tops_2(A_34,B_35,C_36) = k2_funct_1(C_36)
      | ~ v2_funct_1(C_36)
      | k2_relset_1(A_34,B_35,C_36) != B_35
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1417,plain,(
    ! [B_152,A_153,C_154] :
      ( k2_tops_2(B_152,A_153,k2_funct_1(C_154)) = k2_funct_1(k2_funct_1(C_154))
      | ~ v2_funct_1(k2_funct_1(C_154))
      | k2_relset_1(B_152,A_153,k2_funct_1(C_154)) != A_153
      | ~ v1_funct_2(k2_funct_1(C_154),B_152,A_153)
      | ~ v1_funct_1(k2_funct_1(C_154))
      | k2_relset_1(A_153,B_152,C_154) != B_152
      | ~ v2_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152)))
      | ~ v1_funct_2(C_154,A_153,B_152)
      | ~ v1_funct_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_645,c_54])).

tff(c_1423,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_1417])).

tff(c_1427,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_58,c_372,c_492,c_605,c_1135,c_787,c_1423])).

tff(c_626,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_tops_2(A_100,B_101,C_102) = k2_funct_1(C_102)
      | ~ v2_funct_1(C_102)
      | k2_relset_1(A_100,B_101,C_102) != B_101
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_629,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_626])).

tff(c_632,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_372,c_58,c_629])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_156,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_83,c_82,c_82,c_82,c_56])).

tff(c_293,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_291,c_291,c_156])).

tff(c_373,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_367,c_367,c_293])).

tff(c_633,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_373])).

tff(c_1438,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_633])).

tff(c_1445,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1438])).

tff(c_1448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_58,c_843,c_1445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:13:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.81  
% 4.70/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.81  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.70/1.81  
% 4.70/1.81  %Foreground sorts:
% 4.70/1.81  
% 4.70/1.81  
% 4.70/1.81  %Background operators:
% 4.70/1.81  
% 4.70/1.81  
% 4.70/1.81  %Foreground operators:
% 4.70/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.70/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.70/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.70/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.70/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.70/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.70/1.81  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.70/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.70/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.70/1.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.70/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.70/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.70/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.70/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.70/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.70/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.70/1.82  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.70/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.82  
% 4.76/1.84  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.76/1.84  tff(f_201, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 4.76/1.84  tff(f_159, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.76/1.84  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.76/1.84  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.76/1.84  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.76/1.84  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.76/1.84  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.76/1.84  tff(f_139, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 4.76/1.84  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.76/1.84  tff(f_122, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.76/1.84  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.76/1.84  tff(f_155, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.76/1.84  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.76/1.84  tff(f_62, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.76/1.84  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.76/1.84  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.76/1.84  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.76/1.84  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.76/1.84  tff(c_72, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_75, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.76/1.84  tff(c_83, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_75])).
% 4.76/1.84  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_82, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_75])).
% 4.76/1.84  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_109, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_82, c_62])).
% 4.76/1.84  tff(c_115, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.84  tff(c_118, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_109, c_115])).
% 4.76/1.84  tff(c_121, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_118])).
% 4.76/1.84  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.76/1.84  tff(c_122, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.76/1.84  tff(c_126, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_109, c_122])).
% 4.76/1.84  tff(c_169, plain, (![B_59, A_60]: (k1_relat_1(B_59)=A_60 | ~v1_partfun1(B_59, A_60) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.76/1.84  tff(c_172, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_169])).
% 4.76/1.84  tff(c_175, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_172])).
% 4.76/1.84  tff(c_176, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_175])).
% 4.76/1.84  tff(c_192, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.76/1.84  tff(c_196, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_192])).
% 4.76/1.84  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_110, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_82, c_60])).
% 4.76/1.84  tff(c_197, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_110])).
% 4.76/1.84  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_84, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_64])).
% 4.76/1.84  tff(c_93, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_84])).
% 4.76/1.84  tff(c_207, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_93])).
% 4.76/1.84  tff(c_205, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_109])).
% 4.76/1.84  tff(c_273, plain, (![B_69, C_70, A_71]: (k1_xboole_0=B_69 | v1_partfun1(C_70, A_71) | ~v1_funct_2(C_70, A_71, B_69) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_69))) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.76/1.84  tff(c_276, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_205, c_273])).
% 4.76/1.84  tff(c_279, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_207, c_276])).
% 4.76/1.84  tff(c_280, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_176, c_279])).
% 4.76/1.84  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_95, plain, (![A_46]: (~v1_xboole_0(u1_struct_0(A_46)) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.76/1.84  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_82, c_95])).
% 4.76/1.84  tff(c_105, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_101])).
% 4.76/1.84  tff(c_106, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_105])).
% 4.76/1.84  tff(c_206, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_106])).
% 4.76/1.84  tff(c_286, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_206])).
% 4.76/1.84  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_286])).
% 4.76/1.84  tff(c_291, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_175])).
% 4.76/1.84  tff(c_296, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_109])).
% 4.76/1.84  tff(c_362, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.76/1.84  tff(c_366, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_296, c_362])).
% 4.76/1.84  tff(c_295, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_110])).
% 4.76/1.84  tff(c_367, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_295])).
% 4.76/1.84  tff(c_298, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_93])).
% 4.76/1.84  tff(c_375, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_298])).
% 4.76/1.84  tff(c_374, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_296])).
% 4.76/1.84  tff(c_699, plain, (![A_110, B_111, C_112, D_113]: (r2_funct_2(A_110, B_111, C_112, C_112) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_2(D_113, A_110, B_111) | ~v1_funct_1(D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_2(C_112, A_110, B_111) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.76/1.84  tff(c_703, plain, (![C_112]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_112, C_112) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_112, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_112))), inference(resolution, [status(thm)], [c_374, c_699])).
% 4.76/1.84  tff(c_834, plain, (![C_123]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_123, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_123, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_123))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_703])).
% 4.76/1.84  tff(c_839, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_834])).
% 4.76/1.84  tff(c_843, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_839])).
% 4.76/1.84  tff(c_26, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.76/1.84  tff(c_372, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_366])).
% 4.76/1.84  tff(c_486, plain, (![C_89, A_90, B_91]: (v1_funct_1(k2_funct_1(C_89)) | k2_relset_1(A_90, B_91, C_89)!=B_91 | ~v2_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_2(C_89, A_90, B_91) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.76/1.84  tff(c_489, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_486])).
% 4.76/1.84  tff(c_492, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_58, c_372, c_489])).
% 4.76/1.84  tff(c_599, plain, (![C_96, B_97, A_98]: (v1_funct_2(k2_funct_1(C_96), B_97, A_98) | k2_relset_1(A_98, B_97, C_96)!=B_97 | ~v2_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))) | ~v1_funct_2(C_96, A_98, B_97) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.76/1.84  tff(c_602, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_599])).
% 4.76/1.84  tff(c_605, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_58, c_372, c_602])).
% 4.76/1.84  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.76/1.84  tff(c_645, plain, (![C_104, B_105, A_106]: (m1_subset_1(k2_funct_1(C_104), k1_zfmisc_1(k2_zfmisc_1(B_105, A_106))) | k2_relset_1(A_106, B_105, C_104)!=B_105 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_104, A_106, B_105) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.76/1.84  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.84  tff(c_673, plain, (![C_104, B_105, A_106]: (v1_relat_1(k2_funct_1(C_104)) | ~v1_relat_1(k2_zfmisc_1(B_105, A_106)) | k2_relset_1(A_106, B_105, C_104)!=B_105 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_104, A_106, B_105) | ~v1_funct_1(C_104))), inference(resolution, [status(thm)], [c_645, c_4])).
% 4.76/1.84  tff(c_688, plain, (![C_107, A_108, B_109]: (v1_relat_1(k2_funct_1(C_107)) | k2_relset_1(A_108, B_109, C_107)!=B_109 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_673])).
% 4.76/1.84  tff(c_694, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_688])).
% 4.76/1.84  tff(c_698, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_58, c_372, c_694])).
% 4.76/1.84  tff(c_30, plain, (![C_16, A_14, B_15]: (v4_relat_1(C_16, A_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.76/1.84  tff(c_719, plain, (![C_117, B_118, A_119]: (v4_relat_1(k2_funct_1(C_117), B_118) | k2_relset_1(A_119, B_118, C_117)!=B_118 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))) | ~v1_funct_2(C_117, A_119, B_118) | ~v1_funct_1(C_117))), inference(resolution, [status(thm)], [c_645, c_30])).
% 4.76/1.84  tff(c_725, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_719])).
% 4.76/1.84  tff(c_729, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_58, c_372, c_725])).
% 4.76/1.84  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.76/1.84  tff(c_327, plain, (![A_72]: (k1_relat_1(k2_funct_1(A_72))=k2_relat_1(A_72) | ~v2_funct_1(A_72) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.76/1.84  tff(c_34, plain, (![B_21]: (v1_partfun1(B_21, k1_relat_1(B_21)) | ~v4_relat_1(B_21, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.76/1.84  tff(c_476, plain, (![A_88]: (v1_partfun1(k2_funct_1(A_88), k1_relat_1(k2_funct_1(A_88))) | ~v4_relat_1(k2_funct_1(A_88), k2_relat_1(A_88)) | ~v1_relat_1(k2_funct_1(A_88)) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_327, c_34])).
% 4.76/1.84  tff(c_479, plain, (![A_11]: (v1_partfun1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v4_relat_1(k2_funct_1(A_11), k2_relat_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_476])).
% 4.76/1.84  tff(c_732, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_729, c_479])).
% 4.76/1.84  tff(c_738, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_58, c_698, c_732])).
% 4.76/1.84  tff(c_36, plain, (![B_21, A_20]: (k1_relat_1(B_21)=A_20 | ~v1_partfun1(B_21, A_20) | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.76/1.84  tff(c_735, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_729, c_36])).
% 4.76/1.84  tff(c_741, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_735])).
% 4.76/1.84  tff(c_743, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_741])).
% 4.76/1.84  tff(c_16, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.76/1.84  tff(c_24, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.76/1.84  tff(c_450, plain, (![A_83, B_84]: (v2_funct_1(A_83) | k2_relat_1(B_84)!=k1_relat_1(A_83) | ~v2_funct_1(k5_relat_1(B_84, A_83)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.76/1.84  tff(c_456, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_12))) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_450])).
% 4.76/1.84  tff(c_460, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | k1_relat_1(k2_funct_1(A_12))!=k2_relat_1(A_12) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_456])).
% 4.76/1.84  tff(c_393, plain, (![A_76]: (k5_relat_1(A_76, k2_funct_1(A_76))=k6_relat_1(k1_relat_1(A_76)) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.76/1.84  tff(c_402, plain, (![A_13]: (k6_relat_1(k1_relat_1(k2_funct_1(A_13)))=k5_relat_1(k2_funct_1(A_13), A_13) | ~v2_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_393])).
% 4.76/1.84  tff(c_747, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_743, c_402])).
% 4.76/1.84  tff(c_763, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_58, c_698, c_492, c_747])).
% 4.76/1.84  tff(c_775, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_763])).
% 4.76/1.84  tff(c_778, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_460, c_775])).
% 4.76/1.84  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_58, c_698, c_492, c_743, c_778])).
% 4.76/1.84  tff(c_787, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_763])).
% 4.76/1.84  tff(c_32, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.76/1.84  tff(c_788, plain, (![B_120, A_121, C_122]: (k2_relset_1(B_120, A_121, k2_funct_1(C_122))=k2_relat_1(k2_funct_1(C_122)) | k2_relset_1(A_121, B_120, C_122)!=B_120 | ~v2_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))) | ~v1_funct_2(C_122, A_121, B_120) | ~v1_funct_1(C_122))), inference(resolution, [status(thm)], [c_645, c_32])).
% 4.76/1.84  tff(c_794, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_788])).
% 4.76/1.84  tff(c_798, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_58, c_372, c_794])).
% 4.76/1.84  tff(c_48, plain, (![C_31, A_29, B_30]: (v1_funct_1(k2_funct_1(C_31)) | k2_relset_1(A_29, B_30, C_31)!=B_30 | ~v2_funct_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.76/1.84  tff(c_1109, plain, (![C_141, B_142, A_143]: (v1_funct_1(k2_funct_1(k2_funct_1(C_141))) | k2_relset_1(B_142, A_143, k2_funct_1(C_141))!=A_143 | ~v2_funct_1(k2_funct_1(C_141)) | ~v1_funct_2(k2_funct_1(C_141), B_142, A_143) | ~v1_funct_1(k2_funct_1(C_141)) | k2_relset_1(A_143, B_142, C_141)!=B_142 | ~v2_funct_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))) | ~v1_funct_2(C_141, A_143, B_142) | ~v1_funct_1(C_141))), inference(resolution, [status(thm)], [c_645, c_48])).
% 4.76/1.84  tff(c_1115, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_1109])).
% 4.76/1.84  tff(c_1119, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_58, c_372, c_492, c_605, c_787, c_798, c_1115])).
% 4.76/1.84  tff(c_1120, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1119])).
% 4.76/1.84  tff(c_1123, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1120])).
% 4.76/1.84  tff(c_1127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_58, c_1123])).
% 4.76/1.84  tff(c_1129, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1119])).
% 4.76/1.84  tff(c_1135, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_798])).
% 4.76/1.84  tff(c_54, plain, (![A_34, B_35, C_36]: (k2_tops_2(A_34, B_35, C_36)=k2_funct_1(C_36) | ~v2_funct_1(C_36) | k2_relset_1(A_34, B_35, C_36)!=B_35 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.76/1.84  tff(c_1417, plain, (![B_152, A_153, C_154]: (k2_tops_2(B_152, A_153, k2_funct_1(C_154))=k2_funct_1(k2_funct_1(C_154)) | ~v2_funct_1(k2_funct_1(C_154)) | k2_relset_1(B_152, A_153, k2_funct_1(C_154))!=A_153 | ~v1_funct_2(k2_funct_1(C_154), B_152, A_153) | ~v1_funct_1(k2_funct_1(C_154)) | k2_relset_1(A_153, B_152, C_154)!=B_152 | ~v2_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))) | ~v1_funct_2(C_154, A_153, B_152) | ~v1_funct_1(C_154))), inference(resolution, [status(thm)], [c_645, c_54])).
% 4.76/1.84  tff(c_1423, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_1417])).
% 4.76/1.84  tff(c_1427, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_58, c_372, c_492, c_605, c_1135, c_787, c_1423])).
% 4.76/1.84  tff(c_626, plain, (![A_100, B_101, C_102]: (k2_tops_2(A_100, B_101, C_102)=k2_funct_1(C_102) | ~v2_funct_1(C_102) | k2_relset_1(A_100, B_101, C_102)!=B_101 | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(C_102, A_100, B_101) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.76/1.84  tff(c_629, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_626])).
% 4.76/1.84  tff(c_632, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_372, c_58, c_629])).
% 4.76/1.84  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.76/1.84  tff(c_156, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_83, c_82, c_82, c_82, c_56])).
% 4.76/1.84  tff(c_293, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_291, c_291, c_156])).
% 4.76/1.84  tff(c_373, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_367, c_367, c_293])).
% 4.76/1.84  tff(c_633, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_373])).
% 4.76/1.84  tff(c_1438, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_633])).
% 4.76/1.84  tff(c_1445, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1438])).
% 4.76/1.84  tff(c_1448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_58, c_843, c_1445])).
% 4.76/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.84  
% 4.76/1.84  Inference rules
% 4.76/1.84  ----------------------
% 4.76/1.84  #Ref     : 0
% 4.76/1.84  #Sup     : 317
% 4.76/1.84  #Fact    : 0
% 4.76/1.84  #Define  : 0
% 4.76/1.84  #Split   : 9
% 4.76/1.84  #Chain   : 0
% 4.76/1.84  #Close   : 0
% 4.76/1.84  
% 4.76/1.84  Ordering : KBO
% 4.76/1.84  
% 4.76/1.84  Simplification rules
% 4.76/1.84  ----------------------
% 4.76/1.84  #Subsume      : 38
% 4.76/1.84  #Demod        : 454
% 4.76/1.84  #Tautology    : 163
% 4.76/1.84  #SimpNegUnit  : 4
% 4.76/1.84  #BackRed      : 34
% 4.76/1.84  
% 4.76/1.84  #Partial instantiations: 0
% 4.76/1.84  #Strategies tried      : 1
% 4.76/1.84  
% 4.76/1.84  Timing (in seconds)
% 4.76/1.84  ----------------------
% 4.76/1.85  Preprocessing        : 0.39
% 4.76/1.85  Parsing              : 0.21
% 4.76/1.85  CNF conversion       : 0.02
% 4.76/1.85  Main loop            : 0.62
% 4.76/1.85  Inferencing          : 0.21
% 4.76/1.85  Reduction            : 0.21
% 4.76/1.85  Demodulation         : 0.15
% 4.76/1.85  BG Simplification    : 0.03
% 4.76/1.85  Subsumption          : 0.12
% 4.76/1.85  Abstraction          : 0.03
% 4.76/1.85  MUC search           : 0.00
% 4.76/1.85  Cooper               : 0.00
% 4.76/1.85  Total                : 1.06
% 4.76/1.85  Index Insertion      : 0.00
% 4.76/1.85  Index Deletion       : 0.00
% 4.76/1.85  Index Matching       : 0.00
% 4.76/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
