%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:32 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  160 (23185 expanded)
%              Number of leaves         :   43 (8093 expanded)
%              Depth                    :   26
%              Number of atoms          :  408 (67551 expanded)
%              Number of equality atoms :   81 (15185 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_173,negated_conjecture,(
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

tff(f_131,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
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

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_127,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_64,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_65,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_73,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_65])).

tff(c_60,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_65])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_97,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_72,c_54])).

tff(c_16,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_16])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_115,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_119,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_97,c_115])).

tff(c_148,plain,(
    ! [B_50,A_51] :
      ( k1_relat_1(B_50) = A_51
      | ~ v1_partfun1(B_50,A_51)
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_119,c_148])).

tff(c_154,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_151])).

tff(c_155,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_183,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_187,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_183])).

tff(c_52,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_102,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_72,c_52])).

tff(c_188,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_102])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_82,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_72,c_56])).

tff(c_199,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_82])).

tff(c_197,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_97])).

tff(c_239,plain,(
    ! [B_59,C_60,A_61] :
      ( k1_xboole_0 = B_59
      | v1_partfun1(C_60,A_61)
      | ~ v1_funct_2(C_60,A_61,B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_59)))
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_242,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_197,c_239])).

tff(c_245,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_199,c_242])).

tff(c_246,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_245])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_83,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(u1_struct_0(A_35))
      | ~ l1_struct_0(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_89,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_83])).

tff(c_93,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_89])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_93])).

tff(c_198,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94])).

tff(c_258,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_198])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_258])).

tff(c_263,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_268,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_97])).

tff(c_346,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_350,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_268,c_346])).

tff(c_267,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_102])).

tff(c_351,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_267])).

tff(c_270,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_82])).

tff(c_359,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_270])).

tff(c_358,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_268])).

tff(c_402,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_funct_2(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(D_74,A_72,B_73)
      | ~ v1_funct_1(D_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_404,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_402])).

tff(c_407,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_404])).

tff(c_14,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_356,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_350])).

tff(c_425,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_funct_1(k2_funct_1(C_79))
      | k2_relset_1(A_80,B_81,C_79) != B_81
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_79,A_80,B_81)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_428,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_425])).

tff(c_431,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_50,c_356,c_428])).

tff(c_432,plain,(
    ! [C_82,B_83,A_84] :
      ( v1_funct_2(k2_funct_1(C_82),B_83,A_84)
      | k2_relset_1(A_84,B_83,C_82) != B_83
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83)))
      | ~ v1_funct_2(C_82,A_84,B_83)
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_435,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_432])).

tff(c_438,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_50,c_356,c_435])).

tff(c_10,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_458,plain,(
    ! [C_89,B_90,A_91] :
      ( m1_subset_1(k2_funct_1(C_89),k1_zfmisc_1(k2_zfmisc_1(B_90,A_91)))
      | k2_relset_1(A_91,B_90,C_89) != B_90
      | ~ v2_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90)))
      | ~ v1_funct_2(C_89,A_91,B_90)
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_502,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(k2_funct_1(C_92))
      | k2_relset_1(A_93,B_94,C_92) != B_94
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_2(C_92,A_93,B_94)
      | ~ v1_funct_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_458,c_16])).

tff(c_508,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_502])).

tff(c_512,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_50,c_356,c_508])).

tff(c_20,plain,(
    ! [C_9,A_7,B_8] :
      ( v4_relat_1(C_9,A_7)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_520,plain,(
    ! [C_99,B_100,A_101] :
      ( v4_relat_1(k2_funct_1(C_99),B_100)
      | k2_relset_1(A_101,B_100,C_99) != B_100
      | ~ v2_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_99,A_101,B_100)
      | ~ v1_funct_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_458,c_20])).

tff(c_526,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_520])).

tff(c_530,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_50,c_356,c_526])).

tff(c_12,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_331,plain,(
    ! [A_66] :
      ( k1_relat_1(k2_funct_1(A_66)) = k2_relat_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [B_14] :
      ( v1_partfun1(B_14,k1_relat_1(B_14))
      | ~ v4_relat_1(B_14,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_415,plain,(
    ! [A_78] :
      ( v1_partfun1(k2_funct_1(A_78),k1_relat_1(k2_funct_1(A_78)))
      | ~ v4_relat_1(k2_funct_1(A_78),k2_relat_1(A_78))
      | ~ v1_relat_1(k2_funct_1(A_78))
      | ~ v2_funct_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_24])).

tff(c_418,plain,(
    ! [A_2] :
      ( v1_partfun1(k2_funct_1(A_2),k2_relat_1(A_2))
      | ~ v4_relat_1(k2_funct_1(A_2),k2_relat_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_415])).

tff(c_533,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_530,c_418])).

tff(c_539,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_58,c_50,c_512,c_533])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(B_14) = A_13
      | ~ v1_partfun1(B_14,A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_536,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_530,c_26])).

tff(c_542,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_536])).

tff(c_544,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_542])).

tff(c_603,plain,(
    ! [A_110] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_110)),k1_relat_1(A_110))
      | ~ v4_relat_1(k2_funct_1(k2_funct_1(A_110)),k2_relat_1(k2_funct_1(A_110)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_110)))
      | ~ v2_funct_1(k2_funct_1(A_110))
      | ~ v1_funct_1(k2_funct_1(A_110))
      | ~ v1_relat_1(k2_funct_1(A_110))
      | ~ v2_funct_1(A_110)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_415])).

tff(c_669,plain,(
    ! [A_122] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_122)),k1_relat_1(A_122))
      | ~ v4_relat_1(A_122,k2_relat_1(k2_funct_1(A_122)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_122)))
      | ~ v2_funct_1(k2_funct_1(A_122))
      | ~ v1_funct_1(k2_funct_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122)
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_603])).

tff(c_672,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_669])).

tff(c_683,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_431,c_512,c_431,c_672])).

tff(c_684,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_687,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_684])).

tff(c_691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_58,c_50,c_687])).

tff(c_693,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_582,plain,(
    ! [B_105,A_106,C_107] :
      ( k2_relset_1(B_105,A_106,k2_funct_1(C_107)) = k2_relat_1(k2_funct_1(C_107))
      | k2_relset_1(A_106,B_105,C_107) != B_105
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ v1_funct_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_458,c_22])).

tff(c_588,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_582])).

tff(c_592,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_50,c_356,c_588])).

tff(c_40,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_funct_1(k2_funct_1(C_24))
      | k2_relset_1(A_22,B_23,C_24) != B_23
      | ~ v2_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_694,plain,(
    ! [C_123,B_124,A_125] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_123)))
      | k2_relset_1(B_124,A_125,k2_funct_1(C_123)) != A_125
      | ~ v2_funct_1(k2_funct_1(C_123))
      | ~ v1_funct_2(k2_funct_1(C_123),B_124,A_125)
      | ~ v1_funct_1(k2_funct_1(C_123))
      | k2_relset_1(A_125,B_124,C_123) != B_124
      | ~ v2_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_2(C_123,A_125,B_124)
      | ~ v1_funct_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_458,c_40])).

tff(c_700,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_694])).

tff(c_704,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_50,c_356,c_431,c_438,c_592,c_700])).

tff(c_706,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_704])).

tff(c_707,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_710,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_707])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_58,c_50,c_710])).

tff(c_716,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_722,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_592])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_tops_2(A_27,B_28,C_29) = k2_funct_1(C_29)
      | ~ v2_funct_1(C_29)
      | k2_relset_1(A_27,B_28,C_29) != B_28
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_836,plain,(
    ! [B_129,A_130,C_131] :
      ( k2_tops_2(B_129,A_130,k2_funct_1(C_131)) = k2_funct_1(k2_funct_1(C_131))
      | ~ v2_funct_1(k2_funct_1(C_131))
      | k2_relset_1(B_129,A_130,k2_funct_1(C_131)) != A_130
      | ~ v1_funct_2(k2_funct_1(C_131),B_129,A_130)
      | ~ v1_funct_1(k2_funct_1(C_131))
      | k2_relset_1(A_130,B_129,C_131) != B_129
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_2(C_131,A_130,B_129)
      | ~ v1_funct_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_458,c_46])).

tff(c_842,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_836])).

tff(c_846,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_50,c_356,c_431,c_438,c_722,c_693,c_842])).

tff(c_439,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_tops_2(A_85,B_86,C_87) = k2_funct_1(C_87)
      | ~ v2_funct_1(C_87)
      | k2_relset_1(A_85,B_86,C_87) != B_86
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_442,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_439])).

tff(c_445,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_359,c_356,c_50,c_442])).

tff(c_48,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_108,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_73,c_72,c_72,c_72,c_48])).

tff(c_266,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_263,c_263,c_108])).

tff(c_357,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_351,c_351,c_266])).

tff(c_446,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_357])).

tff(c_847,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_446])).

tff(c_854,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_847])).

tff(c_857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_58,c_50,c_407,c_854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:13:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.59  
% 3.75/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.59  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.75/1.59  
% 3.75/1.59  %Foreground sorts:
% 3.75/1.59  
% 3.75/1.59  
% 3.75/1.59  %Background operators:
% 3.75/1.59  
% 3.75/1.59  
% 3.75/1.59  %Foreground operators:
% 3.75/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.75/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.75/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.75/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.75/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.75/1.59  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.75/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.75/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.75/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.75/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.75/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.75/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.75/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.75/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.59  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.75/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.59  
% 3.75/1.62  tff(f_173, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.75/1.62  tff(f_131, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.75/1.62  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.75/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.75/1.62  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.75/1.62  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.75/1.62  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.75/1.62  tff(f_111, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 3.75/1.62  tff(f_139, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.75/1.62  tff(f_94, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.75/1.62  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.75/1.62  tff(f_127, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.75/1.62  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.75/1.62  tff(f_38, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.75/1.62  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.75/1.62  tff(c_64, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_65, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.75/1.62  tff(c_73, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_65])).
% 3.75/1.62  tff(c_60, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_72, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_65])).
% 3.75/1.62  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_97, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_72, c_54])).
% 3.75/1.62  tff(c_16, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.75/1.62  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_97, c_16])).
% 3.75/1.62  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.75/1.62  tff(c_115, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.75/1.62  tff(c_119, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_97, c_115])).
% 3.75/1.62  tff(c_148, plain, (![B_50, A_51]: (k1_relat_1(B_50)=A_51 | ~v1_partfun1(B_50, A_51) | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.75/1.62  tff(c_151, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_119, c_148])).
% 3.75/1.62  tff(c_154, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_151])).
% 3.75/1.62  tff(c_155, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_154])).
% 3.75/1.62  tff(c_183, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.62  tff(c_187, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_97, c_183])).
% 3.75/1.62  tff(c_52, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_102, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_72, c_52])).
% 3.75/1.62  tff(c_188, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_102])).
% 3.75/1.62  tff(c_56, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_82, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_72, c_56])).
% 3.75/1.62  tff(c_199, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_82])).
% 3.75/1.62  tff(c_197, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_97])).
% 3.75/1.62  tff(c_239, plain, (![B_59, C_60, A_61]: (k1_xboole_0=B_59 | v1_partfun1(C_60, A_61) | ~v1_funct_2(C_60, A_61, B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_59))) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.75/1.62  tff(c_242, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_197, c_239])).
% 3.75/1.62  tff(c_245, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_199, c_242])).
% 3.75/1.62  tff(c_246, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_155, c_245])).
% 3.75/1.62  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_83, plain, (![A_35]: (~v1_xboole_0(u1_struct_0(A_35)) | ~l1_struct_0(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.75/1.62  tff(c_89, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_83])).
% 3.75/1.62  tff(c_93, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_89])).
% 3.75/1.62  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_93])).
% 3.75/1.62  tff(c_198, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94])).
% 3.75/1.62  tff(c_258, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_246, c_198])).
% 3.75/1.62  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_258])).
% 3.75/1.62  tff(c_263, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_154])).
% 3.75/1.62  tff(c_268, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_97])).
% 3.75/1.62  tff(c_346, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.62  tff(c_350, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_268, c_346])).
% 3.75/1.62  tff(c_267, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_102])).
% 3.75/1.62  tff(c_351, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_267])).
% 3.75/1.62  tff(c_270, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_82])).
% 3.75/1.62  tff(c_359, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_270])).
% 3.75/1.62  tff(c_358, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_268])).
% 3.75/1.62  tff(c_402, plain, (![A_72, B_73, D_74]: (r2_funct_2(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(D_74, A_72, B_73) | ~v1_funct_1(D_74))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.75/1.62  tff(c_404, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_402])).
% 3.75/1.62  tff(c_407, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_404])).
% 3.75/1.62  tff(c_14, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.75/1.62  tff(c_356, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_350])).
% 3.75/1.62  tff(c_425, plain, (![C_79, A_80, B_81]: (v1_funct_1(k2_funct_1(C_79)) | k2_relset_1(A_80, B_81, C_79)!=B_81 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_79, A_80, B_81) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.75/1.62  tff(c_428, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_425])).
% 3.75/1.62  tff(c_431, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_50, c_356, c_428])).
% 3.75/1.62  tff(c_432, plain, (![C_82, B_83, A_84]: (v1_funct_2(k2_funct_1(C_82), B_83, A_84) | k2_relset_1(A_84, B_83, C_82)!=B_83 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))) | ~v1_funct_2(C_82, A_84, B_83) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.75/1.62  tff(c_435, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_432])).
% 3.75/1.62  tff(c_438, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_50, c_356, c_435])).
% 3.75/1.62  tff(c_10, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.75/1.62  tff(c_4, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.75/1.62  tff(c_458, plain, (![C_89, B_90, A_91]: (m1_subset_1(k2_funct_1(C_89), k1_zfmisc_1(k2_zfmisc_1(B_90, A_91))) | k2_relset_1(A_91, B_90, C_89)!=B_90 | ~v2_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))) | ~v1_funct_2(C_89, A_91, B_90) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.75/1.62  tff(c_502, plain, (![C_92, A_93, B_94]: (v1_relat_1(k2_funct_1(C_92)) | k2_relset_1(A_93, B_94, C_92)!=B_94 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_2(C_92, A_93, B_94) | ~v1_funct_1(C_92))), inference(resolution, [status(thm)], [c_458, c_16])).
% 3.75/1.62  tff(c_508, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_502])).
% 3.75/1.62  tff(c_512, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_50, c_356, c_508])).
% 3.75/1.62  tff(c_20, plain, (![C_9, A_7, B_8]: (v4_relat_1(C_9, A_7) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.75/1.62  tff(c_520, plain, (![C_99, B_100, A_101]: (v4_relat_1(k2_funct_1(C_99), B_100) | k2_relset_1(A_101, B_100, C_99)!=B_100 | ~v2_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_99, A_101, B_100) | ~v1_funct_1(C_99))), inference(resolution, [status(thm)], [c_458, c_20])).
% 3.75/1.62  tff(c_526, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_520])).
% 3.75/1.62  tff(c_530, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_50, c_356, c_526])).
% 3.75/1.62  tff(c_12, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.75/1.62  tff(c_331, plain, (![A_66]: (k1_relat_1(k2_funct_1(A_66))=k2_relat_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.75/1.62  tff(c_24, plain, (![B_14]: (v1_partfun1(B_14, k1_relat_1(B_14)) | ~v4_relat_1(B_14, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.75/1.62  tff(c_415, plain, (![A_78]: (v1_partfun1(k2_funct_1(A_78), k1_relat_1(k2_funct_1(A_78))) | ~v4_relat_1(k2_funct_1(A_78), k2_relat_1(A_78)) | ~v1_relat_1(k2_funct_1(A_78)) | ~v2_funct_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_331, c_24])).
% 3.75/1.62  tff(c_418, plain, (![A_2]: (v1_partfun1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v4_relat_1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_12, c_415])).
% 3.75/1.62  tff(c_533, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_530, c_418])).
% 3.75/1.62  tff(c_539, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_58, c_50, c_512, c_533])).
% 3.75/1.62  tff(c_26, plain, (![B_14, A_13]: (k1_relat_1(B_14)=A_13 | ~v1_partfun1(B_14, A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.75/1.62  tff(c_536, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_530, c_26])).
% 3.75/1.62  tff(c_542, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_536])).
% 3.75/1.62  tff(c_544, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_542])).
% 3.75/1.62  tff(c_603, plain, (![A_110]: (v1_partfun1(k2_funct_1(k2_funct_1(A_110)), k1_relat_1(A_110)) | ~v4_relat_1(k2_funct_1(k2_funct_1(A_110)), k2_relat_1(k2_funct_1(A_110))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_110))) | ~v2_funct_1(k2_funct_1(A_110)) | ~v1_funct_1(k2_funct_1(A_110)) | ~v1_relat_1(k2_funct_1(A_110)) | ~v2_funct_1(A_110) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_14, c_415])).
% 3.75/1.62  tff(c_669, plain, (![A_122]: (v1_partfun1(k2_funct_1(k2_funct_1(A_122)), k1_relat_1(A_122)) | ~v4_relat_1(A_122, k2_relat_1(k2_funct_1(A_122))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_122))) | ~v2_funct_1(k2_funct_1(A_122)) | ~v1_funct_1(k2_funct_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_14, c_603])).
% 3.75/1.62  tff(c_672, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_544, c_669])).
% 3.75/1.62  tff(c_683, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_431, c_512, c_431, c_672])).
% 3.75/1.62  tff(c_684, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_683])).
% 3.75/1.62  tff(c_687, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_684])).
% 3.75/1.62  tff(c_691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_58, c_50, c_687])).
% 3.75/1.62  tff(c_693, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_683])).
% 3.75/1.62  tff(c_22, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.62  tff(c_582, plain, (![B_105, A_106, C_107]: (k2_relset_1(B_105, A_106, k2_funct_1(C_107))=k2_relat_1(k2_funct_1(C_107)) | k2_relset_1(A_106, B_105, C_107)!=B_105 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_107, A_106, B_105) | ~v1_funct_1(C_107))), inference(resolution, [status(thm)], [c_458, c_22])).
% 3.75/1.62  tff(c_588, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_582])).
% 3.75/1.62  tff(c_592, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_50, c_356, c_588])).
% 3.75/1.62  tff(c_40, plain, (![C_24, A_22, B_23]: (v1_funct_1(k2_funct_1(C_24)) | k2_relset_1(A_22, B_23, C_24)!=B_23 | ~v2_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.75/1.62  tff(c_694, plain, (![C_123, B_124, A_125]: (v1_funct_1(k2_funct_1(k2_funct_1(C_123))) | k2_relset_1(B_124, A_125, k2_funct_1(C_123))!=A_125 | ~v2_funct_1(k2_funct_1(C_123)) | ~v1_funct_2(k2_funct_1(C_123), B_124, A_125) | ~v1_funct_1(k2_funct_1(C_123)) | k2_relset_1(A_125, B_124, C_123)!=B_124 | ~v2_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_2(C_123, A_125, B_124) | ~v1_funct_1(C_123))), inference(resolution, [status(thm)], [c_458, c_40])).
% 3.75/1.62  tff(c_700, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_694])).
% 3.75/1.62  tff(c_704, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_50, c_356, c_431, c_438, c_592, c_700])).
% 3.75/1.62  tff(c_706, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_704])).
% 3.75/1.62  tff(c_707, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_706])).
% 3.75/1.62  tff(c_710, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_707])).
% 3.75/1.62  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_58, c_50, c_710])).
% 3.75/1.62  tff(c_716, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_706])).
% 3.75/1.62  tff(c_722, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_592])).
% 3.75/1.62  tff(c_46, plain, (![A_27, B_28, C_29]: (k2_tops_2(A_27, B_28, C_29)=k2_funct_1(C_29) | ~v2_funct_1(C_29) | k2_relset_1(A_27, B_28, C_29)!=B_28 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.75/1.62  tff(c_836, plain, (![B_129, A_130, C_131]: (k2_tops_2(B_129, A_130, k2_funct_1(C_131))=k2_funct_1(k2_funct_1(C_131)) | ~v2_funct_1(k2_funct_1(C_131)) | k2_relset_1(B_129, A_130, k2_funct_1(C_131))!=A_130 | ~v1_funct_2(k2_funct_1(C_131), B_129, A_130) | ~v1_funct_1(k2_funct_1(C_131)) | k2_relset_1(A_130, B_129, C_131)!=B_129 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(C_131, A_130, B_129) | ~v1_funct_1(C_131))), inference(resolution, [status(thm)], [c_458, c_46])).
% 3.75/1.62  tff(c_842, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_836])).
% 3.75/1.62  tff(c_846, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_50, c_356, c_431, c_438, c_722, c_693, c_842])).
% 3.75/1.62  tff(c_439, plain, (![A_85, B_86, C_87]: (k2_tops_2(A_85, B_86, C_87)=k2_funct_1(C_87) | ~v2_funct_1(C_87) | k2_relset_1(A_85, B_86, C_87)!=B_86 | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_87, A_85, B_86) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.75/1.62  tff(c_442, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_439])).
% 3.75/1.62  tff(c_445, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_359, c_356, c_50, c_442])).
% 3.75/1.62  tff(c_48, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.75/1.62  tff(c_108, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_73, c_72, c_72, c_72, c_48])).
% 3.75/1.62  tff(c_266, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_263, c_263, c_108])).
% 3.75/1.62  tff(c_357, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_351, c_351, c_266])).
% 3.75/1.62  tff(c_446, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_357])).
% 3.75/1.62  tff(c_847, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_846, c_446])).
% 3.75/1.62  tff(c_854, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_847])).
% 3.75/1.62  tff(c_857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_58, c_50, c_407, c_854])).
% 3.75/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.62  
% 3.75/1.62  Inference rules
% 3.75/1.62  ----------------------
% 3.75/1.62  #Ref     : 0
% 3.75/1.62  #Sup     : 174
% 3.75/1.62  #Fact    : 0
% 3.75/1.62  #Define  : 0
% 3.75/1.62  #Split   : 7
% 3.75/1.62  #Chain   : 0
% 3.75/1.62  #Close   : 0
% 3.75/1.62  
% 3.75/1.62  Ordering : KBO
% 3.75/1.62  
% 3.75/1.62  Simplification rules
% 3.75/1.62  ----------------------
% 3.75/1.62  #Subsume      : 6
% 3.75/1.62  #Demod        : 240
% 3.75/1.62  #Tautology    : 89
% 3.75/1.62  #SimpNegUnit  : 4
% 3.75/1.62  #BackRed      : 33
% 3.75/1.62  
% 3.75/1.62  #Partial instantiations: 0
% 3.75/1.62  #Strategies tried      : 1
% 3.75/1.62  
% 3.75/1.62  Timing (in seconds)
% 3.75/1.62  ----------------------
% 3.75/1.62  Preprocessing        : 0.37
% 3.75/1.63  Parsing              : 0.19
% 3.75/1.63  CNF conversion       : 0.02
% 3.75/1.63  Main loop            : 0.46
% 3.75/1.63  Inferencing          : 0.16
% 3.75/1.63  Reduction            : 0.15
% 3.75/1.63  Demodulation         : 0.11
% 3.75/1.63  BG Simplification    : 0.03
% 3.75/1.63  Subsumption          : 0.08
% 3.75/1.63  Abstraction          : 0.02
% 3.75/1.63  MUC search           : 0.00
% 3.75/1.63  Cooper               : 0.00
% 3.75/1.63  Total                : 0.89
% 3.75/1.63  Index Insertion      : 0.00
% 3.75/1.63  Index Deletion       : 0.00
% 3.75/1.63  Index Matching       : 0.00
% 3.75/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
