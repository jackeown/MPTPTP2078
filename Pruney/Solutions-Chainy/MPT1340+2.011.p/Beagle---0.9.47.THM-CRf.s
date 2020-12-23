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
% DateTime   : Thu Dec  3 10:23:31 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  140 (13829 expanded)
%              Number of leaves         :   41 (4827 expanded)
%              Depth                    :   22
%              Number of atoms          :  354 (40060 expanded)
%              Number of equality atoms :   76 (9131 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_175,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

tff(c_58,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_59,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_67,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_59])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_66,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_59])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_66,c_48])).

tff(c_97,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_97])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_166,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_166])).

tff(c_46,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_77,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_66,c_46])).

tff(c_171,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_77])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_83,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(u1_struct_0(A_42))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_89,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_83])).

tff(c_93,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_93])).

tff(c_180,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_94])).

tff(c_102,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_96,c_102])).

tff(c_158,plain,(
    ! [B_56,A_57] :
      ( k1_relat_1(B_56) = A_57
      | ~ v1_partfun1(B_56,A_57)
      | ~ v4_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_161,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_158])).

tff(c_164,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_161])).

tff(c_165,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_50])).

tff(c_82,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_68])).

tff(c_181,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_82])).

tff(c_179,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_96])).

tff(c_16,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_partfun1(C_15,A_12)
      | ~ v1_funct_2(C_15,A_12,B_13)
      | ~ v1_funct_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_204,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_179,c_16])).

tff(c_219,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_181,c_204])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_165,c_219])).

tff(c_222,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_226,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_96])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_271,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_14])).

tff(c_229,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_77])).

tff(c_282,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_229])).

tff(c_228,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_82])).

tff(c_290,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_228])).

tff(c_289,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_226])).

tff(c_340,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_funct_2(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(D_72,A_70,B_71)
      | ~ v1_funct_1(D_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_342,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_340])).

tff(c_345,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_342])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_287,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_271])).

tff(c_356,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_funct_1(k2_funct_1(C_74))
      | k2_relset_1(A_75,B_76,C_74) != B_76
      | ~ v2_funct_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_2(C_74,A_75,B_76)
      | ~ v1_funct_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_359,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_356])).

tff(c_362,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_44,c_287,c_359])).

tff(c_363,plain,(
    ! [C_77,B_78,A_79] :
      ( v1_funct_2(k2_funct_1(C_77),B_78,A_79)
      | k2_relset_1(A_79,B_78,C_77) != B_78
      | ~ v2_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_2(C_77,A_79,B_78)
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_366,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_363])).

tff(c_369,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_44,c_287,c_366])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_389,plain,(
    ! [C_84,B_85,A_86] :
      ( m1_subset_1(k2_funct_1(C_84),k1_zfmisc_1(k2_zfmisc_1(B_85,A_86)))
      | k2_relset_1(A_86,B_85,C_84) != B_85
      | ~ v2_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85)))
      | ~ v1_funct_2(C_84,A_86,B_85)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_508,plain,(
    ! [B_100,A_101,C_102] :
      ( k2_relset_1(B_100,A_101,k2_funct_1(C_102)) = k2_relat_1(k2_funct_1(C_102))
      | k2_relset_1(A_101,B_100,C_102) != B_100
      | ~ v2_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ v1_funct_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_389,c_14])).

tff(c_514,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_508])).

tff(c_518,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_44,c_287,c_514])).

tff(c_370,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_tops_2(A_80,B_81,C_82) = k2_funct_1(C_82)
      | ~ v2_funct_1(C_82)
      | k2_relset_1(A_80,B_81,C_82) != B_81
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_373,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_370])).

tff(c_376,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_287,c_44,c_373])).

tff(c_293,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_66])).

tff(c_230,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_67])).

tff(c_536,plain,(
    ! [A_104,B_105,C_106] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_104),u1_struct_0(B_105),C_106))
      | ~ v2_funct_1(C_106)
      | k2_relset_1(u1_struct_0(A_104),u1_struct_0(B_105),C_106) != k2_struct_0(B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104),u1_struct_0(B_105))))
      | ~ v1_funct_2(C_106,u1_struct_0(A_104),u1_struct_0(B_105))
      | ~ v1_funct_1(C_106)
      | ~ l1_struct_0(B_105)
      | ~ l1_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_549,plain,(
    ! [B_105,C_106] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_105),C_106))
      | ~ v2_funct_1(C_106)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_105),C_106) != k2_struct_0(B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_105))))
      | ~ v1_funct_2(C_106,u1_struct_0('#skF_1'),u1_struct_0(B_105))
      | ~ v1_funct_1(C_106)
      | ~ l1_struct_0(B_105)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_536])).

tff(c_598,plain,(
    ! [B_114,C_115] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0(B_114),C_115))
      | ~ v2_funct_1(C_115)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0(B_114),C_115) != k2_struct_0(B_114)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_114))))
      | ~ v1_funct_2(C_115,k1_relat_1('#skF_3'),u1_struct_0(B_114))
      | ~ v1_funct_1(C_115)
      | ~ l1_struct_0(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_230,c_230,c_230,c_549])).

tff(c_605,plain,(
    ! [C_115] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_115))
      | ~ v2_funct_1(C_115)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_115) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_115,k1_relat_1('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_115)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_598])).

tff(c_614,plain,(
    ! [C_116] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_116))
      | ~ v2_funct_1(C_116)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_116) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_116,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_293,c_293,c_282,c_293,c_605])).

tff(c_621,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_614])).

tff(c_625,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_287,c_44,c_376,c_621])).

tff(c_28,plain,(
    ! [C_24,B_23,A_22] :
      ( m1_subset_1(k2_funct_1(C_24),k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | k2_relset_1(A_22,B_23,C_24) != B_23
      | ~ v2_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_552,plain,(
    ! [A_104,C_106] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_104),u1_struct_0('#skF_1'),C_106))
      | ~ v2_funct_1(C_106)
      | k2_relset_1(u1_struct_0(A_104),u1_struct_0('#skF_1'),C_106) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_106,u1_struct_0(A_104),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_106)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_536])).

tff(c_632,plain,(
    ! [A_118,C_119] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_118),k1_relat_1('#skF_3'),C_119))
      | ~ v2_funct_1(C_119)
      | k2_relset_1(u1_struct_0(A_118),k1_relat_1('#skF_3'),C_119) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_118),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_119)
      | ~ l1_struct_0(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_230,c_230,c_222,c_230,c_552])).

tff(c_639,plain,(
    ! [C_119] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_119))
      | ~ v2_funct_1(C_119)
      | k2_relset_1(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_119) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_119,u1_struct_0('#skF_2'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_119)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_632])).

tff(c_648,plain,(
    ! [C_120] :
      ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),C_120))
      | ~ v2_funct_1(C_120)
      | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),C_120) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_120,k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_293,c_293,c_293,c_639])).

tff(c_925,plain,(
    ! [C_142] :
      ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1(C_142)))
      | ~ v2_funct_1(k2_funct_1(C_142))
      | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1(C_142)) != k1_relat_1('#skF_3')
      | ~ v1_funct_2(k2_funct_1(C_142),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1(C_142))
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_142) != k2_relat_1('#skF_3')
      | ~ v2_funct_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_142,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_28,c_648])).

tff(c_932,plain,
    ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_925])).

tff(c_936,plain,
    ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_44,c_287,c_362,c_369,c_518,c_625,c_932])).

tff(c_937,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_936])).

tff(c_940,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_937])).

tff(c_944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_52,c_44,c_940])).

tff(c_946,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_936])).

tff(c_947,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_518])).

tff(c_38,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_tops_2(A_27,B_28,C_29) = k2_funct_1(C_29)
      | ~ v2_funct_1(C_29)
      | k2_relset_1(A_27,B_28,C_29) != B_28
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_983,plain,(
    ! [B_143,A_144,C_145] :
      ( k2_tops_2(B_143,A_144,k2_funct_1(C_145)) = k2_funct_1(k2_funct_1(C_145))
      | ~ v2_funct_1(k2_funct_1(C_145))
      | k2_relset_1(B_143,A_144,k2_funct_1(C_145)) != A_144
      | ~ v1_funct_2(k2_funct_1(C_145),B_143,A_144)
      | ~ v1_funct_1(k2_funct_1(C_145))
      | k2_relset_1(A_144,B_143,C_145) != B_143
      | ~ v2_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ v1_funct_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_389,c_38])).

tff(c_989,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_983])).

tff(c_993,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_290,c_44,c_287,c_362,c_369,c_947,c_625,c_989])).

tff(c_42,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_107,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_67,c_66,c_66,c_66,c_42])).

tff(c_225,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_222,c_222,c_107])).

tff(c_288,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_282,c_282,c_225])).

tff(c_377,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_288])).

tff(c_995,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_377])).

tff(c_1003,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_995])).

tff(c_1006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_52,c_44,c_345,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.64  
% 3.87/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.64  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.87/1.64  
% 3.87/1.64  %Foreground sorts:
% 3.87/1.64  
% 3.87/1.64  
% 3.87/1.64  %Background operators:
% 3.87/1.64  
% 3.87/1.64  
% 3.87/1.64  %Foreground operators:
% 3.87/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.87/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.87/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.87/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.87/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.87/1.64  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.87/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.87/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.87/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.87/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.87/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.87/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.87/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.87/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.87/1.64  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.87/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.64  
% 3.87/1.67  tff(f_175, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.87/1.67  tff(f_115, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.87/1.67  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.87/1.67  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.87/1.67  tff(f_123, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.87/1.67  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.87/1.67  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.87/1.67  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.87/1.67  tff(f_95, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.87/1.67  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.87/1.67  tff(f_111, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.87/1.67  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.87/1.67  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.87/1.67  tff(f_153, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 3.87/1.67  tff(c_58, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_59, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.87/1.67  tff(c_67, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_59])).
% 3.87/1.67  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_66, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_59])).
% 3.87/1.67  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_66, c_48])).
% 3.87/1.67  tff(c_97, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.87/1.67  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_97])).
% 3.87/1.67  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_166, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.87/1.67  tff(c_170, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_166])).
% 3.87/1.67  tff(c_46, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_77, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_66, c_46])).
% 3.87/1.67  tff(c_171, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_77])).
% 3.87/1.67  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_83, plain, (![A_42]: (~v1_xboole_0(u1_struct_0(A_42)) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.87/1.67  tff(c_89, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_66, c_83])).
% 3.87/1.67  tff(c_93, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89])).
% 3.87/1.67  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_93])).
% 3.87/1.67  tff(c_180, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_94])).
% 3.87/1.67  tff(c_102, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.67  tff(c_106, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_96, c_102])).
% 3.87/1.67  tff(c_158, plain, (![B_56, A_57]: (k1_relat_1(B_56)=A_57 | ~v1_partfun1(B_56, A_57) | ~v4_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.67  tff(c_161, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_158])).
% 3.87/1.67  tff(c_164, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_161])).
% 3.87/1.67  tff(c_165, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_164])).
% 3.87/1.67  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_68, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_50])).
% 3.87/1.67  tff(c_82, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_68])).
% 3.87/1.67  tff(c_181, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_82])).
% 3.87/1.67  tff(c_179, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_96])).
% 3.87/1.67  tff(c_16, plain, (![C_15, A_12, B_13]: (v1_partfun1(C_15, A_12) | ~v1_funct_2(C_15, A_12, B_13) | ~v1_funct_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.67  tff(c_204, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_179, c_16])).
% 3.87/1.67  tff(c_219, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_181, c_204])).
% 3.87/1.67  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_165, c_219])).
% 3.87/1.67  tff(c_222, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_164])).
% 3.87/1.67  tff(c_226, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_96])).
% 3.87/1.67  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.87/1.67  tff(c_271, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_226, c_14])).
% 3.87/1.67  tff(c_229, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_77])).
% 3.87/1.67  tff(c_282, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_229])).
% 3.87/1.67  tff(c_228, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_82])).
% 3.87/1.67  tff(c_290, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_228])).
% 3.87/1.67  tff(c_289, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_226])).
% 3.87/1.67  tff(c_340, plain, (![A_70, B_71, D_72]: (r2_funct_2(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(D_72, A_70, B_71) | ~v1_funct_1(D_72))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.87/1.67  tff(c_342, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_340])).
% 3.87/1.67  tff(c_345, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_342])).
% 3.87/1.67  tff(c_6, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.87/1.67  tff(c_287, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_271])).
% 3.87/1.67  tff(c_356, plain, (![C_74, A_75, B_76]: (v1_funct_1(k2_funct_1(C_74)) | k2_relset_1(A_75, B_76, C_74)!=B_76 | ~v2_funct_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_2(C_74, A_75, B_76) | ~v1_funct_1(C_74))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.87/1.67  tff(c_359, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_356])).
% 3.87/1.67  tff(c_362, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_44, c_287, c_359])).
% 3.87/1.67  tff(c_363, plain, (![C_77, B_78, A_79]: (v1_funct_2(k2_funct_1(C_77), B_78, A_79) | k2_relset_1(A_79, B_78, C_77)!=B_78 | ~v2_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_2(C_77, A_79, B_78) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.87/1.67  tff(c_366, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_363])).
% 3.87/1.67  tff(c_369, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_44, c_287, c_366])).
% 3.87/1.67  tff(c_2, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.67  tff(c_389, plain, (![C_84, B_85, A_86]: (m1_subset_1(k2_funct_1(C_84), k1_zfmisc_1(k2_zfmisc_1(B_85, A_86))) | k2_relset_1(A_86, B_85, C_84)!=B_85 | ~v2_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))) | ~v1_funct_2(C_84, A_86, B_85) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.87/1.67  tff(c_508, plain, (![B_100, A_101, C_102]: (k2_relset_1(B_100, A_101, k2_funct_1(C_102))=k2_relat_1(k2_funct_1(C_102)) | k2_relset_1(A_101, B_100, C_102)!=B_100 | ~v2_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_102, A_101, B_100) | ~v1_funct_1(C_102))), inference(resolution, [status(thm)], [c_389, c_14])).
% 3.87/1.67  tff(c_514, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_508])).
% 3.87/1.67  tff(c_518, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_44, c_287, c_514])).
% 3.87/1.67  tff(c_370, plain, (![A_80, B_81, C_82]: (k2_tops_2(A_80, B_81, C_82)=k2_funct_1(C_82) | ~v2_funct_1(C_82) | k2_relset_1(A_80, B_81, C_82)!=B_81 | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_82, A_80, B_81) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.87/1.67  tff(c_373, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_370])).
% 3.87/1.67  tff(c_376, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_287, c_44, c_373])).
% 3.87/1.67  tff(c_293, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_66])).
% 3.87/1.67  tff(c_230, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_67])).
% 3.87/1.67  tff(c_536, plain, (![A_104, B_105, C_106]: (v2_funct_1(k2_tops_2(u1_struct_0(A_104), u1_struct_0(B_105), C_106)) | ~v2_funct_1(C_106) | k2_relset_1(u1_struct_0(A_104), u1_struct_0(B_105), C_106)!=k2_struct_0(B_105) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104), u1_struct_0(B_105)))) | ~v1_funct_2(C_106, u1_struct_0(A_104), u1_struct_0(B_105)) | ~v1_funct_1(C_106) | ~l1_struct_0(B_105) | ~l1_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.87/1.67  tff(c_549, plain, (![B_105, C_106]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_105), C_106)) | ~v2_funct_1(C_106) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_105), C_106)!=k2_struct_0(B_105) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_105)))) | ~v1_funct_2(C_106, u1_struct_0('#skF_1'), u1_struct_0(B_105)) | ~v1_funct_1(C_106) | ~l1_struct_0(B_105) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_536])).
% 3.87/1.67  tff(c_598, plain, (![B_114, C_115]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0(B_114), C_115)) | ~v2_funct_1(C_115) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0(B_114), C_115)!=k2_struct_0(B_114) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_114)))) | ~v1_funct_2(C_115, k1_relat_1('#skF_3'), u1_struct_0(B_114)) | ~v1_funct_1(C_115) | ~l1_struct_0(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_230, c_230, c_230, c_549])).
% 3.87/1.67  tff(c_605, plain, (![C_115]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_115)) | ~v2_funct_1(C_115) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_115)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_115, k1_relat_1('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_115) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_598])).
% 3.87/1.67  tff(c_614, plain, (![C_116]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_116)) | ~v2_funct_1(C_116) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_116)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_116, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_116))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_293, c_293, c_282, c_293, c_605])).
% 3.87/1.67  tff(c_621, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_614])).
% 3.87/1.67  tff(c_625, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_287, c_44, c_376, c_621])).
% 3.87/1.67  tff(c_28, plain, (![C_24, B_23, A_22]: (m1_subset_1(k2_funct_1(C_24), k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | k2_relset_1(A_22, B_23, C_24)!=B_23 | ~v2_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.87/1.67  tff(c_552, plain, (![A_104, C_106]: (v2_funct_1(k2_tops_2(u1_struct_0(A_104), u1_struct_0('#skF_1'), C_106)) | ~v2_funct_1(C_106) | k2_relset_1(u1_struct_0(A_104), u1_struct_0('#skF_1'), C_106)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_106, u1_struct_0(A_104), u1_struct_0('#skF_1')) | ~v1_funct_1(C_106) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_104))), inference(superposition, [status(thm), theory('equality')], [c_230, c_536])).
% 3.87/1.67  tff(c_632, plain, (![A_118, C_119]: (v2_funct_1(k2_tops_2(u1_struct_0(A_118), k1_relat_1('#skF_3'), C_119)) | ~v2_funct_1(C_119) | k2_relset_1(u1_struct_0(A_118), k1_relat_1('#skF_3'), C_119)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_119, u1_struct_0(A_118), k1_relat_1('#skF_3')) | ~v1_funct_1(C_119) | ~l1_struct_0(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_230, c_230, c_222, c_230, c_552])).
% 3.87/1.67  tff(c_639, plain, (![C_119]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_119)) | ~v2_funct_1(C_119) | k2_relset_1(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_119)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_119, u1_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_119) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_632])).
% 3.87/1.67  tff(c_648, plain, (![C_120]: (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), C_120)) | ~v2_funct_1(C_120) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), C_120)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_120, k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_120))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_293, c_293, c_293, c_639])).
% 3.87/1.67  tff(c_925, plain, (![C_142]: (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1(C_142))) | ~v2_funct_1(k2_funct_1(C_142)) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1(C_142))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1(C_142), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(C_142)) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_142)!=k2_relat_1('#skF_3') | ~v2_funct_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_142, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_142))), inference(resolution, [status(thm)], [c_28, c_648])).
% 3.87/1.67  tff(c_932, plain, (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_925])).
% 3.87/1.67  tff(c_936, plain, (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_44, c_287, c_362, c_369, c_518, c_625, c_932])).
% 3.87/1.67  tff(c_937, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_936])).
% 3.87/1.67  tff(c_940, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_937])).
% 3.87/1.67  tff(c_944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_52, c_44, c_940])).
% 3.87/1.67  tff(c_946, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_936])).
% 3.87/1.67  tff(c_947, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_946, c_518])).
% 3.87/1.67  tff(c_38, plain, (![A_27, B_28, C_29]: (k2_tops_2(A_27, B_28, C_29)=k2_funct_1(C_29) | ~v2_funct_1(C_29) | k2_relset_1(A_27, B_28, C_29)!=B_28 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.87/1.67  tff(c_983, plain, (![B_143, A_144, C_145]: (k2_tops_2(B_143, A_144, k2_funct_1(C_145))=k2_funct_1(k2_funct_1(C_145)) | ~v2_funct_1(k2_funct_1(C_145)) | k2_relset_1(B_143, A_144, k2_funct_1(C_145))!=A_144 | ~v1_funct_2(k2_funct_1(C_145), B_143, A_144) | ~v1_funct_1(k2_funct_1(C_145)) | k2_relset_1(A_144, B_143, C_145)!=B_143 | ~v2_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_2(C_145, A_144, B_143) | ~v1_funct_1(C_145))), inference(resolution, [status(thm)], [c_389, c_38])).
% 3.87/1.67  tff(c_989, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_983])).
% 3.87/1.67  tff(c_993, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_290, c_44, c_287, c_362, c_369, c_947, c_625, c_989])).
% 3.87/1.67  tff(c_42, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.87/1.67  tff(c_107, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_67, c_66, c_66, c_66, c_42])).
% 3.87/1.67  tff(c_225, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_222, c_222, c_107])).
% 3.87/1.67  tff(c_288, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_282, c_282, c_225])).
% 3.87/1.67  tff(c_377, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_288])).
% 3.87/1.67  tff(c_995, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_993, c_377])).
% 3.87/1.67  tff(c_1003, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_995])).
% 3.87/1.67  tff(c_1006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_52, c_44, c_345, c_1003])).
% 3.87/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.67  
% 3.87/1.67  Inference rules
% 3.87/1.67  ----------------------
% 3.87/1.67  #Ref     : 0
% 3.87/1.67  #Sup     : 202
% 3.87/1.67  #Fact    : 0
% 3.87/1.67  #Define  : 0
% 3.87/1.67  #Split   : 9
% 3.87/1.67  #Chain   : 0
% 3.87/1.67  #Close   : 0
% 3.87/1.67  
% 3.87/1.67  Ordering : KBO
% 3.87/1.67  
% 3.87/1.67  Simplification rules
% 3.87/1.67  ----------------------
% 3.87/1.67  #Subsume      : 9
% 3.87/1.67  #Demod        : 372
% 3.87/1.67  #Tautology    : 91
% 3.87/1.67  #SimpNegUnit  : 6
% 3.87/1.67  #BackRed      : 29
% 3.87/1.67  
% 3.87/1.67  #Partial instantiations: 0
% 3.87/1.67  #Strategies tried      : 1
% 3.87/1.67  
% 3.87/1.67  Timing (in seconds)
% 3.87/1.67  ----------------------
% 3.87/1.67  Preprocessing        : 0.37
% 3.87/1.67  Parsing              : 0.19
% 3.87/1.67  CNF conversion       : 0.02
% 3.87/1.67  Main loop            : 0.51
% 3.87/1.67  Inferencing          : 0.18
% 3.87/1.67  Reduction            : 0.18
% 3.87/1.67  Demodulation         : 0.13
% 3.87/1.67  BG Simplification    : 0.03
% 3.87/1.67  Subsumption          : 0.09
% 3.87/1.67  Abstraction          : 0.03
% 3.87/1.67  MUC search           : 0.00
% 3.87/1.67  Cooper               : 0.00
% 3.87/1.67  Total                : 0.94
% 3.87/1.67  Index Insertion      : 0.00
% 3.87/1.67  Index Deletion       : 0.00
% 3.87/1.67  Index Matching       : 0.00
% 3.87/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
