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
% DateTime   : Thu Dec  3 10:23:31 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  143 (14150 expanded)
%              Number of leaves         :   41 (4938 expanded)
%              Depth                    :   22
%              Number of atoms          :  368 (40991 expanded)
%              Number of equality atoms :   76 (9337 expanded)
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

tff(f_113,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_109,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_151,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_57,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_65,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_57])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_57])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_75,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_46])).

tff(c_95,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_95])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_164,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_164])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_90,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_44])).

tff(c_169,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_90])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_77,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(u1_struct_0(A_42))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_83,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_77])).

tff(c_87,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_88,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_87])).

tff(c_177,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_88])).

tff(c_100,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_75,c_100])).

tff(c_129,plain,(
    ! [B_54,A_55] :
      ( k1_relat_1(B_54) = A_55
      | ~ v1_partfun1(B_54,A_55)
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_129])).

tff(c_135,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_132])).

tff(c_136,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_66])).

tff(c_178,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_76])).

tff(c_179,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_75])).

tff(c_16,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_partfun1(C_15,A_12)
      | ~ v1_funct_2(C_15,A_12,B_13)
      | ~ v1_funct_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_198,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_179,c_16])).

tff(c_213,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_178,c_198])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_136,c_213])).

tff(c_216,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_223,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_75])).

tff(c_298,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_302,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_223,c_298])).

tff(c_220,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_90])).

tff(c_303,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_220])).

tff(c_222,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_76])).

tff(c_311,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_222])).

tff(c_310,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_223])).

tff(c_462,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( r2_funct_2(A_92,B_93,C_94,C_94)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2(D_95,A_92,B_93)
      | ~ v1_funct_1(D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2(C_94,A_92,B_93)
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_466,plain,(
    ! [C_94] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_94,C_94)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_94,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_310,c_462])).

tff(c_494,plain,(
    ! [C_99] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_99,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_99,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_466])).

tff(c_499,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_494])).

tff(c_503,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_499])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_308,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_302])).

tff(c_371,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_funct_1(k2_funct_1(C_73))
      | k2_relset_1(A_74,B_75,C_73) != B_75
      | ~ v2_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_374,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_371])).

tff(c_377,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_42,c_308,c_374])).

tff(c_378,plain,(
    ! [C_76,B_77,A_78] :
      ( v1_funct_2(k2_funct_1(C_76),B_77,A_78)
      | k2_relset_1(A_78,B_77,C_76) != B_77
      | ~ v2_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77)))
      | ~ v1_funct_2(C_76,A_78,B_77)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_381,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_378])).

tff(c_384,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_42,c_308,c_381])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_404,plain,(
    ! [C_83,B_84,A_85] :
      ( m1_subset_1(k2_funct_1(C_83),k1_zfmisc_1(k2_zfmisc_1(B_84,A_85)))
      | k2_relset_1(A_85,B_84,C_83) != B_84
      | ~ v2_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84)))
      | ~ v1_funct_2(C_83,A_85,B_84)
      | ~ v1_funct_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_532,plain,(
    ! [B_100,A_101,C_102] :
      ( k2_relset_1(B_100,A_101,k2_funct_1(C_102)) = k2_relat_1(k2_funct_1(C_102))
      | k2_relset_1(A_101,B_100,C_102) != B_100
      | ~ v2_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ v1_funct_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_404,c_14])).

tff(c_538,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_532])).

tff(c_542,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_42,c_308,c_538])).

tff(c_385,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_tops_2(A_79,B_80,C_81) = k2_funct_1(C_81)
      | ~ v2_funct_1(C_81)
      | k2_relset_1(A_79,B_80,C_81) != B_80
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(C_81,A_79,B_80)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_388,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_385])).

tff(c_391,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_308,c_42,c_388])).

tff(c_314,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_64])).

tff(c_224,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_65])).

tff(c_547,plain,(
    ! [A_103,B_104,C_105] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_103),u1_struct_0(B_104),C_105))
      | ~ v2_funct_1(C_105)
      | k2_relset_1(u1_struct_0(A_103),u1_struct_0(B_104),C_105) != k2_struct_0(B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,u1_struct_0(A_103),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_struct_0(B_104)
      | ~ l1_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_560,plain,(
    ! [B_104,C_105] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_104),C_105))
      | ~ v2_funct_1(C_105)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_104),C_105) != k2_struct_0(B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,u1_struct_0('#skF_1'),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_struct_0(B_104)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_547])).

tff(c_611,plain,(
    ! [B_111,C_112] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0(B_111),C_112))
      | ~ v2_funct_1(C_112)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0(B_111),C_112) != k2_struct_0(B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_112,k1_relat_1('#skF_3'),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ l1_struct_0(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_224,c_224,c_560])).

tff(c_618,plain,(
    ! [C_112] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_112))
      | ~ v2_funct_1(C_112)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_112) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_112,k1_relat_1('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_112)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_611])).

tff(c_627,plain,(
    ! [C_113] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_113))
      | ~ v2_funct_1(C_113)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_113) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_113,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_314,c_314,c_303,c_314,c_618])).

tff(c_634,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_627])).

tff(c_638,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_308,c_42,c_391,c_634])).

tff(c_26,plain,(
    ! [C_24,B_23,A_22] :
      ( m1_subset_1(k2_funct_1(C_24),k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | k2_relset_1(A_22,B_23,C_24) != B_23
      | ~ v2_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_563,plain,(
    ! [A_103,C_105] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_103),u1_struct_0('#skF_1'),C_105))
      | ~ v2_funct_1(C_105)
      | k2_relset_1(u1_struct_0(A_103),u1_struct_0('#skF_1'),C_105) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_105,u1_struct_0(A_103),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_105)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_547])).

tff(c_645,plain,(
    ! [A_115,C_116] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_115),k1_relat_1('#skF_3'),C_116))
      | ~ v2_funct_1(C_116)
      | k2_relset_1(u1_struct_0(A_115),k1_relat_1('#skF_3'),C_116) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_115),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_116,u1_struct_0(A_115),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_116)
      | ~ l1_struct_0(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_224,c_216,c_224,c_563])).

tff(c_652,plain,(
    ! [C_116] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_116))
      | ~ v2_funct_1(C_116)
      | k2_relset_1(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_116) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_116,u1_struct_0('#skF_2'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_116)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_645])).

tff(c_661,plain,(
    ! [C_117] :
      ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),C_117))
      | ~ v2_funct_1(C_117)
      | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),C_117) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_117,k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_314,c_314,c_314,c_652])).

tff(c_713,plain,(
    ! [C_126] :
      ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1(C_126)))
      | ~ v2_funct_1(k2_funct_1(C_126))
      | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1(C_126)) != k1_relat_1('#skF_3')
      | ~ v1_funct_2(k2_funct_1(C_126),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1(C_126))
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_126) != k2_relat_1('#skF_3')
      | ~ v2_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_126,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_126) ) ),
    inference(resolution,[status(thm)],[c_26,c_661])).

tff(c_720,plain,
    ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_713])).

tff(c_724,plain,
    ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_42,c_308,c_377,c_384,c_542,c_638,c_720])).

tff(c_725,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_728,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_725])).

tff(c_732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_50,c_42,c_728])).

tff(c_734,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_735,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_542])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_tops_2(A_27,B_28,C_29) = k2_funct_1(C_29)
      | ~ v2_funct_1(C_29)
      | k2_relset_1(A_27,B_28,C_29) != B_28
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_902,plain,(
    ! [B_135,A_136,C_137] :
      ( k2_tops_2(B_135,A_136,k2_funct_1(C_137)) = k2_funct_1(k2_funct_1(C_137))
      | ~ v2_funct_1(k2_funct_1(C_137))
      | k2_relset_1(B_135,A_136,k2_funct_1(C_137)) != A_136
      | ~ v1_funct_2(k2_funct_1(C_137),B_135,A_136)
      | ~ v1_funct_1(k2_funct_1(C_137))
      | k2_relset_1(A_136,B_135,C_137) != B_135
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135)))
      | ~ v1_funct_2(C_137,A_136,B_135)
      | ~ v1_funct_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_404,c_36])).

tff(c_908,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_310,c_902])).

tff(c_912,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311,c_42,c_308,c_377,c_384,c_735,c_638,c_908])).

tff(c_40,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_105,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_65,c_64,c_64,c_64,c_40])).

tff(c_219,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_216,c_105])).

tff(c_309,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_303,c_303,c_219])).

tff(c_392,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_309])).

tff(c_914,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_392])).

tff(c_926,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_914])).

tff(c_929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_50,c_42,c_503,c_926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:13:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.61  
% 3.59/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.61  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.59/1.61  
% 3.59/1.61  %Foreground sorts:
% 3.59/1.61  
% 3.59/1.61  
% 3.59/1.61  %Background operators:
% 3.59/1.61  
% 3.59/1.61  
% 3.59/1.61  %Foreground operators:
% 3.59/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.59/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.59/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.59/1.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.59/1.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.59/1.61  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.59/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.59/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.61  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.59/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.59/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.59/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.59/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.59/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.61  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.59/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.61  
% 3.84/1.64  tff(f_173, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.84/1.64  tff(f_113, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.84/1.64  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.84/1.64  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.84/1.64  tff(f_121, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.84/1.64  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.84/1.64  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.84/1.64  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.84/1.64  tff(f_93, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.84/1.64  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.84/1.64  tff(f_109, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.84/1.64  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.84/1.64  tff(f_133, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.84/1.64  tff(f_151, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 3.84/1.64  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_57, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.84/1.64  tff(c_65, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_57])).
% 3.84/1.64  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_57])).
% 3.84/1.64  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_75, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_46])).
% 3.84/1.64  tff(c_95, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.84/1.64  tff(c_99, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_95])).
% 3.84/1.64  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_164, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.84/1.64  tff(c_168, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_164])).
% 3.84/1.64  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_90, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_44])).
% 3.84/1.64  tff(c_169, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_90])).
% 3.84/1.64  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_77, plain, (![A_42]: (~v1_xboole_0(u1_struct_0(A_42)) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.84/1.64  tff(c_83, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64, c_77])).
% 3.84/1.64  tff(c_87, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 3.84/1.64  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_87])).
% 3.84/1.64  tff(c_177, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_88])).
% 3.84/1.64  tff(c_100, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.84/1.64  tff(c_104, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_75, c_100])).
% 3.84/1.64  tff(c_129, plain, (![B_54, A_55]: (k1_relat_1(B_54)=A_55 | ~v1_partfun1(B_54, A_55) | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.84/1.64  tff(c_132, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_129])).
% 3.84/1.64  tff(c_135, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_132])).
% 3.84/1.64  tff(c_136, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_135])).
% 3.84/1.64  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_48])).
% 3.84/1.64  tff(c_76, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_66])).
% 3.84/1.64  tff(c_178, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_76])).
% 3.84/1.64  tff(c_179, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_75])).
% 3.84/1.64  tff(c_16, plain, (![C_15, A_12, B_13]: (v1_partfun1(C_15, A_12) | ~v1_funct_2(C_15, A_12, B_13) | ~v1_funct_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.84/1.64  tff(c_198, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_179, c_16])).
% 3.84/1.64  tff(c_213, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_178, c_198])).
% 3.84/1.64  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_136, c_213])).
% 3.84/1.64  tff(c_216, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_135])).
% 3.84/1.64  tff(c_223, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_75])).
% 3.84/1.64  tff(c_298, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.84/1.64  tff(c_302, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_223, c_298])).
% 3.84/1.64  tff(c_220, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_90])).
% 3.84/1.64  tff(c_303, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_220])).
% 3.84/1.64  tff(c_222, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_76])).
% 3.84/1.64  tff(c_311, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_222])).
% 3.84/1.64  tff(c_310, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_223])).
% 3.84/1.64  tff(c_462, plain, (![A_92, B_93, C_94, D_95]: (r2_funct_2(A_92, B_93, C_94, C_94) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2(D_95, A_92, B_93) | ~v1_funct_1(D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2(C_94, A_92, B_93) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.84/1.64  tff(c_466, plain, (![C_94]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_94, C_94) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_94, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_94))), inference(resolution, [status(thm)], [c_310, c_462])).
% 3.84/1.64  tff(c_494, plain, (![C_99]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_99, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_99, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_466])).
% 3.84/1.64  tff(c_499, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_494])).
% 3.84/1.64  tff(c_503, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_499])).
% 3.84/1.64  tff(c_6, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.84/1.64  tff(c_308, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_302])).
% 3.84/1.64  tff(c_371, plain, (![C_73, A_74, B_75]: (v1_funct_1(k2_funct_1(C_73)) | k2_relset_1(A_74, B_75, C_73)!=B_75 | ~v2_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.84/1.64  tff(c_374, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_371])).
% 3.84/1.64  tff(c_377, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_42, c_308, c_374])).
% 3.84/1.64  tff(c_378, plain, (![C_76, B_77, A_78]: (v1_funct_2(k2_funct_1(C_76), B_77, A_78) | k2_relset_1(A_78, B_77, C_76)!=B_77 | ~v2_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))) | ~v1_funct_2(C_76, A_78, B_77) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.84/1.64  tff(c_381, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_378])).
% 3.84/1.64  tff(c_384, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_42, c_308, c_381])).
% 3.84/1.64  tff(c_2, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.84/1.64  tff(c_404, plain, (![C_83, B_84, A_85]: (m1_subset_1(k2_funct_1(C_83), k1_zfmisc_1(k2_zfmisc_1(B_84, A_85))) | k2_relset_1(A_85, B_84, C_83)!=B_84 | ~v2_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))) | ~v1_funct_2(C_83, A_85, B_84) | ~v1_funct_1(C_83))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.84/1.64  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.84/1.64  tff(c_532, plain, (![B_100, A_101, C_102]: (k2_relset_1(B_100, A_101, k2_funct_1(C_102))=k2_relat_1(k2_funct_1(C_102)) | k2_relset_1(A_101, B_100, C_102)!=B_100 | ~v2_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_102, A_101, B_100) | ~v1_funct_1(C_102))), inference(resolution, [status(thm)], [c_404, c_14])).
% 3.84/1.64  tff(c_538, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_532])).
% 3.84/1.64  tff(c_542, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_42, c_308, c_538])).
% 3.84/1.64  tff(c_385, plain, (![A_79, B_80, C_81]: (k2_tops_2(A_79, B_80, C_81)=k2_funct_1(C_81) | ~v2_funct_1(C_81) | k2_relset_1(A_79, B_80, C_81)!=B_80 | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_2(C_81, A_79, B_80) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.84/1.64  tff(c_388, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_385])).
% 3.84/1.64  tff(c_391, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_308, c_42, c_388])).
% 3.84/1.64  tff(c_314, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_64])).
% 3.84/1.64  tff(c_224, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_65])).
% 3.84/1.64  tff(c_547, plain, (![A_103, B_104, C_105]: (v2_funct_1(k2_tops_2(u1_struct_0(A_103), u1_struct_0(B_104), C_105)) | ~v2_funct_1(C_105) | k2_relset_1(u1_struct_0(A_103), u1_struct_0(B_104), C_105)!=k2_struct_0(B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, u1_struct_0(A_103), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_struct_0(B_104) | ~l1_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.84/1.64  tff(c_560, plain, (![B_104, C_105]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_104), C_105)) | ~v2_funct_1(C_105) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_104), C_105)!=k2_struct_0(B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, u1_struct_0('#skF_1'), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_struct_0(B_104) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_547])).
% 3.84/1.64  tff(c_611, plain, (![B_111, C_112]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0(B_111), C_112)) | ~v2_funct_1(C_112) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0(B_111), C_112)!=k2_struct_0(B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_111)))) | ~v1_funct_2(C_112, k1_relat_1('#skF_3'), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~l1_struct_0(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_224, c_224, c_560])).
% 3.84/1.64  tff(c_618, plain, (![C_112]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_112)) | ~v2_funct_1(C_112) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_112)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_112, k1_relat_1('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_112) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_611])).
% 3.84/1.64  tff(c_627, plain, (![C_113]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_113)) | ~v2_funct_1(C_113) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_113)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_113, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_113))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_314, c_314, c_303, c_314, c_618])).
% 3.84/1.64  tff(c_634, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_627])).
% 3.84/1.64  tff(c_638, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_308, c_42, c_391, c_634])).
% 3.84/1.64  tff(c_26, plain, (![C_24, B_23, A_22]: (m1_subset_1(k2_funct_1(C_24), k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | k2_relset_1(A_22, B_23, C_24)!=B_23 | ~v2_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.84/1.64  tff(c_563, plain, (![A_103, C_105]: (v2_funct_1(k2_tops_2(u1_struct_0(A_103), u1_struct_0('#skF_1'), C_105)) | ~v2_funct_1(C_105) | k2_relset_1(u1_struct_0(A_103), u1_struct_0('#skF_1'), C_105)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_105, u1_struct_0(A_103), u1_struct_0('#skF_1')) | ~v1_funct_1(C_105) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_103))), inference(superposition, [status(thm), theory('equality')], [c_224, c_547])).
% 3.84/1.64  tff(c_645, plain, (![A_115, C_116]: (v2_funct_1(k2_tops_2(u1_struct_0(A_115), k1_relat_1('#skF_3'), C_116)) | ~v2_funct_1(C_116) | k2_relset_1(u1_struct_0(A_115), k1_relat_1('#skF_3'), C_116)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_115), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_116, u1_struct_0(A_115), k1_relat_1('#skF_3')) | ~v1_funct_1(C_116) | ~l1_struct_0(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_224, c_216, c_224, c_563])).
% 3.84/1.64  tff(c_652, plain, (![C_116]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_116)) | ~v2_funct_1(C_116) | k2_relset_1(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_116)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_116, u1_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_116) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_645])).
% 3.84/1.64  tff(c_661, plain, (![C_117]: (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), C_117)) | ~v2_funct_1(C_117) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), C_117)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_117, k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_117))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_314, c_314, c_314, c_652])).
% 3.84/1.64  tff(c_713, plain, (![C_126]: (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1(C_126))) | ~v2_funct_1(k2_funct_1(C_126)) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1(C_126))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1(C_126), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(C_126)) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_126)!=k2_relat_1('#skF_3') | ~v2_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_126, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_126))), inference(resolution, [status(thm)], [c_26, c_661])).
% 3.84/1.64  tff(c_720, plain, (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_713])).
% 3.84/1.64  tff(c_724, plain, (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_42, c_308, c_377, c_384, c_542, c_638, c_720])).
% 3.84/1.64  tff(c_725, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_724])).
% 3.84/1.64  tff(c_728, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_725])).
% 3.84/1.64  tff(c_732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_50, c_42, c_728])).
% 3.84/1.64  tff(c_734, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_724])).
% 3.84/1.64  tff(c_735, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_734, c_542])).
% 3.84/1.64  tff(c_36, plain, (![A_27, B_28, C_29]: (k2_tops_2(A_27, B_28, C_29)=k2_funct_1(C_29) | ~v2_funct_1(C_29) | k2_relset_1(A_27, B_28, C_29)!=B_28 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.84/1.64  tff(c_902, plain, (![B_135, A_136, C_137]: (k2_tops_2(B_135, A_136, k2_funct_1(C_137))=k2_funct_1(k2_funct_1(C_137)) | ~v2_funct_1(k2_funct_1(C_137)) | k2_relset_1(B_135, A_136, k2_funct_1(C_137))!=A_136 | ~v1_funct_2(k2_funct_1(C_137), B_135, A_136) | ~v1_funct_1(k2_funct_1(C_137)) | k2_relset_1(A_136, B_135, C_137)!=B_135 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))) | ~v1_funct_2(C_137, A_136, B_135) | ~v1_funct_1(C_137))), inference(resolution, [status(thm)], [c_404, c_36])).
% 3.84/1.64  tff(c_908, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_310, c_902])).
% 3.84/1.64  tff(c_912, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311, c_42, c_308, c_377, c_384, c_735, c_638, c_908])).
% 3.84/1.64  tff(c_40, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.84/1.64  tff(c_105, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_65, c_64, c_64, c_64, c_40])).
% 3.84/1.64  tff(c_219, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_216, c_105])).
% 3.84/1.64  tff(c_309, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_303, c_303, c_219])).
% 3.84/1.64  tff(c_392, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_309])).
% 3.84/1.64  tff(c_914, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_912, c_392])).
% 3.84/1.64  tff(c_926, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_914])).
% 3.84/1.64  tff(c_929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_50, c_42, c_503, c_926])).
% 3.84/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.64  
% 3.84/1.64  Inference rules
% 3.84/1.64  ----------------------
% 3.84/1.64  #Ref     : 0
% 3.84/1.64  #Sup     : 188
% 3.84/1.64  #Fact    : 0
% 3.84/1.64  #Define  : 0
% 3.84/1.64  #Split   : 6
% 3.84/1.64  #Chain   : 0
% 3.84/1.64  #Close   : 0
% 3.84/1.64  
% 3.84/1.64  Ordering : KBO
% 3.84/1.64  
% 3.84/1.64  Simplification rules
% 3.84/1.64  ----------------------
% 3.84/1.64  #Subsume      : 10
% 3.84/1.64  #Demod        : 316
% 3.84/1.64  #Tautology    : 88
% 3.84/1.64  #SimpNegUnit  : 6
% 3.84/1.64  #BackRed      : 29
% 3.84/1.64  
% 3.84/1.64  #Partial instantiations: 0
% 3.84/1.64  #Strategies tried      : 1
% 3.84/1.64  
% 3.84/1.64  Timing (in seconds)
% 3.84/1.64  ----------------------
% 3.84/1.64  Preprocessing        : 0.37
% 3.84/1.64  Parsing              : 0.20
% 3.84/1.64  CNF conversion       : 0.02
% 3.84/1.64  Main loop            : 0.47
% 3.84/1.64  Inferencing          : 0.16
% 3.84/1.64  Reduction            : 0.16
% 3.84/1.64  Demodulation         : 0.12
% 3.84/1.64  BG Simplification    : 0.03
% 3.84/1.64  Subsumption          : 0.08
% 3.84/1.64  Abstraction          : 0.02
% 3.84/1.64  MUC search           : 0.00
% 3.84/1.64  Cooper               : 0.00
% 3.84/1.64  Total                : 0.90
% 3.84/1.64  Index Insertion      : 0.00
% 3.84/1.64  Index Deletion       : 0.00
% 3.84/1.64  Index Matching       : 0.00
% 3.84/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
