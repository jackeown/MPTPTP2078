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

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  138 (12814 expanded)
%              Number of leaves         :   41 (4474 expanded)
%              Depth                    :   22
%              Number of atoms          :  339 (37117 expanded)
%              Number of equality atoms :   72 (8443 expanded)
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
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

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

tff(c_78,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_78])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_152,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_152])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_83,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_44])).

tff(c_157,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_83])).

tff(c_34,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k2_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_171,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_34])).

tff(c_175,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_171])).

tff(c_176,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_175])).

tff(c_88,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_75,c_88])).

tff(c_117,plain,(
    ! [B_54,A_55] :
      ( k1_relat_1(B_54) = A_55
      | ~ v1_partfun1(B_54,A_55)
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_117])).

tff(c_123,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_120])).

tff(c_124,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_66])).

tff(c_165,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_76])).

tff(c_166,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_75])).

tff(c_16,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_partfun1(C_15,A_12)
      | ~ v1_funct_2(C_15,A_12,B_13)
      | ~ v1_funct_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_189,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_166,c_16])).

tff(c_204,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165,c_189])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_124,c_204])).

tff(c_207,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_213,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_75])).

tff(c_289,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_293,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_213,c_289])).

tff(c_211,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_83])).

tff(c_294,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_211])).

tff(c_212,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_76])).

tff(c_302,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_212])).

tff(c_301,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_213])).

tff(c_456,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( r2_funct_2(A_94,B_95,C_96,C_96)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(D_97,A_94,B_95)
      | ~ v1_funct_1(D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_460,plain,(
    ! [C_96] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_96,C_96)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_96,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_301,c_456])).

tff(c_553,plain,(
    ! [C_103] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_103,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_103,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_460])).

tff(c_558,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_553])).

tff(c_562,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_558])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_299,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_293])).

tff(c_361,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_funct_1(k2_funct_1(C_73))
      | k2_relset_1(A_74,B_75,C_73) != B_75
      | ~ v2_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_364,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_361])).

tff(c_367,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_42,c_299,c_364])).

tff(c_368,plain,(
    ! [C_76,B_77,A_78] :
      ( v1_funct_2(k2_funct_1(C_76),B_77,A_78)
      | k2_relset_1(A_78,B_77,C_76) != B_77
      | ~ v2_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77)))
      | ~ v1_funct_2(C_76,A_78,B_77)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_371,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_368])).

tff(c_374,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_42,c_299,c_371])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_375,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_tops_2(A_79,B_80,C_81) = k2_funct_1(C_81)
      | ~ v2_funct_1(C_81)
      | k2_relset_1(A_79,B_80,C_81) != B_80
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(C_81,A_79,B_80)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_378,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_375])).

tff(c_381,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_299,c_42,c_378])).

tff(c_304,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_64])).

tff(c_214,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_65])).

tff(c_526,plain,(
    ! [A_100,B_101,C_102] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_100),u1_struct_0(B_101),C_102))
      | ~ v2_funct_1(C_102)
      | k2_relset_1(u1_struct_0(A_100),u1_struct_0(B_101),C_102) != k2_struct_0(B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_100),u1_struct_0(B_101))))
      | ~ v1_funct_2(C_102,u1_struct_0(A_100),u1_struct_0(B_101))
      | ~ v1_funct_1(C_102)
      | ~ l1_struct_0(B_101)
      | ~ l1_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_539,plain,(
    ! [B_101,C_102] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_101),C_102))
      | ~ v2_funct_1(C_102)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_101),C_102) != k2_struct_0(B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_101))))
      | ~ v1_funct_2(C_102,u1_struct_0('#skF_1'),u1_struct_0(B_101))
      | ~ v1_funct_1(C_102)
      | ~ l1_struct_0(B_101)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_526])).

tff(c_563,plain,(
    ! [B_104,C_105] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0(B_104),C_105))
      | ~ v2_funct_1(C_105)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0(B_104),C_105) != k2_struct_0(B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,k1_relat_1('#skF_3'),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_struct_0(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_214,c_214,c_214,c_539])).

tff(c_570,plain,(
    ! [C_105] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_105))
      | ~ v2_funct_1(C_105)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_105) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_105,k1_relat_1('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_105)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_563])).

tff(c_645,plain,(
    ! [C_115] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_115))
      | ~ v2_funct_1(C_115)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_115) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_115,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_304,c_294,c_304,c_304,c_570])).

tff(c_652,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_645])).

tff(c_656,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_299,c_42,c_381,c_652])).

tff(c_387,plain,(
    ! [C_82,B_83,A_84] :
      ( m1_subset_1(k2_funct_1(C_82),k1_zfmisc_1(k2_zfmisc_1(B_83,A_84)))
      | k2_relset_1(A_84,B_83,C_82) != B_83
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83)))
      | ~ v1_funct_2(C_82,A_84,B_83)
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_592,plain,(
    ! [B_107,A_108,C_109] :
      ( k2_relset_1(B_107,A_108,k2_funct_1(C_109)) = k2_relat_1(k2_funct_1(C_109))
      | k2_relset_1(A_108,B_107,C_109) != B_107
      | ~ v2_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ v1_funct_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_387,c_14])).

tff(c_598,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_592])).

tff(c_602,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_42,c_299,c_598])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_funct_1(k2_funct_1(C_24))
      | k2_relset_1(A_22,B_23,C_24) != B_23
      | ~ v2_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_731,plain,(
    ! [C_128,B_129,A_130] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_128)))
      | k2_relset_1(B_129,A_130,k2_funct_1(C_128)) != A_130
      | ~ v2_funct_1(k2_funct_1(C_128))
      | ~ v1_funct_2(k2_funct_1(C_128),B_129,A_130)
      | ~ v1_funct_1(k2_funct_1(C_128))
      | k2_relset_1(A_130,B_129,C_128) != B_129
      | ~ v2_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_2(C_128,A_130,B_129)
      | ~ v1_funct_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_387,c_30])).

tff(c_737,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_731])).

tff(c_741,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_42,c_299,c_367,c_374,c_656,c_602,c_737])).

tff(c_742,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_745,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_742])).

tff(c_749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_50,c_42,c_745])).

tff(c_751,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_763,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_602])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_tops_2(A_27,B_28,C_29) = k2_funct_1(C_29)
      | ~ v2_funct_1(C_29)
      | k2_relset_1(A_27,B_28,C_29) != B_28
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

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
    inference(resolution,[status(thm)],[c_387,c_36])).

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
    inference(resolution,[status(thm)],[c_301,c_983])).

tff(c_993,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_42,c_299,c_367,c_374,c_763,c_656,c_989])).

tff(c_40,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_98,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_65,c_64,c_64,c_64,c_40])).

tff(c_209,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_207,c_207,c_98])).

tff(c_300,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_294,c_294,c_209])).

tff(c_382,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_300])).

tff(c_995,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_382])).

tff(c_1003,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_995])).

tff(c_1006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_50,c_42,c_562,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:05:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.58  
% 3.55/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.59  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.55/1.59  
% 3.55/1.59  %Foreground sorts:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Background operators:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Foreground operators:
% 3.55/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.55/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.55/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.55/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.59  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.55/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.55/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.55/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.55/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.55/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.59  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.55/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.59  
% 3.55/1.61  tff(f_173, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.55/1.61  tff(f_113, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.55/1.61  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.55/1.61  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.55/1.61  tff(f_121, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.55/1.61  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.55/1.61  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.55/1.61  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.55/1.61  tff(f_93, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.55/1.61  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.55/1.61  tff(f_109, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.55/1.61  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.55/1.61  tff(f_133, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.55/1.61  tff(f_151, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 3.55/1.61  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_57, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.55/1.61  tff(c_65, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_57])).
% 3.55/1.61  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_57])).
% 3.55/1.61  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_75, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_46])).
% 3.55/1.61  tff(c_78, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.61  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_78])).
% 3.55/1.61  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_152, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.61  tff(c_156, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_152])).
% 3.55/1.61  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_83, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_44])).
% 3.55/1.61  tff(c_157, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_83])).
% 3.55/1.61  tff(c_34, plain, (![A_26]: (~v1_xboole_0(k2_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.55/1.61  tff(c_171, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_157, c_34])).
% 3.55/1.61  tff(c_175, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_171])).
% 3.55/1.61  tff(c_176, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_175])).
% 3.55/1.61  tff(c_88, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.55/1.61  tff(c_92, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_75, c_88])).
% 3.55/1.61  tff(c_117, plain, (![B_54, A_55]: (k1_relat_1(B_54)=A_55 | ~v1_partfun1(B_54, A_55) | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.55/1.61  tff(c_120, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_117])).
% 3.55/1.61  tff(c_123, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_120])).
% 3.55/1.61  tff(c_124, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_123])).
% 3.55/1.61  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_48])).
% 3.55/1.61  tff(c_76, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_66])).
% 3.55/1.61  tff(c_165, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_76])).
% 3.55/1.61  tff(c_166, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_75])).
% 3.55/1.61  tff(c_16, plain, (![C_15, A_12, B_13]: (v1_partfun1(C_15, A_12) | ~v1_funct_2(C_15, A_12, B_13) | ~v1_funct_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.55/1.61  tff(c_189, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_166, c_16])).
% 3.55/1.61  tff(c_204, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165, c_189])).
% 3.55/1.61  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_124, c_204])).
% 3.55/1.61  tff(c_207, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_123])).
% 3.55/1.61  tff(c_213, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_75])).
% 3.55/1.61  tff(c_289, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.61  tff(c_293, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_213, c_289])).
% 3.55/1.61  tff(c_211, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_83])).
% 3.55/1.61  tff(c_294, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_211])).
% 3.55/1.61  tff(c_212, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_76])).
% 3.55/1.61  tff(c_302, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_212])).
% 3.55/1.61  tff(c_301, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_213])).
% 3.55/1.61  tff(c_456, plain, (![A_94, B_95, C_96, D_97]: (r2_funct_2(A_94, B_95, C_96, C_96) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(D_97, A_94, B_95) | ~v1_funct_1(D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.61  tff(c_460, plain, (![C_96]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_96, C_96) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_96, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_96))), inference(resolution, [status(thm)], [c_301, c_456])).
% 3.55/1.61  tff(c_553, plain, (![C_103]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_103, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_103, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_460])).
% 3.55/1.61  tff(c_558, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_553])).
% 3.55/1.61  tff(c_562, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_558])).
% 3.55/1.61  tff(c_6, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.61  tff(c_299, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_293])).
% 3.55/1.61  tff(c_361, plain, (![C_73, A_74, B_75]: (v1_funct_1(k2_funct_1(C_73)) | k2_relset_1(A_74, B_75, C_73)!=B_75 | ~v2_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.55/1.61  tff(c_364, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_361])).
% 3.55/1.61  tff(c_367, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_42, c_299, c_364])).
% 3.55/1.61  tff(c_368, plain, (![C_76, B_77, A_78]: (v1_funct_2(k2_funct_1(C_76), B_77, A_78) | k2_relset_1(A_78, B_77, C_76)!=B_77 | ~v2_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))) | ~v1_funct_2(C_76, A_78, B_77) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.55/1.61  tff(c_371, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_368])).
% 3.55/1.61  tff(c_374, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_42, c_299, c_371])).
% 3.55/1.61  tff(c_2, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.55/1.61  tff(c_375, plain, (![A_79, B_80, C_81]: (k2_tops_2(A_79, B_80, C_81)=k2_funct_1(C_81) | ~v2_funct_1(C_81) | k2_relset_1(A_79, B_80, C_81)!=B_80 | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_2(C_81, A_79, B_80) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.55/1.61  tff(c_378, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_375])).
% 3.55/1.61  tff(c_381, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_299, c_42, c_378])).
% 3.55/1.61  tff(c_304, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_64])).
% 3.55/1.61  tff(c_214, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_65])).
% 3.55/1.61  tff(c_526, plain, (![A_100, B_101, C_102]: (v2_funct_1(k2_tops_2(u1_struct_0(A_100), u1_struct_0(B_101), C_102)) | ~v2_funct_1(C_102) | k2_relset_1(u1_struct_0(A_100), u1_struct_0(B_101), C_102)!=k2_struct_0(B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_100), u1_struct_0(B_101)))) | ~v1_funct_2(C_102, u1_struct_0(A_100), u1_struct_0(B_101)) | ~v1_funct_1(C_102) | ~l1_struct_0(B_101) | ~l1_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.55/1.61  tff(c_539, plain, (![B_101, C_102]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_101), C_102)) | ~v2_funct_1(C_102) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_101), C_102)!=k2_struct_0(B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_101)))) | ~v1_funct_2(C_102, u1_struct_0('#skF_1'), u1_struct_0(B_101)) | ~v1_funct_1(C_102) | ~l1_struct_0(B_101) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_526])).
% 3.55/1.61  tff(c_563, plain, (![B_104, C_105]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0(B_104), C_105)) | ~v2_funct_1(C_105) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0(B_104), C_105)!=k2_struct_0(B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, k1_relat_1('#skF_3'), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_struct_0(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_214, c_214, c_214, c_539])).
% 3.55/1.61  tff(c_570, plain, (![C_105]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_105)) | ~v2_funct_1(C_105) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_105)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_105, k1_relat_1('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_105) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_304, c_563])).
% 3.55/1.61  tff(c_645, plain, (![C_115]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_115)) | ~v2_funct_1(C_115) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_115)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_115, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_304, c_294, c_304, c_304, c_570])).
% 3.55/1.61  tff(c_652, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_645])).
% 3.55/1.61  tff(c_656, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_299, c_42, c_381, c_652])).
% 3.55/1.61  tff(c_387, plain, (![C_82, B_83, A_84]: (m1_subset_1(k2_funct_1(C_82), k1_zfmisc_1(k2_zfmisc_1(B_83, A_84))) | k2_relset_1(A_84, B_83, C_82)!=B_83 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))) | ~v1_funct_2(C_82, A_84, B_83) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.55/1.61  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.61  tff(c_592, plain, (![B_107, A_108, C_109]: (k2_relset_1(B_107, A_108, k2_funct_1(C_109))=k2_relat_1(k2_funct_1(C_109)) | k2_relset_1(A_108, B_107, C_109)!=B_107 | ~v2_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_109, A_108, B_107) | ~v1_funct_1(C_109))), inference(resolution, [status(thm)], [c_387, c_14])).
% 3.55/1.61  tff(c_598, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_592])).
% 3.55/1.61  tff(c_602, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_42, c_299, c_598])).
% 3.55/1.61  tff(c_30, plain, (![C_24, A_22, B_23]: (v1_funct_1(k2_funct_1(C_24)) | k2_relset_1(A_22, B_23, C_24)!=B_23 | ~v2_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.55/1.61  tff(c_731, plain, (![C_128, B_129, A_130]: (v1_funct_1(k2_funct_1(k2_funct_1(C_128))) | k2_relset_1(B_129, A_130, k2_funct_1(C_128))!=A_130 | ~v2_funct_1(k2_funct_1(C_128)) | ~v1_funct_2(k2_funct_1(C_128), B_129, A_130) | ~v1_funct_1(k2_funct_1(C_128)) | k2_relset_1(A_130, B_129, C_128)!=B_129 | ~v2_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(C_128, A_130, B_129) | ~v1_funct_1(C_128))), inference(resolution, [status(thm)], [c_387, c_30])).
% 3.55/1.61  tff(c_737, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_731])).
% 3.55/1.61  tff(c_741, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_42, c_299, c_367, c_374, c_656, c_602, c_737])).
% 3.55/1.61  tff(c_742, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_741])).
% 3.55/1.61  tff(c_745, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_742])).
% 3.55/1.61  tff(c_749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_50, c_42, c_745])).
% 3.55/1.61  tff(c_751, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_741])).
% 3.55/1.61  tff(c_763, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_602])).
% 3.55/1.61  tff(c_36, plain, (![A_27, B_28, C_29]: (k2_tops_2(A_27, B_28, C_29)=k2_funct_1(C_29) | ~v2_funct_1(C_29) | k2_relset_1(A_27, B_28, C_29)!=B_28 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.55/1.61  tff(c_983, plain, (![B_143, A_144, C_145]: (k2_tops_2(B_143, A_144, k2_funct_1(C_145))=k2_funct_1(k2_funct_1(C_145)) | ~v2_funct_1(k2_funct_1(C_145)) | k2_relset_1(B_143, A_144, k2_funct_1(C_145))!=A_144 | ~v1_funct_2(k2_funct_1(C_145), B_143, A_144) | ~v1_funct_1(k2_funct_1(C_145)) | k2_relset_1(A_144, B_143, C_145)!=B_143 | ~v2_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_2(C_145, A_144, B_143) | ~v1_funct_1(C_145))), inference(resolution, [status(thm)], [c_387, c_36])).
% 3.55/1.61  tff(c_989, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_983])).
% 3.55/1.61  tff(c_993, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_42, c_299, c_367, c_374, c_763, c_656, c_989])).
% 3.55/1.61  tff(c_40, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.55/1.61  tff(c_98, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_65, c_64, c_64, c_64, c_40])).
% 3.55/1.61  tff(c_209, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_207, c_207, c_98])).
% 3.55/1.61  tff(c_300, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_294, c_294, c_209])).
% 3.55/1.61  tff(c_382, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_300])).
% 3.55/1.61  tff(c_995, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_993, c_382])).
% 3.55/1.61  tff(c_1003, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_995])).
% 3.55/1.61  tff(c_1006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_50, c_42, c_562, c_1003])).
% 3.55/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.61  
% 3.55/1.61  Inference rules
% 3.55/1.61  ----------------------
% 3.55/1.61  #Ref     : 0
% 3.55/1.61  #Sup     : 207
% 3.55/1.61  #Fact    : 0
% 3.55/1.61  #Define  : 0
% 3.55/1.61  #Split   : 8
% 3.55/1.61  #Chain   : 0
% 3.55/1.61  #Close   : 0
% 3.55/1.61  
% 3.55/1.61  Ordering : KBO
% 3.55/1.61  
% 3.55/1.61  Simplification rules
% 3.55/1.61  ----------------------
% 3.55/1.61  #Subsume      : 7
% 3.55/1.61  #Demod        : 353
% 3.55/1.61  #Tautology    : 93
% 3.55/1.61  #SimpNegUnit  : 6
% 3.55/1.61  #BackRed      : 25
% 3.55/1.61  
% 3.55/1.61  #Partial instantiations: 0
% 3.55/1.61  #Strategies tried      : 1
% 3.55/1.61  
% 3.55/1.61  Timing (in seconds)
% 3.55/1.61  ----------------------
% 3.55/1.61  Preprocessing        : 0.35
% 3.55/1.61  Parsing              : 0.19
% 3.55/1.61  CNF conversion       : 0.02
% 3.55/1.61  Main loop            : 0.49
% 3.55/1.61  Inferencing          : 0.17
% 3.55/1.61  Reduction            : 0.16
% 3.55/1.61  Demodulation         : 0.12
% 3.55/1.61  BG Simplification    : 0.03
% 3.55/1.61  Subsumption          : 0.09
% 3.55/1.61  Abstraction          : 0.03
% 3.55/1.61  MUC search           : 0.00
% 3.89/1.61  Cooper               : 0.00
% 3.89/1.61  Total                : 0.89
% 3.89/1.61  Index Insertion      : 0.00
% 3.89/1.61  Index Deletion       : 0.00
% 3.89/1.61  Index Matching       : 0.00
% 3.89/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
