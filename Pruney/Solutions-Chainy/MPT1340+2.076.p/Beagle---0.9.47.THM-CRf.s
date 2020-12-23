%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:41 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  145 (14917 expanded)
%              Number of leaves         :   42 (5201 expanded)
%              Depth                    :   22
%              Number of atoms          :  373 (42547 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_178,negated_conjecture,(
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

tff(f_118,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_114,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_156,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_60])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_67,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_97,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_48])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_168,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_168])).

tff(c_46,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_92,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_46])).

tff(c_173,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_92])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_78,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_78])).

tff(c_88,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_84])).

tff(c_89,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_88])).

tff(c_182,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_89])).

tff(c_110,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_97,c_110])).

tff(c_133,plain,(
    ! [B_57,A_58] :
      ( k1_relat_1(B_57) = A_58
      | ~ v1_partfun1(B_57,A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_136,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_133])).

tff(c_139,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_136])).

tff(c_140,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_77,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_50])).

tff(c_183,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_77])).

tff(c_181,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_97])).

tff(c_18,plain,(
    ! [C_17,A_14,B_15] :
      ( v1_partfun1(C_17,A_14)
      | ~ v1_funct_2(C_17,A_14,B_15)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | v1_xboole_0(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_202,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_181,c_18])).

tff(c_217,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_183,c_202])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_140,c_217])).

tff(c_220,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_224,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_97])).

tff(c_303,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_307,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_224,c_303])).

tff(c_225,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_92])).

tff(c_308,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_225])).

tff(c_227,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_77])).

tff(c_316,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_227])).

tff(c_315,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_224])).

tff(c_470,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( r2_funct_2(A_95,B_96,C_97,C_97)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(D_98,A_95,B_96)
      | ~ v1_funct_1(D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_97,A_95,B_96)
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_474,plain,(
    ! [C_97] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_97,C_97)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_97,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_315,c_470])).

tff(c_519,plain,(
    ! [C_99] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_99,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_99,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_474])).

tff(c_524,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_519])).

tff(c_528,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_524])).

tff(c_10,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_313,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_307])).

tff(c_377,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_funct_1(k2_funct_1(C_76))
      | k2_relset_1(A_77,B_78,C_76) != B_78
      | ~ v2_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(C_76,A_77,B_78)
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_380,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_377])).

tff(c_383,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_44,c_313,c_380])).

tff(c_384,plain,(
    ! [C_79,B_80,A_81] :
      ( v1_funct_2(k2_funct_1(C_79),B_80,A_81)
      | k2_relset_1(A_81,B_80,C_79) != B_80
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_2(C_79,A_81,B_80)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_387,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_384])).

tff(c_390,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_44,c_313,c_387])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_410,plain,(
    ! [C_86,B_87,A_88] :
      ( m1_subset_1(k2_funct_1(C_86),k1_zfmisc_1(k2_zfmisc_1(B_87,A_88)))
      | k2_relset_1(A_88,B_87,C_86) != B_87
      | ~ v2_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87)))
      | ~ v1_funct_2(C_86,A_88,B_87)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_540,plain,(
    ! [B_103,A_104,C_105] :
      ( k2_relset_1(B_103,A_104,k2_funct_1(C_105)) = k2_relat_1(k2_funct_1(C_105))
      | k2_relset_1(A_104,B_103,C_105) != B_103
      | ~ v2_funct_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_2(C_105,A_104,B_103)
      | ~ v1_funct_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_410,c_16])).

tff(c_546,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_540])).

tff(c_550,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_44,c_313,c_546])).

tff(c_391,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_tops_2(A_82,B_83,C_84) = k2_funct_1(C_84)
      | ~ v2_funct_1(C_84)
      | k2_relset_1(A_82,B_83,C_84) != B_83
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(C_84,A_82,B_83)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_394,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_391])).

tff(c_397,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_313,c_44,c_394])).

tff(c_319,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_67])).

tff(c_228,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_68])).

tff(c_555,plain,(
    ! [A_106,B_107,C_108] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_106),u1_struct_0(B_107),C_108))
      | ~ v2_funct_1(C_108)
      | k2_relset_1(u1_struct_0(A_106),u1_struct_0(B_107),C_108) != k2_struct_0(B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106),u1_struct_0(B_107))))
      | ~ v1_funct_2(C_108,u1_struct_0(A_106),u1_struct_0(B_107))
      | ~ v1_funct_1(C_108)
      | ~ l1_struct_0(B_107)
      | ~ l1_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_568,plain,(
    ! [B_107,C_108] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_107),C_108))
      | ~ v2_funct_1(C_108)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_107),C_108) != k2_struct_0(B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_107))))
      | ~ v1_funct_2(C_108,u1_struct_0('#skF_1'),u1_struct_0(B_107))
      | ~ v1_funct_1(C_108)
      | ~ l1_struct_0(B_107)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_555])).

tff(c_619,plain,(
    ! [B_114,C_115] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0(B_114),C_115))
      | ~ v2_funct_1(C_115)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0(B_114),C_115) != k2_struct_0(B_114)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),u1_struct_0(B_114))))
      | ~ v1_funct_2(C_115,k1_relat_1('#skF_3'),u1_struct_0(B_114))
      | ~ v1_funct_1(C_115)
      | ~ l1_struct_0(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_228,c_228,c_228,c_568])).

tff(c_626,plain,(
    ! [C_115] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_115))
      | ~ v2_funct_1(C_115)
      | k2_relset_1(k1_relat_1('#skF_3'),u1_struct_0('#skF_2'),C_115) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_115,k1_relat_1('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_115)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_619])).

tff(c_635,plain,(
    ! [C_116] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_116))
      | ~ v2_funct_1(C_116)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_116) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_116,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_319,c_319,c_308,c_319,c_626])).

tff(c_642,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_635])).

tff(c_646,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_313,c_44,c_397,c_642])).

tff(c_28,plain,(
    ! [C_26,B_25,A_24] :
      ( m1_subset_1(k2_funct_1(C_26),k1_zfmisc_1(k2_zfmisc_1(B_25,A_24)))
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_571,plain,(
    ! [A_106,C_108] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_106),u1_struct_0('#skF_1'),C_108))
      | ~ v2_funct_1(C_108)
      | k2_relset_1(u1_struct_0(A_106),u1_struct_0('#skF_1'),C_108) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_108,u1_struct_0(A_106),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_108)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_555])).

tff(c_653,plain,(
    ! [A_118,C_119] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_118),k1_relat_1('#skF_3'),C_119))
      | ~ v2_funct_1(C_119)
      | k2_relset_1(u1_struct_0(A_118),k1_relat_1('#skF_3'),C_119) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_118),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_119)
      | ~ l1_struct_0(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_228,c_228,c_220,c_228,c_571])).

tff(c_660,plain,(
    ! [C_119] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_119))
      | ~ v2_funct_1(C_119)
      | k2_relset_1(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_119) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_119,u1_struct_0('#skF_2'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_119)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_653])).

tff(c_669,plain,(
    ! [C_120] :
      ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),C_120))
      | ~ v2_funct_1(C_120)
      | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),C_120) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_120,k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_319,c_319,c_319,c_660])).

tff(c_721,plain,(
    ! [C_129] :
      ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1(C_129)))
      | ~ v2_funct_1(k2_funct_1(C_129))
      | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1(C_129)) != k1_relat_1('#skF_3')
      | ~ v1_funct_2(k2_funct_1(C_129),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1(C_129))
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_129) != k2_relat_1('#skF_3')
      | ~ v2_funct_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_129,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_28,c_669])).

tff(c_728,plain,
    ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_721])).

tff(c_732,plain,
    ( v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_44,c_313,c_383,c_390,c_550,c_646,c_728])).

tff(c_733,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_736,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_733])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_52,c_44,c_736])).

tff(c_742,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_743,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_550])).

tff(c_38,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_tops_2(A_29,B_30,C_31) = k2_funct_1(C_31)
      | ~ v2_funct_1(C_31)
      | k2_relset_1(A_29,B_30,C_31) != B_30
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_910,plain,(
    ! [B_138,A_139,C_140] :
      ( k2_tops_2(B_138,A_139,k2_funct_1(C_140)) = k2_funct_1(k2_funct_1(C_140))
      | ~ v2_funct_1(k2_funct_1(C_140))
      | k2_relset_1(B_138,A_139,k2_funct_1(C_140)) != A_139
      | ~ v1_funct_2(k2_funct_1(C_140),B_138,A_139)
      | ~ v1_funct_1(k2_funct_1(C_140))
      | k2_relset_1(A_139,B_138,C_140) != B_138
      | ~ v2_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_2(C_140,A_139,B_138)
      | ~ v1_funct_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_410,c_38])).

tff(c_916,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_315,c_910])).

tff(c_920,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_316,c_44,c_313,c_383,c_390,c_743,c_646,c_916])).

tff(c_42,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_109,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_67,c_67,c_67,c_42])).

tff(c_223,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_220,c_220,c_109])).

tff(c_314,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_308,c_308,c_223])).

tff(c_398,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_314])).

tff(c_922,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_398])).

tff(c_934,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_922])).

tff(c_937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_52,c_44,c_528,c_934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:04:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.64  
% 3.42/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.64  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.42/1.64  
% 3.42/1.64  %Foreground sorts:
% 3.42/1.64  
% 3.42/1.64  
% 3.42/1.64  %Background operators:
% 3.42/1.64  
% 3.42/1.64  
% 3.42/1.64  %Foreground operators:
% 3.42/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.42/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.42/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.42/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.42/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.64  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.42/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.42/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.42/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.42/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.42/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.42/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.42/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.42/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.64  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.42/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.64  
% 3.80/1.67  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.80/1.67  tff(f_178, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.80/1.67  tff(f_118, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.80/1.67  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.80/1.67  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.80/1.67  tff(f_126, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.80/1.67  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.80/1.67  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.80/1.67  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.80/1.67  tff(f_98, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.80/1.67  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.80/1.67  tff(f_114, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.80/1.67  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.80/1.67  tff(f_138, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.80/1.67  tff(f_156, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 3.80/1.67  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.80/1.67  tff(c_58, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_60, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.80/1.67  tff(c_68, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_60])).
% 3.80/1.67  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_67, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_60])).
% 3.80/1.67  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_97, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_48])).
% 3.80/1.67  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.67  tff(c_100, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_97, c_2])).
% 3.80/1.67  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 3.80/1.67  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_168, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/1.67  tff(c_172, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_97, c_168])).
% 3.80/1.67  tff(c_46, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_92, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_46])).
% 3.80/1.67  tff(c_173, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_92])).
% 3.80/1.67  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_78, plain, (![A_46]: (~v1_xboole_0(u1_struct_0(A_46)) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.67  tff(c_84, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_67, c_78])).
% 3.80/1.67  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_84])).
% 3.80/1.67  tff(c_89, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_88])).
% 3.80/1.67  tff(c_182, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_89])).
% 3.80/1.67  tff(c_110, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.67  tff(c_114, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_97, c_110])).
% 3.80/1.67  tff(c_133, plain, (![B_57, A_58]: (k1_relat_1(B_57)=A_58 | ~v1_partfun1(B_57, A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.80/1.67  tff(c_136, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_133])).
% 3.80/1.67  tff(c_139, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_136])).
% 3.80/1.67  tff(c_140, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 3.80/1.67  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_77, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_50])).
% 3.80/1.67  tff(c_183, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_77])).
% 3.80/1.67  tff(c_181, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_97])).
% 3.80/1.67  tff(c_18, plain, (![C_17, A_14, B_15]: (v1_partfun1(C_17, A_14) | ~v1_funct_2(C_17, A_14, B_15) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | v1_xboole_0(B_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.67  tff(c_202, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_181, c_18])).
% 3.80/1.67  tff(c_217, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_183, c_202])).
% 3.80/1.67  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_140, c_217])).
% 3.80/1.67  tff(c_220, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_139])).
% 3.80/1.67  tff(c_224, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_97])).
% 3.80/1.67  tff(c_303, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/1.67  tff(c_307, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_224, c_303])).
% 3.80/1.67  tff(c_225, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_92])).
% 3.80/1.67  tff(c_308, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_225])).
% 3.80/1.67  tff(c_227, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_77])).
% 3.80/1.67  tff(c_316, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_227])).
% 3.80/1.67  tff(c_315, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_224])).
% 3.80/1.67  tff(c_470, plain, (![A_95, B_96, C_97, D_98]: (r2_funct_2(A_95, B_96, C_97, C_97) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(D_98, A_95, B_96) | ~v1_funct_1(D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_97, A_95, B_96) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.80/1.67  tff(c_474, plain, (![C_97]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_97, C_97) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_97, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_97))), inference(resolution, [status(thm)], [c_315, c_470])).
% 3.80/1.67  tff(c_519, plain, (![C_99]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_99, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_99, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_474])).
% 3.80/1.67  tff(c_524, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_519])).
% 3.80/1.67  tff(c_528, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_524])).
% 3.80/1.67  tff(c_10, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.80/1.67  tff(c_313, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_307])).
% 3.80/1.67  tff(c_377, plain, (![C_76, A_77, B_78]: (v1_funct_1(k2_funct_1(C_76)) | k2_relset_1(A_77, B_78, C_76)!=B_78 | ~v2_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(C_76, A_77, B_78) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.80/1.67  tff(c_380, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_377])).
% 3.80/1.67  tff(c_383, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_44, c_313, c_380])).
% 3.80/1.67  tff(c_384, plain, (![C_79, B_80, A_81]: (v1_funct_2(k2_funct_1(C_79), B_80, A_81) | k2_relset_1(A_81, B_80, C_79)!=B_80 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.80/1.67  tff(c_387, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_384])).
% 3.80/1.67  tff(c_390, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_44, c_313, c_387])).
% 3.80/1.67  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.80/1.67  tff(c_410, plain, (![C_86, B_87, A_88]: (m1_subset_1(k2_funct_1(C_86), k1_zfmisc_1(k2_zfmisc_1(B_87, A_88))) | k2_relset_1(A_88, B_87, C_86)!=B_87 | ~v2_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))) | ~v1_funct_2(C_86, A_88, B_87) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.80/1.67  tff(c_16, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/1.67  tff(c_540, plain, (![B_103, A_104, C_105]: (k2_relset_1(B_103, A_104, k2_funct_1(C_105))=k2_relat_1(k2_funct_1(C_105)) | k2_relset_1(A_104, B_103, C_105)!=B_103 | ~v2_funct_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_2(C_105, A_104, B_103) | ~v1_funct_1(C_105))), inference(resolution, [status(thm)], [c_410, c_16])).
% 3.80/1.67  tff(c_546, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_540])).
% 3.80/1.67  tff(c_550, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_44, c_313, c_546])).
% 3.80/1.67  tff(c_391, plain, (![A_82, B_83, C_84]: (k2_tops_2(A_82, B_83, C_84)=k2_funct_1(C_84) | ~v2_funct_1(C_84) | k2_relset_1(A_82, B_83, C_84)!=B_83 | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(C_84, A_82, B_83) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.80/1.67  tff(c_394, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_391])).
% 3.80/1.67  tff(c_397, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_313, c_44, c_394])).
% 3.80/1.67  tff(c_319, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_67])).
% 3.80/1.67  tff(c_228, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_68])).
% 3.80/1.67  tff(c_555, plain, (![A_106, B_107, C_108]: (v2_funct_1(k2_tops_2(u1_struct_0(A_106), u1_struct_0(B_107), C_108)) | ~v2_funct_1(C_108) | k2_relset_1(u1_struct_0(A_106), u1_struct_0(B_107), C_108)!=k2_struct_0(B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106), u1_struct_0(B_107)))) | ~v1_funct_2(C_108, u1_struct_0(A_106), u1_struct_0(B_107)) | ~v1_funct_1(C_108) | ~l1_struct_0(B_107) | ~l1_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.80/1.67  tff(c_568, plain, (![B_107, C_108]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_107), C_108)) | ~v2_funct_1(C_108) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_107), C_108)!=k2_struct_0(B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_107)))) | ~v1_funct_2(C_108, u1_struct_0('#skF_1'), u1_struct_0(B_107)) | ~v1_funct_1(C_108) | ~l1_struct_0(B_107) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_555])).
% 3.80/1.67  tff(c_619, plain, (![B_114, C_115]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0(B_114), C_115)) | ~v2_funct_1(C_115) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0(B_114), C_115)!=k2_struct_0(B_114) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), u1_struct_0(B_114)))) | ~v1_funct_2(C_115, k1_relat_1('#skF_3'), u1_struct_0(B_114)) | ~v1_funct_1(C_115) | ~l1_struct_0(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_228, c_228, c_228, c_568])).
% 3.80/1.67  tff(c_626, plain, (![C_115]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_115)) | ~v2_funct_1(C_115) | k2_relset_1(k1_relat_1('#skF_3'), u1_struct_0('#skF_2'), C_115)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_115, k1_relat_1('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_115) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_619])).
% 3.80/1.67  tff(c_635, plain, (![C_116]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_116)) | ~v2_funct_1(C_116) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_116)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_116, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_116))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_319, c_319, c_308, c_319, c_626])).
% 3.80/1.67  tff(c_642, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_635])).
% 3.80/1.67  tff(c_646, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_313, c_44, c_397, c_642])).
% 3.80/1.67  tff(c_28, plain, (![C_26, B_25, A_24]: (m1_subset_1(k2_funct_1(C_26), k1_zfmisc_1(k2_zfmisc_1(B_25, A_24))) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.80/1.67  tff(c_571, plain, (![A_106, C_108]: (v2_funct_1(k2_tops_2(u1_struct_0(A_106), u1_struct_0('#skF_1'), C_108)) | ~v2_funct_1(C_108) | k2_relset_1(u1_struct_0(A_106), u1_struct_0('#skF_1'), C_108)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_108, u1_struct_0(A_106), u1_struct_0('#skF_1')) | ~v1_funct_1(C_108) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_106))), inference(superposition, [status(thm), theory('equality')], [c_228, c_555])).
% 3.80/1.67  tff(c_653, plain, (![A_118, C_119]: (v2_funct_1(k2_tops_2(u1_struct_0(A_118), k1_relat_1('#skF_3'), C_119)) | ~v2_funct_1(C_119) | k2_relset_1(u1_struct_0(A_118), k1_relat_1('#skF_3'), C_119)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_119, u1_struct_0(A_118), k1_relat_1('#skF_3')) | ~v1_funct_1(C_119) | ~l1_struct_0(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_228, c_228, c_220, c_228, c_571])).
% 3.80/1.67  tff(c_660, plain, (![C_119]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_119)) | ~v2_funct_1(C_119) | k2_relset_1(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_119)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_119, u1_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_119) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_653])).
% 3.80/1.67  tff(c_669, plain, (![C_120]: (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), C_120)) | ~v2_funct_1(C_120) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), C_120)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_120, k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_120))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_319, c_319, c_319, c_660])).
% 3.80/1.67  tff(c_721, plain, (![C_129]: (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1(C_129))) | ~v2_funct_1(k2_funct_1(C_129)) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1(C_129))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1(C_129), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(C_129)) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_129)!=k2_relat_1('#skF_3') | ~v2_funct_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_129, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_129))), inference(resolution, [status(thm)], [c_28, c_669])).
% 3.80/1.67  tff(c_728, plain, (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_721])).
% 3.80/1.67  tff(c_732, plain, (v2_funct_1(k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_44, c_313, c_383, c_390, c_550, c_646, c_728])).
% 3.80/1.67  tff(c_733, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_732])).
% 3.80/1.67  tff(c_736, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_733])).
% 3.80/1.67  tff(c_740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_52, c_44, c_736])).
% 3.80/1.67  tff(c_742, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_732])).
% 3.80/1.67  tff(c_743, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_742, c_550])).
% 3.80/1.67  tff(c_38, plain, (![A_29, B_30, C_31]: (k2_tops_2(A_29, B_30, C_31)=k2_funct_1(C_31) | ~v2_funct_1(C_31) | k2_relset_1(A_29, B_30, C_31)!=B_30 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.80/1.67  tff(c_910, plain, (![B_138, A_139, C_140]: (k2_tops_2(B_138, A_139, k2_funct_1(C_140))=k2_funct_1(k2_funct_1(C_140)) | ~v2_funct_1(k2_funct_1(C_140)) | k2_relset_1(B_138, A_139, k2_funct_1(C_140))!=A_139 | ~v1_funct_2(k2_funct_1(C_140), B_138, A_139) | ~v1_funct_1(k2_funct_1(C_140)) | k2_relset_1(A_139, B_138, C_140)!=B_138 | ~v2_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_2(C_140, A_139, B_138) | ~v1_funct_1(C_140))), inference(resolution, [status(thm)], [c_410, c_38])).
% 3.80/1.67  tff(c_916, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_315, c_910])).
% 3.80/1.67  tff(c_920, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_316, c_44, c_313, c_383, c_390, c_743, c_646, c_916])).
% 3.80/1.67  tff(c_42, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.80/1.67  tff(c_109, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_67, c_67, c_67, c_42])).
% 3.80/1.67  tff(c_223, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_220, c_220, c_109])).
% 3.80/1.67  tff(c_314, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_308, c_308, c_223])).
% 3.80/1.67  tff(c_398, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_314])).
% 3.80/1.67  tff(c_922, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_920, c_398])).
% 3.80/1.67  tff(c_934, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_922])).
% 3.80/1.67  tff(c_937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_52, c_44, c_528, c_934])).
% 3.80/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.67  
% 3.80/1.67  Inference rules
% 3.80/1.67  ----------------------
% 3.80/1.67  #Ref     : 0
% 3.80/1.67  #Sup     : 188
% 3.80/1.67  #Fact    : 0
% 3.80/1.67  #Define  : 0
% 3.80/1.67  #Split   : 6
% 3.80/1.67  #Chain   : 0
% 3.80/1.67  #Close   : 0
% 3.80/1.67  
% 3.80/1.67  Ordering : KBO
% 3.80/1.67  
% 3.80/1.67  Simplification rules
% 3.80/1.67  ----------------------
% 3.80/1.67  #Subsume      : 10
% 3.80/1.67  #Demod        : 320
% 3.80/1.67  #Tautology    : 88
% 3.80/1.67  #SimpNegUnit  : 6
% 3.80/1.67  #BackRed      : 28
% 3.80/1.67  
% 3.80/1.67  #Partial instantiations: 0
% 3.80/1.67  #Strategies tried      : 1
% 3.80/1.67  
% 3.80/1.67  Timing (in seconds)
% 3.80/1.67  ----------------------
% 3.80/1.67  Preprocessing        : 0.38
% 3.80/1.67  Parsing              : 0.21
% 3.80/1.67  CNF conversion       : 0.02
% 3.80/1.67  Main loop            : 0.45
% 3.80/1.67  Inferencing          : 0.16
% 3.80/1.67  Reduction            : 0.16
% 3.80/1.67  Demodulation         : 0.11
% 3.80/1.67  BG Simplification    : 0.03
% 3.80/1.67  Subsumption          : 0.08
% 3.80/1.67  Abstraction          : 0.02
% 3.80/1.67  MUC search           : 0.00
% 3.80/1.67  Cooper               : 0.00
% 3.80/1.67  Total                : 0.89
% 3.80/1.67  Index Insertion      : 0.00
% 3.80/1.67  Index Deletion       : 0.00
% 3.80/1.67  Index Matching       : 0.00
% 3.80/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
