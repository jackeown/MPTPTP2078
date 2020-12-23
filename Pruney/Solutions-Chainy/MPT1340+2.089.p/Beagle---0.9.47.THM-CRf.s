%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:43 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  169 (41056 expanded)
%              Number of leaves         :   39 (14610 expanded)
%              Depth                    :   25
%              Number of atoms          :  353 (121497 expanded)
%              Number of equality atoms :  102 (33287 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_190,negated_conjecture,(
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

tff(f_126,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_106,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_122,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_74,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_82,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_74])).

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_81,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_74])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_62])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_101])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_159,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_163,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_159])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_92,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_60])).

tff(c_164,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_92])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_91,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_64])).

tff(c_172,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_91])).

tff(c_171,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_98])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_192,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_18])).

tff(c_216,plain,(
    ! [B_70,A_71,C_72] :
      ( k1_xboole_0 = B_70
      | k1_relset_1(A_71,B_70,C_72) = A_71
      | ~ v1_funct_2(C_72,A_71,B_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_219,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_171,c_216])).

tff(c_222,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_192,c_219])).

tff(c_223,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_210,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_funct_2(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(D_69,A_67,B_68)
      | ~ v1_funct_1(D_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_212,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_210])).

tff(c_215,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_172,c_212])).

tff(c_224,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_215])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_229,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_172])).

tff(c_228,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_171])).

tff(c_169,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_163])).

tff(c_227,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_169])).

tff(c_385,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_tops_2(A_97,B_98,C_99) = k2_funct_1(C_99)
      | ~ v2_funct_1(C_99)
      | k2_relset_1(A_97,B_98,C_99) != B_98
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_2(C_99,A_97,B_98)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_391,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_385])).

tff(c_395,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_229,c_227,c_58,c_391])).

tff(c_48,plain,(
    ! [A_29,B_30,C_31] :
      ( m1_subset_1(k2_tops_2(A_29,B_30,C_31),k1_zfmisc_1(k2_zfmisc_1(B_30,A_29)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_405,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_48])).

tff(c_409,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_229,c_228,c_405])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_477,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_409,c_20])).

tff(c_354,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_funct_1(k2_funct_1(C_88))
      | k2_relset_1(A_89,B_90,C_88) != B_90
      | ~ v2_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_2(C_88,A_89,B_90)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_360,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_354])).

tff(c_364,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_229,c_58,c_227,c_360])).

tff(c_365,plain,(
    ! [C_91,B_92,A_93] :
      ( v1_funct_2(k2_funct_1(C_91),B_92,A_93)
      | k2_relset_1(A_93,B_92,C_91) != B_92
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_371,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_365])).

tff(c_375,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_229,c_58,c_227,c_371])).

tff(c_42,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_funct_1(k2_funct_1(C_24))
      | k2_relset_1(A_22,B_23,C_24) != B_23
      | ~ v2_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_421,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_409,c_42])).

tff(c_458,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_375,c_421])).

tff(c_583,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_458])).

tff(c_584,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_587,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_584])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_58,c_587])).

tff(c_592,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_594,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_610,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_594])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_58,c_610])).

tff(c_616,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_622,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_477])).

tff(c_593,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_46,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_tops_2(A_26,B_27,C_28) = k2_funct_1(C_28)
      | ~ v2_funct_1(C_28)
      | k2_relset_1(A_26,B_27,C_28) != B_27
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_413,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_409,c_46])).

tff(c_449,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_375,c_413])).

tff(c_681,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_593,c_449])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_146,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_82,c_81,c_81,c_81,c_56])).

tff(c_170,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_164,c_164,c_146])).

tff(c_226,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_223,c_223,c_170])).

tff(c_398,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_226])).

tff(c_686,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_398])).

tff(c_714,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_686])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_58,c_224,c_714])).

tff(c_718,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_725,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_172])).

tff(c_724,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_171])).

tff(c_24,plain,(
    ! [C_17,A_15] :
      ( k1_xboole_0 = C_17
      | ~ v1_funct_2(C_17,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_759,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_724,c_24])).

tff(c_782,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_759])).

tff(c_790,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_782])).

tff(c_719,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_796,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_719])).

tff(c_795,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_725])).

tff(c_721,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_192])).

tff(c_792,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_721])).

tff(c_791,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_724])).

tff(c_30,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1(k1_xboole_0,B_16,C_17) = k1_xboole_0
      | ~ v1_funct_2(C_17,k1_xboole_0,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_832,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_791,c_30])).

tff(c_862,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_792,c_832])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_796,c_862])).

tff(c_865,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_720,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_215])).

tff(c_870,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_720])).

tff(c_866,plain,(
    k2_struct_0('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_897,plain,(
    k2_struct_0('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_866])).

tff(c_871,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_725])).

tff(c_723,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_718,c_169])).

tff(c_869,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_865,c_723])).

tff(c_867,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_724])).

tff(c_1034,plain,(
    ! [C_142,A_143,B_144] :
      ( v1_funct_1(k2_funct_1(C_142))
      | k2_relset_1(A_143,B_144,C_142) != B_144
      | ~ v2_funct_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_2(C_142,A_143,B_144)
      | ~ v1_funct_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1040,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_867,c_1034])).

tff(c_1044,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_871,c_58,c_869,c_1040])).

tff(c_1045,plain,(
    ! [C_145,B_146,A_147] :
      ( v1_funct_2(k2_funct_1(C_145),B_146,A_147)
      | k2_relset_1(A_147,B_146,C_145) != B_146
      | ~ v2_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_2(C_145,A_147,B_146)
      | ~ v1_funct_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1051,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_867,c_1045])).

tff(c_1055,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_871,c_58,c_869,c_1051])).

tff(c_1069,plain,(
    ! [A_151,B_152,C_153] :
      ( k2_tops_2(A_151,B_152,C_153) = k2_funct_1(C_153)
      | ~ v2_funct_1(C_153)
      | k2_relset_1(A_151,B_152,C_153) != B_152
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_2(C_153,A_151,B_152)
      | ~ v1_funct_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1075,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_867,c_1069])).

tff(c_1079,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_871,c_869,c_58,c_1075])).

tff(c_1090,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3')))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_48])).

tff(c_1094,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_871,c_867,c_1090])).

tff(c_50,plain,(
    ! [A_29,B_30,C_31] :
      ( v1_funct_2(k2_tops_2(A_29,B_30,C_31),B_30,A_29)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1117,plain,
    ( v1_funct_2(k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1094,c_50])).

tff(c_1161,plain,(
    v1_funct_2(k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_1055,c_1117])).

tff(c_975,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1(k2_tops_2(A_136,B_137,C_138),k1_zfmisc_1(k2_zfmisc_1(B_137,A_136)))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_2(C_138,A_136,B_137)
      | ~ v1_funct_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_878,plain,(
    ! [C_17,A_15] :
      ( C_17 = '#skF_3'
      | ~ v1_funct_2(C_17,A_15,'#skF_3')
      | A_15 = '#skF_3'
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_865,c_865,c_865,c_24])).

tff(c_1367,plain,(
    ! [B_171,C_172] :
      ( k2_tops_2('#skF_3',B_171,C_172) = '#skF_3'
      | ~ v1_funct_2(k2_tops_2('#skF_3',B_171,C_172),B_171,'#skF_3')
      | B_171 = '#skF_3'
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_171)))
      | ~ v1_funct_2(C_172,'#skF_3',B_171)
      | ~ v1_funct_1(C_172) ) ),
    inference(resolution,[status(thm)],[c_975,c_878])).

tff(c_1369,plain,
    ( k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_struct_0('#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1161,c_1367])).

tff(c_1372,plain,
    ( k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_1055,c_1094,c_1369])).

tff(c_1373,plain,(
    k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_897,c_1372])).

tff(c_722,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_718,c_718,c_170])).

tff(c_884,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3',k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_865,c_865,c_722])).

tff(c_1084,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3',k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_884])).

tff(c_1377,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_1084])).

tff(c_1385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_1377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n008.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 11:06:00 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.15/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.64  
% 3.92/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.64  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.64  
% 3.92/1.64  %Foreground sorts:
% 3.92/1.64  
% 3.92/1.64  
% 3.92/1.64  %Background operators:
% 3.92/1.64  
% 3.92/1.64  
% 3.92/1.64  %Foreground operators:
% 3.92/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.92/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.92/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.92/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.92/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.92/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.92/1.64  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.92/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.92/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.92/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.92/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.92/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.92/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.92/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.92/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.92/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.92/1.64  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.92/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.64  
% 3.92/1.68  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.92/1.68  tff(f_190, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.92/1.68  tff(f_126, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.92/1.68  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.92/1.68  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.92/1.68  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.92/1.68  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.92/1.68  tff(f_106, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.92/1.68  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.92/1.68  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.92/1.68  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.92/1.68  tff(f_138, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.92/1.68  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.92/1.68  tff(f_122, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.92/1.68  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.92/1.68  tff(c_72, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_74, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.92/1.68  tff(c_82, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_74])).
% 3.92/1.68  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_81, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_74])).
% 3.92/1.68  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_62])).
% 3.92/1.68  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.68  tff(c_101, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_98, c_2])).
% 3.92/1.68  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_101])).
% 3.92/1.68  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_159, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.92/1.68  tff(c_163, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_159])).
% 3.92/1.68  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_92, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_60])).
% 3.92/1.68  tff(c_164, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_92])).
% 3.92/1.68  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_91, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_64])).
% 3.92/1.68  tff(c_172, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_91])).
% 3.92/1.68  tff(c_171, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_98])).
% 3.92/1.68  tff(c_18, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.92/1.68  tff(c_192, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_171, c_18])).
% 3.92/1.68  tff(c_216, plain, (![B_70, A_71, C_72]: (k1_xboole_0=B_70 | k1_relset_1(A_71, B_70, C_72)=A_71 | ~v1_funct_2(C_72, A_71, B_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.92/1.68  tff(c_219, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_171, c_216])).
% 3.92/1.68  tff(c_222, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_192, c_219])).
% 3.92/1.68  tff(c_223, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_222])).
% 3.92/1.68  tff(c_210, plain, (![A_67, B_68, D_69]: (r2_funct_2(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(D_69, A_67, B_68) | ~v1_funct_1(D_69))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.92/1.68  tff(c_212, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_171, c_210])).
% 3.92/1.68  tff(c_215, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_172, c_212])).
% 3.92/1.68  tff(c_224, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_215])).
% 3.92/1.68  tff(c_16, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.68  tff(c_12, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/1.68  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.92/1.68  tff(c_229, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_172])).
% 3.92/1.68  tff(c_228, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_171])).
% 3.92/1.68  tff(c_169, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_163])).
% 3.92/1.68  tff(c_227, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_169])).
% 3.92/1.68  tff(c_385, plain, (![A_97, B_98, C_99]: (k2_tops_2(A_97, B_98, C_99)=k2_funct_1(C_99) | ~v2_funct_1(C_99) | k2_relset_1(A_97, B_98, C_99)!=B_98 | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_2(C_99, A_97, B_98) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.92/1.68  tff(c_391, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_228, c_385])).
% 3.92/1.68  tff(c_395, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_229, c_227, c_58, c_391])).
% 3.92/1.68  tff(c_48, plain, (![A_29, B_30, C_31]: (m1_subset_1(k2_tops_2(A_29, B_30, C_31), k1_zfmisc_1(k2_zfmisc_1(B_30, A_29))) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.92/1.68  tff(c_405, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_395, c_48])).
% 3.92/1.68  tff(c_409, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_229, c_228, c_405])).
% 3.92/1.68  tff(c_20, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.92/1.68  tff(c_477, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_409, c_20])).
% 3.92/1.68  tff(c_354, plain, (![C_88, A_89, B_90]: (v1_funct_1(k2_funct_1(C_88)) | k2_relset_1(A_89, B_90, C_88)!=B_90 | ~v2_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_2(C_88, A_89, B_90) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.92/1.68  tff(c_360, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_228, c_354])).
% 3.92/1.68  tff(c_364, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_229, c_58, c_227, c_360])).
% 3.92/1.68  tff(c_365, plain, (![C_91, B_92, A_93]: (v1_funct_2(k2_funct_1(C_91), B_92, A_93) | k2_relset_1(A_93, B_92, C_91)!=B_92 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.92/1.68  tff(c_371, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_228, c_365])).
% 3.92/1.68  tff(c_375, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_229, c_58, c_227, c_371])).
% 3.92/1.68  tff(c_42, plain, (![C_24, A_22, B_23]: (v1_funct_1(k2_funct_1(C_24)) | k2_relset_1(A_22, B_23, C_24)!=B_23 | ~v2_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.92/1.68  tff(c_421, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_409, c_42])).
% 3.92/1.68  tff(c_458, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_375, c_421])).
% 3.92/1.68  tff(c_583, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_458])).
% 3.92/1.68  tff(c_584, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_583])).
% 3.92/1.68  tff(c_587, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_584])).
% 3.92/1.68  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_58, c_587])).
% 3.92/1.68  tff(c_592, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_583])).
% 3.92/1.68  tff(c_594, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_592])).
% 3.92/1.68  tff(c_610, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_594])).
% 3.92/1.68  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_58, c_610])).
% 3.92/1.68  tff(c_616, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_592])).
% 3.92/1.68  tff(c_622, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_477])).
% 3.92/1.68  tff(c_593, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_583])).
% 3.92/1.68  tff(c_46, plain, (![A_26, B_27, C_28]: (k2_tops_2(A_26, B_27, C_28)=k2_funct_1(C_28) | ~v2_funct_1(C_28) | k2_relset_1(A_26, B_27, C_28)!=B_27 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.92/1.68  tff(c_413, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_409, c_46])).
% 3.92/1.68  tff(c_449, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_375, c_413])).
% 3.92/1.68  tff(c_681, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_593, c_449])).
% 3.92/1.68  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.92/1.68  tff(c_146, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_82, c_81, c_81, c_81, c_56])).
% 3.92/1.68  tff(c_170, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_164, c_164, c_146])).
% 3.92/1.68  tff(c_226, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_223, c_223, c_170])).
% 3.92/1.68  tff(c_398, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_226])).
% 3.92/1.68  tff(c_686, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_398])).
% 3.92/1.68  tff(c_714, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_686])).
% 3.92/1.68  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_58, c_224, c_714])).
% 3.92/1.68  tff(c_718, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_222])).
% 3.92/1.68  tff(c_725, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_718, c_172])).
% 3.92/1.68  tff(c_724, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_718, c_171])).
% 3.92/1.68  tff(c_24, plain, (![C_17, A_15]: (k1_xboole_0=C_17 | ~v1_funct_2(C_17, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.92/1.68  tff(c_759, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_724, c_24])).
% 3.92/1.68  tff(c_782, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_725, c_759])).
% 3.92/1.68  tff(c_790, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_782])).
% 3.92/1.68  tff(c_719, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_222])).
% 3.92/1.68  tff(c_796, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_790, c_719])).
% 3.92/1.68  tff(c_795, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_790, c_725])).
% 3.92/1.68  tff(c_721, plain, (k1_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_192])).
% 3.92/1.68  tff(c_792, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_721])).
% 3.92/1.68  tff(c_791, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_790, c_724])).
% 3.92/1.68  tff(c_30, plain, (![B_16, C_17]: (k1_relset_1(k1_xboole_0, B_16, C_17)=k1_xboole_0 | ~v1_funct_2(C_17, k1_xboole_0, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.92/1.68  tff(c_832, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_791, c_30])).
% 3.92/1.68  tff(c_862, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_795, c_792, c_832])).
% 3.92/1.68  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_796, c_862])).
% 3.92/1.68  tff(c_865, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_782])).
% 3.92/1.68  tff(c_720, plain, (r2_funct_2(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_215])).
% 3.92/1.68  tff(c_870, plain, (r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_865, c_720])).
% 3.92/1.68  tff(c_866, plain, (k2_struct_0('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_782])).
% 3.92/1.68  tff(c_897, plain, (k2_struct_0('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_865, c_866])).
% 3.92/1.68  tff(c_871, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_865, c_725])).
% 3.92/1.68  tff(c_723, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_718, c_718, c_169])).
% 3.92/1.68  tff(c_869, plain, (k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_865, c_865, c_723])).
% 3.92/1.68  tff(c_867, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_865, c_724])).
% 3.92/1.68  tff(c_1034, plain, (![C_142, A_143, B_144]: (v1_funct_1(k2_funct_1(C_142)) | k2_relset_1(A_143, B_144, C_142)!=B_144 | ~v2_funct_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_2(C_142, A_143, B_144) | ~v1_funct_1(C_142))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.92/1.68  tff(c_1040, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_867, c_1034])).
% 3.92/1.68  tff(c_1044, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_871, c_58, c_869, c_1040])).
% 3.92/1.68  tff(c_1045, plain, (![C_145, B_146, A_147]: (v1_funct_2(k2_funct_1(C_145), B_146, A_147) | k2_relset_1(A_147, B_146, C_145)!=B_146 | ~v2_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))) | ~v1_funct_2(C_145, A_147, B_146) | ~v1_funct_1(C_145))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.92/1.68  tff(c_1051, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_867, c_1045])).
% 3.92/1.68  tff(c_1055, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_871, c_58, c_869, c_1051])).
% 3.92/1.68  tff(c_1069, plain, (![A_151, B_152, C_153]: (k2_tops_2(A_151, B_152, C_153)=k2_funct_1(C_153) | ~v2_funct_1(C_153) | k2_relset_1(A_151, B_152, C_153)!=B_152 | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_2(C_153, A_151, B_152) | ~v1_funct_1(C_153))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.92/1.68  tff(c_1075, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_867, c_1069])).
% 3.92/1.68  tff(c_1079, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_871, c_869, c_58, c_1075])).
% 3.92/1.68  tff(c_1090, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3'))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1079, c_48])).
% 3.92/1.68  tff(c_1094, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_871, c_867, c_1090])).
% 3.92/1.68  tff(c_50, plain, (![A_29, B_30, C_31]: (v1_funct_2(k2_tops_2(A_29, B_30, C_31), B_30, A_29) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.92/1.68  tff(c_1117, plain, (v1_funct_2(k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1094, c_50])).
% 3.92/1.68  tff(c_1161, plain, (v1_funct_2(k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_1055, c_1117])).
% 3.92/1.68  tff(c_975, plain, (![A_136, B_137, C_138]: (m1_subset_1(k2_tops_2(A_136, B_137, C_138), k1_zfmisc_1(k2_zfmisc_1(B_137, A_136))) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_2(C_138, A_136, B_137) | ~v1_funct_1(C_138))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.92/1.68  tff(c_878, plain, (![C_17, A_15]: (C_17='#skF_3' | ~v1_funct_2(C_17, A_15, '#skF_3') | A_15='#skF_3' | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_865, c_865, c_865, c_865, c_24])).
% 3.92/1.68  tff(c_1367, plain, (![B_171, C_172]: (k2_tops_2('#skF_3', B_171, C_172)='#skF_3' | ~v1_funct_2(k2_tops_2('#skF_3', B_171, C_172), B_171, '#skF_3') | B_171='#skF_3' | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_171))) | ~v1_funct_2(C_172, '#skF_3', B_171) | ~v1_funct_1(C_172))), inference(resolution, [status(thm)], [c_975, c_878])).
% 3.92/1.68  tff(c_1369, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | k2_struct_0('#skF_1')='#skF_3' | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1161, c_1367])).
% 3.92/1.68  tff(c_1372, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_1055, c_1094, c_1369])).
% 3.92/1.68  tff(c_1373, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_897, c_1372])).
% 3.92/1.68  tff(c_722, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k1_xboole_0, k2_tops_2(k1_xboole_0, k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_718, c_718, c_170])).
% 3.92/1.68  tff(c_884, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_865, c_865, c_865, c_722])).
% 3.92/1.68  tff(c_1084, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_884])).
% 3.92/1.68  tff(c_1377, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1373, c_1084])).
% 3.92/1.68  tff(c_1385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_870, c_1377])).
% 3.92/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.68  
% 3.92/1.68  Inference rules
% 3.92/1.68  ----------------------
% 3.92/1.68  #Ref     : 0
% 3.92/1.68  #Sup     : 285
% 3.92/1.68  #Fact    : 0
% 3.92/1.68  #Define  : 0
% 3.92/1.68  #Split   : 7
% 3.92/1.68  #Chain   : 0
% 3.92/1.68  #Close   : 0
% 3.92/1.68  
% 3.92/1.68  Ordering : KBO
% 3.92/1.68  
% 3.92/1.68  Simplification rules
% 3.92/1.68  ----------------------
% 3.92/1.68  #Subsume      : 17
% 3.92/1.68  #Demod        : 393
% 3.92/1.68  #Tautology    : 160
% 3.92/1.68  #SimpNegUnit  : 9
% 3.92/1.68  #BackRed      : 63
% 3.92/1.68  
% 3.92/1.68  #Partial instantiations: 0
% 3.92/1.68  #Strategies tried      : 1
% 3.92/1.68  
% 3.92/1.68  Timing (in seconds)
% 3.92/1.68  ----------------------
% 3.92/1.68  Preprocessing        : 0.36
% 3.92/1.68  Parsing              : 0.19
% 3.92/1.68  CNF conversion       : 0.02
% 3.92/1.68  Main loop            : 0.56
% 3.92/1.68  Inferencing          : 0.18
% 3.92/1.68  Reduction            : 0.20
% 3.92/1.68  Demodulation         : 0.14
% 3.92/1.68  BG Simplification    : 0.03
% 3.92/1.68  Subsumption          : 0.10
% 3.92/1.68  Abstraction          : 0.03
% 3.92/1.68  MUC search           : 0.00
% 3.92/1.68  Cooper               : 0.00
% 3.92/1.68  Total                : 0.99
% 3.92/1.68  Index Insertion      : 0.00
% 3.92/1.68  Index Deletion       : 0.00
% 3.92/1.68  Index Matching       : 0.00
% 3.92/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
