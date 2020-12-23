%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:41 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  157 (22596 expanded)
%              Number of leaves         :   42 (7866 expanded)
%              Depth                    :   26
%              Number of atoms          :  422 (64735 expanded)
%              Number of equality atoms :   71 (13999 expanded)
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

tff(f_172,negated_conjecture,(
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

tff(f_130,axiom,(
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

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_126,axiom,(
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

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_72,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_64])).

tff(c_58,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_71,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_64])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_95,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_52])).

tff(c_101,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_95,c_101])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_104])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_48,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_82,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(u1_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_88,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_82])).

tff(c_92,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_88])).

tff(c_93,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_92])).

tff(c_108,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_112,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_95,c_108])).

tff(c_161,plain,(
    ! [B_55,A_56] :
      ( k1_relat_1(B_55) = A_56
      | ~ v1_partfun1(B_55,A_56)
      | ~ v4_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_164,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_161])).

tff(c_167,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_164])).

tff(c_168,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_81,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_54])).

tff(c_194,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_partfun1(C_61,A_62)
      | ~ v1_funct_2(C_61,A_62,B_63)
      | ~ v1_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | v1_xboole_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_197,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_95,c_194])).

tff(c_200,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_81,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_168,c_200])).

tff(c_203,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_208,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_95])).

tff(c_275,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_279,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_275])).

tff(c_50,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_96,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_50])).

tff(c_207,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_96])).

tff(c_280,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_207])).

tff(c_210,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_81])).

tff(c_287,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_210])).

tff(c_286,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_208])).

tff(c_524,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r2_funct_2(A_100,B_101,C_102,C_102)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(D_103,A_100,B_101)
      | ~ v1_funct_1(D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_528,plain,(
    ! [C_102] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_102,C_102)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_102,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_286,c_524])).

tff(c_544,plain,(
    ! [C_107] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_107,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_107,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_528])).

tff(c_549,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_544])).

tff(c_553,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_549])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_285,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_279])).

tff(c_349,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_funct_1(k2_funct_1(C_72))
      | k2_relset_1(A_73,B_74,C_72) != B_74
      | ~ v2_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_2(C_72,A_73,B_74)
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_352,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_349])).

tff(c_355,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_48,c_285,c_352])).

tff(c_356,plain,(
    ! [C_75,B_76,A_77] :
      ( v1_funct_2(k2_funct_1(C_75),B_76,A_77)
      | k2_relset_1(A_77,B_76,C_75) != B_76
      | ~ v2_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76)))
      | ~ v1_funct_2(C_75,A_77,B_76)
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_359,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_356])).

tff(c_362,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_48,c_285,c_359])).

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

tff(c_370,plain,(
    ! [C_81,B_82,A_83] :
      ( m1_subset_1(k2_funct_1(C_81),k1_zfmisc_1(k2_zfmisc_1(B_82,A_83)))
      | k2_relset_1(A_83,B_82,C_81) != B_82
      | ~ v2_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_2(C_81,A_83,B_82)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_394,plain,(
    ! [C_81,B_82,A_83] :
      ( v1_relat_1(k2_funct_1(C_81))
      | ~ v1_relat_1(k2_zfmisc_1(B_82,A_83))
      | k2_relset_1(A_83,B_82,C_81) != B_82
      | ~ v2_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_2(C_81,A_83,B_82)
      | ~ v1_funct_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_370,c_2])).

tff(c_413,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_relat_1(k2_funct_1(C_84))
      | k2_relset_1(A_85,B_86,C_84) != B_86
      | ~ v2_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_394])).

tff(c_419,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_413])).

tff(c_423,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_48,c_285,c_419])).

tff(c_20,plain,(
    ! [C_11,A_9,B_10] :
      ( v4_relat_1(C_11,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_424,plain,(
    ! [C_87,B_88,A_89] :
      ( v4_relat_1(k2_funct_1(C_87),B_88)
      | k2_relset_1(A_89,B_88,C_87) != B_88
      | ~ v2_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88)))
      | ~ v1_funct_2(C_87,A_89,B_88)
      | ~ v1_funct_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_370,c_20])).

tff(c_430,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_424])).

tff(c_434,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_48,c_285,c_430])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(B_20) = A_19
      | ~ v1_partfun1(B_20,A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_437,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_434,c_30])).

tff(c_440,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_437])).

tff(c_441,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_260,plain,(
    ! [A_64] :
      ( k1_relat_1(k2_funct_1(A_64)) = k2_relat_1(A_64)
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [B_20] :
      ( v1_partfun1(B_20,k1_relat_1(B_20))
      | ~ v4_relat_1(B_20,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_339,plain,(
    ! [A_71] :
      ( v1_partfun1(k2_funct_1(A_71),k1_relat_1(k2_funct_1(A_71)))
      | ~ v4_relat_1(k2_funct_1(A_71),k2_relat_1(A_71))
      | ~ v1_relat_1(k2_funct_1(A_71))
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_28])).

tff(c_479,plain,(
    ! [A_99] :
      ( v1_partfun1(k2_funct_1(A_99),k2_relat_1(A_99))
      | ~ v4_relat_1(k2_funct_1(A_99),k2_relat_1(A_99))
      | ~ v1_relat_1(k2_funct_1(A_99))
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99)
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_339])).

tff(c_482,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_434,c_479])).

tff(c_491,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_56,c_48,c_423,c_482])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_491])).

tff(c_494,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_595,plain,(
    ! [A_113] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_113)),k1_relat_1(A_113))
      | ~ v4_relat_1(k2_funct_1(k2_funct_1(A_113)),k2_relat_1(k2_funct_1(A_113)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_113)))
      | ~ v2_funct_1(k2_funct_1(A_113))
      | ~ v1_funct_1(k2_funct_1(A_113))
      | ~ v1_relat_1(k2_funct_1(A_113))
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_339])).

tff(c_628,plain,(
    ! [A_120] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_120)),k1_relat_1(A_120))
      | ~ v4_relat_1(A_120,k2_relat_1(k2_funct_1(A_120)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_120)))
      | ~ v2_funct_1(k2_funct_1(A_120))
      | ~ v1_funct_1(k2_funct_1(A_120))
      | ~ v1_relat_1(k2_funct_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120)
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_595])).

tff(c_631,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_494,c_628])).

tff(c_642,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_355,c_423,c_355,c_631])).

tff(c_643,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_642])).

tff(c_653,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_643])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_56,c_48,c_653])).

tff(c_659,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_567,plain,(
    ! [B_109,A_110,C_111] :
      ( k2_relset_1(B_109,A_110,k2_funct_1(C_111)) = k2_relat_1(k2_funct_1(C_111))
      | k2_relset_1(A_110,B_109,C_111) != B_109
      | ~ v2_funct_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ v1_funct_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_370,c_22])).

tff(c_573,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_567])).

tff(c_577,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_48,c_285,c_573])).

tff(c_38,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_funct_1(k2_funct_1(C_27))
      | k2_relset_1(A_25,B_26,C_27) != B_26
      | ~ v2_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_688,plain,(
    ! [C_122,B_123,A_124] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_122)))
      | k2_relset_1(B_123,A_124,k2_funct_1(C_122)) != A_124
      | ~ v2_funct_1(k2_funct_1(C_122))
      | ~ v1_funct_2(k2_funct_1(C_122),B_123,A_124)
      | ~ v1_funct_1(k2_funct_1(C_122))
      | k2_relset_1(A_124,B_123,C_122) != B_123
      | ~ v2_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(C_122,A_124,B_123)
      | ~ v1_funct_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_370,c_38])).

tff(c_694,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_688])).

tff(c_698,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_48,c_285,c_355,c_362,c_659,c_577,c_694])).

tff(c_699,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_698])).

tff(c_702,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_699])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_56,c_48,c_702])).

tff(c_708,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_714,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_577])).

tff(c_44,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_tops_2(A_30,B_31,C_32) = k2_funct_1(C_32)
      | ~ v2_funct_1(C_32)
      | k2_relset_1(A_30,B_31,C_32) != B_31
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_891,plain,(
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
    inference(resolution,[status(thm)],[c_370,c_44])).

tff(c_897,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_891])).

tff(c_901,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_48,c_285,c_355,c_362,c_714,c_659,c_897])).

tff(c_363,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_tops_2(A_78,B_79,C_80) = k2_funct_1(C_80)
      | ~ v2_funct_1(C_80)
      | k2_relset_1(A_78,B_79,C_80) != B_79
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(C_80,A_78,B_79)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_366,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_363])).

tff(c_369,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_285,c_48,c_366])).

tff(c_46,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_113,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_71,c_71,c_71,c_46])).

tff(c_206,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_203,c_203,c_113])).

tff(c_338,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_280,c_280,c_206])).

tff(c_408,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_338])).

tff(c_902,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_408])).

tff(c_909,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_902])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_56,c_48,c_553,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:03:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.54  
% 3.64/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.55  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.64/1.55  
% 3.64/1.55  %Foreground sorts:
% 3.64/1.55  
% 3.64/1.55  
% 3.64/1.55  %Background operators:
% 3.64/1.55  
% 3.64/1.55  
% 3.64/1.55  %Foreground operators:
% 3.64/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.64/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.64/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.55  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.64/1.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.64/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.55  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.64/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.55  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.64/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.64/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.64/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.64/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.64/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.64/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.55  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.64/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.55  
% 3.64/1.57  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.64/1.57  tff(f_172, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.64/1.57  tff(f_130, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.64/1.57  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.64/1.57  tff(f_138, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.64/1.57  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.64/1.57  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.64/1.57  tff(f_88, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.64/1.57  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.64/1.57  tff(f_110, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.64/1.57  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.64/1.57  tff(f_126, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.64/1.57  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.64/1.57  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.64/1.57  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.64/1.57  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.57  tff(c_62, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_64, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.64/1.57  tff(c_72, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_64])).
% 3.64/1.57  tff(c_58, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_71, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_64])).
% 3.64/1.57  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_95, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_52])).
% 3.64/1.57  tff(c_101, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.57  tff(c_104, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_95, c_101])).
% 3.64/1.57  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_104])).
% 3.64/1.57  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_48, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_82, plain, (![A_40]: (~v1_xboole_0(u1_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.64/1.57  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71, c_82])).
% 3.64/1.57  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_88])).
% 3.64/1.57  tff(c_93, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_92])).
% 3.64/1.57  tff(c_108, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.57  tff(c_112, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_95, c_108])).
% 3.64/1.57  tff(c_161, plain, (![B_55, A_56]: (k1_relat_1(B_55)=A_56 | ~v1_partfun1(B_55, A_56) | ~v4_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.57  tff(c_164, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_161])).
% 3.64/1.57  tff(c_167, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_164])).
% 3.64/1.57  tff(c_168, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_167])).
% 3.64/1.57  tff(c_54, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_81, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_54])).
% 3.64/1.57  tff(c_194, plain, (![C_61, A_62, B_63]: (v1_partfun1(C_61, A_62) | ~v1_funct_2(C_61, A_62, B_63) | ~v1_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | v1_xboole_0(B_63))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.64/1.57  tff(c_197, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_95, c_194])).
% 3.64/1.57  tff(c_200, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_81, c_197])).
% 3.64/1.57  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_168, c_200])).
% 3.64/1.57  tff(c_203, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_167])).
% 3.64/1.57  tff(c_208, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_95])).
% 3.64/1.57  tff(c_275, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.64/1.57  tff(c_279, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_208, c_275])).
% 3.64/1.57  tff(c_50, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_96, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_50])).
% 3.64/1.57  tff(c_207, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_96])).
% 3.64/1.57  tff(c_280, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_207])).
% 3.64/1.57  tff(c_210, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_81])).
% 3.64/1.57  tff(c_287, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_210])).
% 3.64/1.57  tff(c_286, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_208])).
% 3.64/1.57  tff(c_524, plain, (![A_100, B_101, C_102, D_103]: (r2_funct_2(A_100, B_101, C_102, C_102) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(D_103, A_100, B_101) | ~v1_funct_1(D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(C_102, A_100, B_101) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.64/1.57  tff(c_528, plain, (![C_102]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_102, C_102) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_102, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_102))), inference(resolution, [status(thm)], [c_286, c_524])).
% 3.64/1.57  tff(c_544, plain, (![C_107]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_107, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_107, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_107))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_528])).
% 3.64/1.57  tff(c_549, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_544])).
% 3.64/1.57  tff(c_553, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_549])).
% 3.64/1.57  tff(c_16, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.64/1.57  tff(c_285, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_279])).
% 3.64/1.57  tff(c_349, plain, (![C_72, A_73, B_74]: (v1_funct_1(k2_funct_1(C_72)) | k2_relset_1(A_73, B_74, C_72)!=B_74 | ~v2_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_2(C_72, A_73, B_74) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.64/1.57  tff(c_352, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_349])).
% 3.64/1.57  tff(c_355, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_48, c_285, c_352])).
% 3.64/1.57  tff(c_356, plain, (![C_75, B_76, A_77]: (v1_funct_2(k2_funct_1(C_75), B_76, A_77) | k2_relset_1(A_77, B_76, C_75)!=B_76 | ~v2_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))) | ~v1_funct_2(C_75, A_77, B_76) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.64/1.57  tff(c_359, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_356])).
% 3.64/1.57  tff(c_362, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_48, c_285, c_359])).
% 3.64/1.57  tff(c_12, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.64/1.57  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.64/1.57  tff(c_370, plain, (![C_81, B_82, A_83]: (m1_subset_1(k2_funct_1(C_81), k1_zfmisc_1(k2_zfmisc_1(B_82, A_83))) | k2_relset_1(A_83, B_82, C_81)!=B_82 | ~v2_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_2(C_81, A_83, B_82) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.64/1.57  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.57  tff(c_394, plain, (![C_81, B_82, A_83]: (v1_relat_1(k2_funct_1(C_81)) | ~v1_relat_1(k2_zfmisc_1(B_82, A_83)) | k2_relset_1(A_83, B_82, C_81)!=B_82 | ~v2_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_2(C_81, A_83, B_82) | ~v1_funct_1(C_81))), inference(resolution, [status(thm)], [c_370, c_2])).
% 3.64/1.57  tff(c_413, plain, (![C_84, A_85, B_86]: (v1_relat_1(k2_funct_1(C_84)) | k2_relset_1(A_85, B_86, C_84)!=B_86 | ~v2_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_394])).
% 3.64/1.57  tff(c_419, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_413])).
% 3.64/1.57  tff(c_423, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_48, c_285, c_419])).
% 3.64/1.57  tff(c_20, plain, (![C_11, A_9, B_10]: (v4_relat_1(C_11, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.57  tff(c_424, plain, (![C_87, B_88, A_89]: (v4_relat_1(k2_funct_1(C_87), B_88) | k2_relset_1(A_89, B_88, C_87)!=B_88 | ~v2_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))) | ~v1_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87))), inference(resolution, [status(thm)], [c_370, c_20])).
% 3.64/1.57  tff(c_430, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_424])).
% 3.64/1.57  tff(c_434, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_48, c_285, c_430])).
% 3.64/1.57  tff(c_30, plain, (![B_20, A_19]: (k1_relat_1(B_20)=A_19 | ~v1_partfun1(B_20, A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.57  tff(c_437, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_434, c_30])).
% 3.64/1.57  tff(c_440, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_437])).
% 3.64/1.57  tff(c_441, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_440])).
% 3.64/1.57  tff(c_14, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.64/1.57  tff(c_260, plain, (![A_64]: (k1_relat_1(k2_funct_1(A_64))=k2_relat_1(A_64) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.64/1.57  tff(c_28, plain, (![B_20]: (v1_partfun1(B_20, k1_relat_1(B_20)) | ~v4_relat_1(B_20, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.57  tff(c_339, plain, (![A_71]: (v1_partfun1(k2_funct_1(A_71), k1_relat_1(k2_funct_1(A_71))) | ~v4_relat_1(k2_funct_1(A_71), k2_relat_1(A_71)) | ~v1_relat_1(k2_funct_1(A_71)) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_260, c_28])).
% 3.64/1.57  tff(c_479, plain, (![A_99]: (v1_partfun1(k2_funct_1(A_99), k2_relat_1(A_99)) | ~v4_relat_1(k2_funct_1(A_99), k2_relat_1(A_99)) | ~v1_relat_1(k2_funct_1(A_99)) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_14, c_339])).
% 3.64/1.57  tff(c_482, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_434, c_479])).
% 3.64/1.57  tff(c_491, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_56, c_48, c_423, c_482])).
% 3.64/1.57  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_491])).
% 3.64/1.57  tff(c_494, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_440])).
% 3.64/1.57  tff(c_595, plain, (![A_113]: (v1_partfun1(k2_funct_1(k2_funct_1(A_113)), k1_relat_1(A_113)) | ~v4_relat_1(k2_funct_1(k2_funct_1(A_113)), k2_relat_1(k2_funct_1(A_113))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_113))) | ~v2_funct_1(k2_funct_1(A_113)) | ~v1_funct_1(k2_funct_1(A_113)) | ~v1_relat_1(k2_funct_1(A_113)) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_16, c_339])).
% 3.64/1.57  tff(c_628, plain, (![A_120]: (v1_partfun1(k2_funct_1(k2_funct_1(A_120)), k1_relat_1(A_120)) | ~v4_relat_1(A_120, k2_relat_1(k2_funct_1(A_120))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_120))) | ~v2_funct_1(k2_funct_1(A_120)) | ~v1_funct_1(k2_funct_1(A_120)) | ~v1_relat_1(k2_funct_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_16, c_595])).
% 3.64/1.57  tff(c_631, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_628])).
% 3.64/1.57  tff(c_642, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_355, c_423, c_355, c_631])).
% 3.64/1.57  tff(c_643, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_642])).
% 3.64/1.57  tff(c_653, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_643])).
% 3.64/1.57  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_56, c_48, c_653])).
% 3.64/1.57  tff(c_659, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_642])).
% 3.64/1.57  tff(c_22, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.64/1.57  tff(c_567, plain, (![B_109, A_110, C_111]: (k2_relset_1(B_109, A_110, k2_funct_1(C_111))=k2_relat_1(k2_funct_1(C_111)) | k2_relset_1(A_110, B_109, C_111)!=B_109 | ~v2_funct_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_2(C_111, A_110, B_109) | ~v1_funct_1(C_111))), inference(resolution, [status(thm)], [c_370, c_22])).
% 3.64/1.57  tff(c_573, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_567])).
% 3.64/1.57  tff(c_577, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_48, c_285, c_573])).
% 3.64/1.57  tff(c_38, plain, (![C_27, A_25, B_26]: (v1_funct_1(k2_funct_1(C_27)) | k2_relset_1(A_25, B_26, C_27)!=B_26 | ~v2_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.64/1.57  tff(c_688, plain, (![C_122, B_123, A_124]: (v1_funct_1(k2_funct_1(k2_funct_1(C_122))) | k2_relset_1(B_123, A_124, k2_funct_1(C_122))!=A_124 | ~v2_funct_1(k2_funct_1(C_122)) | ~v1_funct_2(k2_funct_1(C_122), B_123, A_124) | ~v1_funct_1(k2_funct_1(C_122)) | k2_relset_1(A_124, B_123, C_122)!=B_123 | ~v2_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(C_122, A_124, B_123) | ~v1_funct_1(C_122))), inference(resolution, [status(thm)], [c_370, c_38])).
% 3.64/1.57  tff(c_694, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_688])).
% 3.64/1.57  tff(c_698, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_48, c_285, c_355, c_362, c_659, c_577, c_694])).
% 3.64/1.57  tff(c_699, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_698])).
% 3.64/1.57  tff(c_702, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_699])).
% 3.64/1.57  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_56, c_48, c_702])).
% 3.64/1.57  tff(c_708, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_698])).
% 3.64/1.57  tff(c_714, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_708, c_577])).
% 3.64/1.57  tff(c_44, plain, (![A_30, B_31, C_32]: (k2_tops_2(A_30, B_31, C_32)=k2_funct_1(C_32) | ~v2_funct_1(C_32) | k2_relset_1(A_30, B_31, C_32)!=B_31 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.57  tff(c_891, plain, (![B_129, A_130, C_131]: (k2_tops_2(B_129, A_130, k2_funct_1(C_131))=k2_funct_1(k2_funct_1(C_131)) | ~v2_funct_1(k2_funct_1(C_131)) | k2_relset_1(B_129, A_130, k2_funct_1(C_131))!=A_130 | ~v1_funct_2(k2_funct_1(C_131), B_129, A_130) | ~v1_funct_1(k2_funct_1(C_131)) | k2_relset_1(A_130, B_129, C_131)!=B_129 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(C_131, A_130, B_129) | ~v1_funct_1(C_131))), inference(resolution, [status(thm)], [c_370, c_44])).
% 3.64/1.57  tff(c_897, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_891])).
% 3.64/1.57  tff(c_901, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_48, c_285, c_355, c_362, c_714, c_659, c_897])).
% 3.64/1.57  tff(c_363, plain, (![A_78, B_79, C_80]: (k2_tops_2(A_78, B_79, C_80)=k2_funct_1(C_80) | ~v2_funct_1(C_80) | k2_relset_1(A_78, B_79, C_80)!=B_79 | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(C_80, A_78, B_79) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.64/1.57  tff(c_366, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_363])).
% 3.64/1.57  tff(c_369, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_285, c_48, c_366])).
% 3.64/1.57  tff(c_46, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.64/1.57  tff(c_113, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_71, c_71, c_71, c_46])).
% 3.64/1.57  tff(c_206, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_203, c_203, c_113])).
% 3.64/1.57  tff(c_338, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_280, c_280, c_206])).
% 3.64/1.57  tff(c_408, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_338])).
% 3.64/1.57  tff(c_902, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_901, c_408])).
% 3.64/1.57  tff(c_909, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_902])).
% 3.64/1.57  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_56, c_48, c_553, c_909])).
% 3.64/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.57  
% 3.64/1.57  Inference rules
% 3.64/1.57  ----------------------
% 3.64/1.58  #Ref     : 0
% 3.64/1.58  #Sup     : 186
% 3.64/1.58  #Fact    : 0
% 3.64/1.58  #Define  : 0
% 3.64/1.58  #Split   : 9
% 3.64/1.58  #Chain   : 0
% 3.64/1.58  #Close   : 0
% 3.64/1.58  
% 3.64/1.58  Ordering : KBO
% 3.64/1.58  
% 3.64/1.58  Simplification rules
% 3.64/1.58  ----------------------
% 3.64/1.58  #Subsume      : 5
% 3.64/1.58  #Demod        : 288
% 3.64/1.58  #Tautology    : 89
% 3.64/1.58  #SimpNegUnit  : 6
% 3.64/1.58  #BackRed      : 19
% 3.64/1.58  
% 3.64/1.58  #Partial instantiations: 0
% 3.64/1.58  #Strategies tried      : 1
% 3.64/1.58  
% 3.64/1.58  Timing (in seconds)
% 3.64/1.58  ----------------------
% 3.64/1.58  Preprocessing        : 0.36
% 3.64/1.58  Parsing              : 0.19
% 3.64/1.58  CNF conversion       : 0.02
% 3.64/1.58  Main loop            : 0.44
% 3.64/1.58  Inferencing          : 0.15
% 3.64/1.58  Reduction            : 0.15
% 3.64/1.58  Demodulation         : 0.11
% 3.64/1.58  BG Simplification    : 0.02
% 3.64/1.58  Subsumption          : 0.08
% 3.64/1.58  Abstraction          : 0.02
% 3.64/1.58  MUC search           : 0.00
% 3.64/1.58  Cooper               : 0.00
% 3.64/1.58  Total                : 0.85
% 3.64/1.58  Index Insertion      : 0.00
% 3.64/1.58  Index Deletion       : 0.00
% 3.64/1.58  Index Matching       : 0.00
% 3.64/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
