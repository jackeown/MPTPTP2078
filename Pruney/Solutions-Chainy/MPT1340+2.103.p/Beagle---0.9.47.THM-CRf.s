%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:45 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   97 (1102 expanded)
%              Number of leaves         :   32 ( 430 expanded)
%              Depth                    :   12
%              Number of atoms          :  276 (3794 expanded)
%              Number of equality atoms :   58 ( 803 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_145,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_84,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_123,axiom,(
    ! [A] :
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
               => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                  & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_48])).

tff(c_42,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_55,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_67,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_36])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_65,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_38])).

tff(c_168,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( r2_funct_2(A_54,B_55,C_56,C_56)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(D_57,A_54,B_55)
      | ~ v1_funct_1(D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_172,plain,(
    ! [C_56] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_56,C_56)
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_56,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_56) ) ),
    inference(resolution,[status(thm)],[c_67,c_168])).

tff(c_177,plain,(
    ! [C_58] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_58,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_58,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_172])).

tff(c_182,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_177])).

tff(c_186,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_182])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_74,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_34])).

tff(c_109,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_funct_1(k2_funct_1(C_39))
      | k2_relset_1(A_40,B_41,C_39) != B_41
      | ~ v2_funct_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(C_39,A_40,B_41)
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_112,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_109])).

tff(c_115,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_32,c_74,c_112])).

tff(c_116,plain,(
    ! [C_42,B_43,A_44] :
      ( v1_funct_2(k2_funct_1(C_42),B_43,A_44)
      | k2_relset_1(A_44,B_43,C_42) != B_43
      | ~ v2_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43)))
      | ~ v1_funct_2(C_42,A_44,B_43)
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_119,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_116])).

tff(c_122,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_32,c_74,c_119])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,(
    ! [C_48,B_49,A_50] :
      ( m1_subset_1(k2_funct_1(C_48),k1_zfmisc_1(k2_zfmisc_1(B_49,A_50)))
      | k2_relset_1(A_50,B_49,C_48) != B_49
      | ~ v2_funct_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ v1_funct_2(C_48,A_50,B_49)
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_funct_1(k2_funct_1(C_14))
      | k2_relset_1(A_12,B_13,C_14) != B_13
      | ~ v2_funct_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_195,plain,(
    ! [C_62,B_63,A_64] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_62)))
      | k2_relset_1(B_63,A_64,k2_funct_1(C_62)) != A_64
      | ~ v2_funct_1(k2_funct_1(C_62))
      | ~ v1_funct_2(k2_funct_1(C_62),B_63,A_64)
      | ~ v1_funct_1(k2_funct_1(C_62))
      | k2_relset_1(A_64,B_63,C_62) != B_63
      | ~ v2_funct_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63)))
      | ~ v1_funct_2(C_62,A_64,B_63)
      | ~ v1_funct_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_135,c_20])).

tff(c_201,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_195])).

tff(c_205,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_32,c_74,c_115,c_122,c_201])).

tff(c_206,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_260,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_206])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_40,c_32,c_260])).

tff(c_265,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_267,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_123,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_tops_2(A_45,B_46,C_47) = k2_funct_1(C_47)
      | ~ v2_funct_1(C_47)
      | k2_relset_1(A_45,B_46,C_47) != B_46
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_126,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_123])).

tff(c_129,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_74,c_32,c_126])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_452,plain,(
    ! [B_91,A_92,C_93] :
      ( k2_relset_1(u1_struct_0(B_91),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),u1_struct_0(B_91),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),u1_struct_0(B_91),C_93) != k2_struct_0(B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0(B_91))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),u1_struct_0(B_91))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0(B_91)
      | v2_struct_0(B_91)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_473,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),u1_struct_0('#skF_2'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),u1_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_452])).

tff(c_494,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),k2_struct_0('#skF_2'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),k2_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_55,c_55,c_55,c_55,c_473])).

tff(c_503,plain,(
    ! [A_94,C_95] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_94),k2_tops_2(u1_struct_0(A_94),k2_struct_0('#skF_2'),C_95)) = k2_struct_0(A_94)
      | ~ v2_funct_1(C_95)
      | k2_relset_1(u1_struct_0(A_94),k2_struct_0('#skF_2'),C_95) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_95,u1_struct_0(A_94),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_95)
      | ~ l1_struct_0(A_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_494])).

tff(c_512,plain,(
    ! [C_95] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_95)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_95)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_95) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_95,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_95)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_503])).

tff(c_532,plain,(
    ! [C_96] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_96)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_96)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_96) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_96,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56,c_56,c_56,c_56,c_512])).

tff(c_541,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_532])).

tff(c_545,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_67,c_74,c_32,c_541])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_545])).

tff(c_549,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_266,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_tops_2(A_16,B_17,C_18) = k2_funct_1(C_18)
      | ~ v2_funct_1(C_18)
      | k2_relset_1(A_16,B_17,C_18) != B_17
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_833,plain,(
    ! [B_120,A_121,C_122] :
      ( k2_tops_2(B_120,A_121,k2_funct_1(C_122)) = k2_funct_1(k2_funct_1(C_122))
      | ~ v2_funct_1(k2_funct_1(C_122))
      | k2_relset_1(B_120,A_121,k2_funct_1(C_122)) != A_121
      | ~ v1_funct_2(k2_funct_1(C_122),B_120,A_121)
      | ~ v1_funct_1(k2_funct_1(C_122))
      | k2_relset_1(A_121,B_120,C_122) != B_120
      | ~ v2_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120)))
      | ~ v1_funct_2(C_122,A_121,B_120)
      | ~ v1_funct_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_135,c_24])).

tff(c_839,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_833])).

tff(c_843,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_32,c_74,c_115,c_122,c_549,c_266,c_839])).

tff(c_30,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_108,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_56,c_55,c_55,c_55,c_30])).

tff(c_130,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_108])).

tff(c_844,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_130])).

tff(c_851,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_844])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_40,c_32,c_186,c_851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  
% 3.58/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.58/1.59  
% 3.58/1.59  %Foreground sorts:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Background operators:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Foreground operators:
% 3.58/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.58/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.58/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.58/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.59  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.58/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.58/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.58/1.59  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.58/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.59  
% 3.75/1.62  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.75/1.62  tff(f_145, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.75/1.62  tff(f_88, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.75/1.62  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.75/1.62  tff(f_68, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.75/1.62  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.75/1.62  tff(f_84, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.75/1.62  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.75/1.62  tff(f_100, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.75/1.62  tff(f_123, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.75/1.62  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.75/1.62  tff(c_46, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_48, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.75/1.62  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_48])).
% 3.75/1.62  tff(c_42, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_55, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_48])).
% 3.75/1.62  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_67, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_36])).
% 3.75/1.62  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.75/1.62  tff(c_70, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_67, c_2])).
% 3.75/1.62  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_70])).
% 3.75/1.62  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_38, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_65, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_38])).
% 3.75/1.62  tff(c_168, plain, (![A_54, B_55, C_56, D_57]: (r2_funct_2(A_54, B_55, C_56, C_56) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(D_57, A_54, B_55) | ~v1_funct_1(D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.75/1.62  tff(c_172, plain, (![C_56]: (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_56, C_56) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_56, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_56))), inference(resolution, [status(thm)], [c_67, c_168])).
% 3.75/1.62  tff(c_177, plain, (![C_58]: (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_58, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_58, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_58))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_172])).
% 3.75/1.62  tff(c_182, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_177])).
% 3.75/1.62  tff(c_186, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_182])).
% 3.75/1.62  tff(c_12, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.75/1.62  tff(c_34, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_74, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_34])).
% 3.75/1.62  tff(c_109, plain, (![C_39, A_40, B_41]: (v1_funct_1(k2_funct_1(C_39)) | k2_relset_1(A_40, B_41, C_39)!=B_41 | ~v2_funct_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(C_39, A_40, B_41) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.75/1.62  tff(c_112, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_109])).
% 3.75/1.62  tff(c_115, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_32, c_74, c_112])).
% 3.75/1.62  tff(c_116, plain, (![C_42, B_43, A_44]: (v1_funct_2(k2_funct_1(C_42), B_43, A_44) | k2_relset_1(A_44, B_43, C_42)!=B_43 | ~v2_funct_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))) | ~v1_funct_2(C_42, A_44, B_43) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.75/1.62  tff(c_119, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_116])).
% 3.75/1.62  tff(c_122, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_32, c_74, c_119])).
% 3.75/1.62  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.75/1.62  tff(c_135, plain, (![C_48, B_49, A_50]: (m1_subset_1(k2_funct_1(C_48), k1_zfmisc_1(k2_zfmisc_1(B_49, A_50))) | k2_relset_1(A_50, B_49, C_48)!=B_49 | ~v2_funct_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~v1_funct_2(C_48, A_50, B_49) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.75/1.62  tff(c_20, plain, (![C_14, A_12, B_13]: (v1_funct_1(k2_funct_1(C_14)) | k2_relset_1(A_12, B_13, C_14)!=B_13 | ~v2_funct_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_2(C_14, A_12, B_13) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.75/1.62  tff(c_195, plain, (![C_62, B_63, A_64]: (v1_funct_1(k2_funct_1(k2_funct_1(C_62))) | k2_relset_1(B_63, A_64, k2_funct_1(C_62))!=A_64 | ~v2_funct_1(k2_funct_1(C_62)) | ~v1_funct_2(k2_funct_1(C_62), B_63, A_64) | ~v1_funct_1(k2_funct_1(C_62)) | k2_relset_1(A_64, B_63, C_62)!=B_63 | ~v2_funct_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))) | ~v1_funct_2(C_62, A_64, B_63) | ~v1_funct_1(C_62))), inference(resolution, [status(thm)], [c_135, c_20])).
% 3.75/1.62  tff(c_201, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_195])).
% 3.75/1.62  tff(c_205, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_32, c_74, c_115, c_122, c_201])).
% 3.75/1.62  tff(c_206, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_205])).
% 3.75/1.62  tff(c_260, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_206])).
% 3.75/1.62  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_40, c_32, c_260])).
% 3.75/1.62  tff(c_265, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_205])).
% 3.75/1.62  tff(c_267, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_265])).
% 3.75/1.62  tff(c_123, plain, (![A_45, B_46, C_47]: (k2_tops_2(A_45, B_46, C_47)=k2_funct_1(C_47) | ~v2_funct_1(C_47) | k2_relset_1(A_45, B_46, C_47)!=B_46 | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.75/1.62  tff(c_126, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_123])).
% 3.75/1.62  tff(c_129, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_74, c_32, c_126])).
% 3.75/1.62  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_452, plain, (![B_91, A_92, C_93]: (k2_relset_1(u1_struct_0(B_91), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), u1_struct_0(B_91), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0(B_91), C_93)!=k2_struct_0(B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0(B_91)))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0(B_91)) | ~v1_funct_1(C_93) | ~l1_struct_0(B_91) | v2_struct_0(B_91) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.75/1.62  tff(c_473, plain, (![A_92, C_93]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), u1_struct_0('#skF_2'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0('#skF_2')) | ~v1_funct_1(C_93) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_55, c_452])).
% 3.75/1.62  tff(c_494, plain, (![A_92, C_93]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), k2_struct_0('#skF_2'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), k2_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), k2_struct_0('#skF_2')) | ~v1_funct_1(C_93) | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_55, c_55, c_55, c_55, c_473])).
% 3.75/1.62  tff(c_503, plain, (![A_94, C_95]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_94), k2_tops_2(u1_struct_0(A_94), k2_struct_0('#skF_2'), C_95))=k2_struct_0(A_94) | ~v2_funct_1(C_95) | k2_relset_1(u1_struct_0(A_94), k2_struct_0('#skF_2'), C_95)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_95, u1_struct_0(A_94), k2_struct_0('#skF_2')) | ~v1_funct_1(C_95) | ~l1_struct_0(A_94))), inference(negUnitSimplification, [status(thm)], [c_44, c_494])).
% 3.75/1.62  tff(c_512, plain, (![C_95]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_95))=k2_struct_0('#skF_1') | ~v2_funct_1(C_95) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_95)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_95, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_95) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_503])).
% 3.75/1.62  tff(c_532, plain, (![C_96]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_96))=k2_struct_0('#skF_1') | ~v2_funct_1(C_96) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_96)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_96, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_96))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56, c_56, c_56, c_56, c_512])).
% 3.75/1.62  tff(c_541, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_129, c_532])).
% 3.75/1.62  tff(c_545, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_67, c_74, c_32, c_541])).
% 3.75/1.62  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_545])).
% 3.75/1.62  tff(c_549, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_265])).
% 3.75/1.62  tff(c_266, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_205])).
% 3.75/1.62  tff(c_24, plain, (![A_16, B_17, C_18]: (k2_tops_2(A_16, B_17, C_18)=k2_funct_1(C_18) | ~v2_funct_1(C_18) | k2_relset_1(A_16, B_17, C_18)!=B_17 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.75/1.62  tff(c_833, plain, (![B_120, A_121, C_122]: (k2_tops_2(B_120, A_121, k2_funct_1(C_122))=k2_funct_1(k2_funct_1(C_122)) | ~v2_funct_1(k2_funct_1(C_122)) | k2_relset_1(B_120, A_121, k2_funct_1(C_122))!=A_121 | ~v1_funct_2(k2_funct_1(C_122), B_120, A_121) | ~v1_funct_1(k2_funct_1(C_122)) | k2_relset_1(A_121, B_120, C_122)!=B_120 | ~v2_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))) | ~v1_funct_2(C_122, A_121, B_120) | ~v1_funct_1(C_122))), inference(resolution, [status(thm)], [c_135, c_24])).
% 3.75/1.62  tff(c_839, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_833])).
% 3.75/1.62  tff(c_843, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_32, c_74, c_115, c_122, c_549, c_266, c_839])).
% 3.75/1.62  tff(c_30, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.75/1.62  tff(c_108, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_56, c_55, c_55, c_55, c_30])).
% 3.75/1.62  tff(c_130, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_108])).
% 3.75/1.62  tff(c_844, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_130])).
% 3.75/1.62  tff(c_851, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_844])).
% 3.75/1.62  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_40, c_32, c_186, c_851])).
% 3.75/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.62  
% 3.75/1.62  Inference rules
% 3.75/1.62  ----------------------
% 3.75/1.62  #Ref     : 0
% 3.75/1.62  #Sup     : 170
% 3.75/1.62  #Fact    : 0
% 3.75/1.62  #Define  : 0
% 3.75/1.62  #Split   : 4
% 3.75/1.62  #Chain   : 0
% 3.75/1.62  #Close   : 0
% 3.75/1.62  
% 3.75/1.62  Ordering : KBO
% 3.75/1.62  
% 3.75/1.62  Simplification rules
% 3.75/1.62  ----------------------
% 3.75/1.62  #Subsume      : 15
% 3.75/1.62  #Demod        : 435
% 3.75/1.62  #Tautology    : 72
% 3.75/1.62  #SimpNegUnit  : 15
% 3.75/1.62  #BackRed      : 2
% 3.75/1.62  
% 3.75/1.62  #Partial instantiations: 0
% 3.75/1.62  #Strategies tried      : 1
% 3.75/1.62  
% 3.75/1.62  Timing (in seconds)
% 3.75/1.62  ----------------------
% 3.75/1.62  Preprocessing        : 0.34
% 3.75/1.62  Parsing              : 0.18
% 3.75/1.62  CNF conversion       : 0.02
% 3.75/1.62  Main loop            : 0.48
% 3.75/1.62  Inferencing          : 0.17
% 3.75/1.62  Reduction            : 0.18
% 3.75/1.62  Demodulation         : 0.13
% 3.75/1.62  BG Simplification    : 0.03
% 3.75/1.62  Subsumption          : 0.08
% 3.75/1.62  Abstraction          : 0.03
% 3.75/1.62  MUC search           : 0.00
% 3.75/1.62  Cooper               : 0.00
% 3.75/1.62  Total                : 0.87
% 3.75/1.62  Index Insertion      : 0.00
% 3.75/1.62  Index Deletion       : 0.00
% 3.75/1.62  Index Matching       : 0.00
% 3.75/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
