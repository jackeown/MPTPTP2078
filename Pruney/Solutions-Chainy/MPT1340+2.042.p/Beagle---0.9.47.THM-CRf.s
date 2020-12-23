%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:35 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 610 expanded)
%              Number of leaves         :   31 ( 242 expanded)
%              Depth                    :   13
%              Number of atoms          :  260 (2016 expanded)
%              Number of equality atoms :   57 ( 448 expanded)
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

tff(f_148,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_69,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_126,axiom,(
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

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_43,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_43])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_61,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_32])).

tff(c_68,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_68])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_52])).

tff(c_91,plain,(
    ! [A_39,B_40,D_41] :
      ( r2_funct_2(A_39,B_40,D_41,D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_41,A_39,B_40)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_91])).

tff(c_96,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_93])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_funct_1(k2_funct_1(A_1)) = A_1
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_63,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_30])).

tff(c_97,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_funct_1(k2_funct_1(C_42))
      | k2_relset_1(A_43,B_44,C_42) != B_44
      | ~ v2_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(C_42,A_43,B_44)
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_100,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_97])).

tff(c_103,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_28,c_63,c_100])).

tff(c_104,plain,(
    ! [C_45,B_46,A_47] :
      ( v1_funct_2(k2_funct_1(C_45),B_46,A_47)
      | k2_relset_1(A_47,B_46,C_45) != B_46
      | ~ v2_funct_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46)))
      | ~ v1_funct_2(C_45,A_47,B_46)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_107,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_104])).

tff(c_110,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_28,c_63,c_107])).

tff(c_111,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_tops_2(A_48,B_49,C_50) = k2_funct_1(C_50)
      | ~ v2_funct_1(C_50)
      | k2_relset_1(A_48,B_49,C_50) != B_49
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_111])).

tff(c_117,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_63,c_28,c_114])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_401,plain,(
    ! [B_88,A_89,C_90] :
      ( k2_relset_1(u1_struct_0(B_88),u1_struct_0(A_89),k2_tops_2(u1_struct_0(A_89),u1_struct_0(B_88),C_90)) = k2_struct_0(A_89)
      | ~ v2_funct_1(C_90)
      | k2_relset_1(u1_struct_0(A_89),u1_struct_0(B_88),C_90) != k2_struct_0(B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89),u1_struct_0(B_88))))
      | ~ v1_funct_2(C_90,u1_struct_0(A_89),u1_struct_0(B_88))
      | ~ v1_funct_1(C_90)
      | ~ l1_struct_0(B_88)
      | v2_struct_0(B_88)
      | ~ l1_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_431,plain,(
    ! [A_89,C_90] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_89),k2_tops_2(u1_struct_0(A_89),k2_struct_0('#skF_2'),C_90)) = k2_struct_0(A_89)
      | ~ v2_funct_1(C_90)
      | k2_relset_1(u1_struct_0(A_89),u1_struct_0('#skF_2'),C_90) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_90,u1_struct_0(A_89),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_90)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_401])).

tff(c_450,plain,(
    ! [A_89,C_90] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_89),k2_tops_2(u1_struct_0(A_89),k2_struct_0('#skF_2'),C_90)) = k2_struct_0(A_89)
      | ~ v2_funct_1(C_90)
      | k2_relset_1(u1_struct_0(A_89),k2_struct_0('#skF_2'),C_90) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_90,u1_struct_0(A_89),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_90)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_50,c_50,c_50,c_431])).

tff(c_461,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),k2_struct_0('#skF_2'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),k2_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0(A_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_450])).

tff(c_470,plain,(
    ! [C_93] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_93)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_461])).

tff(c_490,plain,(
    ! [C_94] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_94)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_94)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_94) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_94,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51,c_51,c_51,c_51,c_470])).

tff(c_499,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_490])).

tff(c_503,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_61,c_63,c_28,c_499])).

tff(c_164,plain,(
    ! [A_61,B_62,C_63] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_61),u1_struct_0(B_62),C_63))
      | ~ v2_funct_1(C_63)
      | k2_relset_1(u1_struct_0(A_61),u1_struct_0(B_62),C_63) != k2_struct_0(B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61),u1_struct_0(B_62))))
      | ~ v1_funct_2(C_63,u1_struct_0(A_61),u1_struct_0(B_62))
      | ~ v1_funct_1(C_63)
      | ~ l1_struct_0(B_62)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_171,plain,(
    ! [B_62,C_63] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_62),C_63))
      | ~ v2_funct_1(C_63)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_62),C_63) != k2_struct_0(B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_62))))
      | ~ v1_funct_2(C_63,u1_struct_0('#skF_1'),u1_struct_0(B_62))
      | ~ v1_funct_1(C_63)
      | ~ l1_struct_0(B_62)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_164])).

tff(c_201,plain,(
    ! [B_67,C_68] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_67),C_68))
      | ~ v2_funct_1(C_68)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_67),C_68) != k2_struct_0(B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_67))))
      | ~ v1_funct_2(C_68,k2_struct_0('#skF_1'),u1_struct_0(B_67))
      | ~ v1_funct_1(C_68)
      | ~ l1_struct_0(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51,c_51,c_51,c_171])).

tff(c_211,plain,(
    ! [C_68] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_68))
      | ~ v2_funct_1(C_68)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_68) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_68,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_68)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_201])).

tff(c_223,plain,(
    ! [C_70] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_70))
      | ~ v2_funct_1(C_70)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_70) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_70,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_50,c_50,c_211])).

tff(c_230,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_223])).

tff(c_234,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_63,c_28,c_117,c_230])).

tff(c_123,plain,(
    ! [C_51,B_52,A_53] :
      ( m1_subset_1(k2_funct_1(C_51),k1_zfmisc_1(k2_zfmisc_1(B_52,A_53)))
      | k2_relset_1(A_53,B_52,C_51) != B_52
      | ~ v2_funct_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52)))
      | ~ v1_funct_2(C_51,A_53,B_52)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_tops_2(A_13,B_14,C_15) = k2_funct_1(C_15)
      | ~ v2_funct_1(C_15)
      | k2_relset_1(A_13,B_14,C_15) != B_14
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_588,plain,(
    ! [B_107,A_108,C_109] :
      ( k2_tops_2(B_107,A_108,k2_funct_1(C_109)) = k2_funct_1(k2_funct_1(C_109))
      | ~ v2_funct_1(k2_funct_1(C_109))
      | k2_relset_1(B_107,A_108,k2_funct_1(C_109)) != A_108
      | ~ v1_funct_2(k2_funct_1(C_109),B_107,A_108)
      | ~ v1_funct_1(k2_funct_1(C_109))
      | k2_relset_1(A_108,B_107,C_109) != B_107
      | ~ v2_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ v1_funct_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_123,c_18])).

tff(c_594,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_588])).

tff(c_598,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62,c_28,c_63,c_103,c_110,c_503,c_234,c_594])).

tff(c_26,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_90,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_51,c_51,c_50,c_50,c_50,c_26])).

tff(c_118,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90])).

tff(c_599,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_118])).

tff(c_606,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_599])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36,c_28,c_96,c_606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.43/1.60  
% 3.43/1.60  %Foreground sorts:
% 3.43/1.60  
% 3.43/1.60  
% 3.43/1.60  %Background operators:
% 3.43/1.60  
% 3.43/1.60  
% 3.43/1.60  %Foreground operators:
% 3.43/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.43/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.43/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.43/1.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.43/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.60  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.43/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.43/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.43/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.43/1.60  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.43/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.60  
% 3.43/1.62  tff(f_148, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.43/1.62  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.43/1.62  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.43/1.62  tff(f_53, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.43/1.62  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.43/1.62  tff(f_69, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.43/1.62  tff(f_85, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.43/1.62  tff(f_108, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.43/1.62  tff(f_126, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 3.43/1.62  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_43, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.43/1.62  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_43])).
% 3.43/1.62  tff(c_38, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_50, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_43])).
% 3.43/1.62  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_61, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_32])).
% 3.43/1.62  tff(c_68, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.62  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_68])).
% 3.43/1.62  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34])).
% 3.43/1.62  tff(c_62, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_52])).
% 3.43/1.62  tff(c_91, plain, (![A_39, B_40, D_41]: (r2_funct_2(A_39, B_40, D_41, D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_41, A_39, B_40) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.43/1.62  tff(c_93, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_91])).
% 3.43/1.62  tff(c_96, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_93])).
% 3.43/1.62  tff(c_2, plain, (![A_1]: (k2_funct_1(k2_funct_1(A_1))=A_1 | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.43/1.62  tff(c_30, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_63, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_30])).
% 3.43/1.62  tff(c_97, plain, (![C_42, A_43, B_44]: (v1_funct_1(k2_funct_1(C_42)) | k2_relset_1(A_43, B_44, C_42)!=B_44 | ~v2_funct_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(C_42, A_43, B_44) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.43/1.62  tff(c_100, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_97])).
% 3.43/1.62  tff(c_103, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_28, c_63, c_100])).
% 3.43/1.62  tff(c_104, plain, (![C_45, B_46, A_47]: (v1_funct_2(k2_funct_1(C_45), B_46, A_47) | k2_relset_1(A_47, B_46, C_45)!=B_46 | ~v2_funct_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))) | ~v1_funct_2(C_45, A_47, B_46) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.43/1.62  tff(c_107, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_104])).
% 3.43/1.62  tff(c_110, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_28, c_63, c_107])).
% 3.43/1.62  tff(c_111, plain, (![A_48, B_49, C_50]: (k2_tops_2(A_48, B_49, C_50)=k2_funct_1(C_50) | ~v2_funct_1(C_50) | k2_relset_1(A_48, B_49, C_50)!=B_49 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.62  tff(c_114, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_111])).
% 3.43/1.62  tff(c_117, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_63, c_28, c_114])).
% 3.43/1.62  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_401, plain, (![B_88, A_89, C_90]: (k2_relset_1(u1_struct_0(B_88), u1_struct_0(A_89), k2_tops_2(u1_struct_0(A_89), u1_struct_0(B_88), C_90))=k2_struct_0(A_89) | ~v2_funct_1(C_90) | k2_relset_1(u1_struct_0(A_89), u1_struct_0(B_88), C_90)!=k2_struct_0(B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89), u1_struct_0(B_88)))) | ~v1_funct_2(C_90, u1_struct_0(A_89), u1_struct_0(B_88)) | ~v1_funct_1(C_90) | ~l1_struct_0(B_88) | v2_struct_0(B_88) | ~l1_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.43/1.62  tff(c_431, plain, (![A_89, C_90]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_89), k2_tops_2(u1_struct_0(A_89), k2_struct_0('#skF_2'), C_90))=k2_struct_0(A_89) | ~v2_funct_1(C_90) | k2_relset_1(u1_struct_0(A_89), u1_struct_0('#skF_2'), C_90)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_90, u1_struct_0(A_89), u1_struct_0('#skF_2')) | ~v1_funct_1(C_90) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_89))), inference(superposition, [status(thm), theory('equality')], [c_50, c_401])).
% 3.43/1.62  tff(c_450, plain, (![A_89, C_90]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_89), k2_tops_2(u1_struct_0(A_89), k2_struct_0('#skF_2'), C_90))=k2_struct_0(A_89) | ~v2_funct_1(C_90) | k2_relset_1(u1_struct_0(A_89), k2_struct_0('#skF_2'), C_90)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_90, u1_struct_0(A_89), k2_struct_0('#skF_2')) | ~v1_funct_1(C_90) | v2_struct_0('#skF_2') | ~l1_struct_0(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_50, c_50, c_50, c_431])).
% 3.43/1.62  tff(c_461, plain, (![A_92, C_93]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), k2_struct_0('#skF_2'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), k2_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), k2_struct_0('#skF_2')) | ~v1_funct_1(C_93) | ~l1_struct_0(A_92))), inference(negUnitSimplification, [status(thm)], [c_40, c_450])).
% 3.43/1.62  tff(c_470, plain, (![C_93]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_93))=k2_struct_0('#skF_1') | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_93) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_461])).
% 3.43/1.62  tff(c_490, plain, (![C_94]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_94))=k2_struct_0('#skF_1') | ~v2_funct_1(C_94) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_94)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_94, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_51, c_51, c_51, c_51, c_470])).
% 3.43/1.62  tff(c_499, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_117, c_490])).
% 3.43/1.62  tff(c_503, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_61, c_63, c_28, c_499])).
% 3.43/1.62  tff(c_164, plain, (![A_61, B_62, C_63]: (v2_funct_1(k2_tops_2(u1_struct_0(A_61), u1_struct_0(B_62), C_63)) | ~v2_funct_1(C_63) | k2_relset_1(u1_struct_0(A_61), u1_struct_0(B_62), C_63)!=k2_struct_0(B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61), u1_struct_0(B_62)))) | ~v1_funct_2(C_63, u1_struct_0(A_61), u1_struct_0(B_62)) | ~v1_funct_1(C_63) | ~l1_struct_0(B_62) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.43/1.62  tff(c_171, plain, (![B_62, C_63]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_62), C_63)) | ~v2_funct_1(C_63) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_62), C_63)!=k2_struct_0(B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_62)))) | ~v1_funct_2(C_63, u1_struct_0('#skF_1'), u1_struct_0(B_62)) | ~v1_funct_1(C_63) | ~l1_struct_0(B_62) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_164])).
% 3.43/1.62  tff(c_201, plain, (![B_67, C_68]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_67), C_68)) | ~v2_funct_1(C_68) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_67), C_68)!=k2_struct_0(B_67) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_67)))) | ~v1_funct_2(C_68, k2_struct_0('#skF_1'), u1_struct_0(B_67)) | ~v1_funct_1(C_68) | ~l1_struct_0(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_51, c_51, c_51, c_171])).
% 3.43/1.62  tff(c_211, plain, (![C_68]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_68)) | ~v2_funct_1(C_68) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_68)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_68, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_68) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_201])).
% 3.43/1.62  tff(c_223, plain, (![C_70]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_70)) | ~v2_funct_1(C_70) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_70)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_70, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_70))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_50, c_50, c_211])).
% 3.43/1.62  tff(c_230, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_223])).
% 3.43/1.62  tff(c_234, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_63, c_28, c_117, c_230])).
% 3.43/1.62  tff(c_123, plain, (![C_51, B_52, A_53]: (m1_subset_1(k2_funct_1(C_51), k1_zfmisc_1(k2_zfmisc_1(B_52, A_53))) | k2_relset_1(A_53, B_52, C_51)!=B_52 | ~v2_funct_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))) | ~v1_funct_2(C_51, A_53, B_52) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.43/1.62  tff(c_18, plain, (![A_13, B_14, C_15]: (k2_tops_2(A_13, B_14, C_15)=k2_funct_1(C_15) | ~v2_funct_1(C_15) | k2_relset_1(A_13, B_14, C_15)!=B_14 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.62  tff(c_588, plain, (![B_107, A_108, C_109]: (k2_tops_2(B_107, A_108, k2_funct_1(C_109))=k2_funct_1(k2_funct_1(C_109)) | ~v2_funct_1(k2_funct_1(C_109)) | k2_relset_1(B_107, A_108, k2_funct_1(C_109))!=A_108 | ~v1_funct_2(k2_funct_1(C_109), B_107, A_108) | ~v1_funct_1(k2_funct_1(C_109)) | k2_relset_1(A_108, B_107, C_109)!=B_107 | ~v2_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_109, A_108, B_107) | ~v1_funct_1(C_109))), inference(resolution, [status(thm)], [c_123, c_18])).
% 3.43/1.62  tff(c_594, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_588])).
% 3.43/1.62  tff(c_598, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62, c_28, c_63, c_103, c_110, c_503, c_234, c_594])).
% 3.43/1.62  tff(c_26, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.43/1.62  tff(c_90, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_51, c_51, c_50, c_50, c_50, c_26])).
% 3.43/1.62  tff(c_118, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_90])).
% 3.43/1.62  tff(c_599, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_598, c_118])).
% 3.43/1.62  tff(c_606, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_599])).
% 3.43/1.62  tff(c_609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_36, c_28, c_96, c_606])).
% 3.43/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.62  
% 3.43/1.62  Inference rules
% 3.43/1.62  ----------------------
% 3.43/1.62  #Ref     : 0
% 3.43/1.62  #Sup     : 120
% 3.43/1.62  #Fact    : 0
% 3.43/1.62  #Define  : 0
% 3.43/1.62  #Split   : 1
% 3.43/1.62  #Chain   : 0
% 3.43/1.62  #Close   : 0
% 3.43/1.62  
% 3.43/1.62  Ordering : KBO
% 3.43/1.62  
% 3.43/1.62  Simplification rules
% 3.43/1.62  ----------------------
% 3.43/1.62  #Subsume      : 12
% 3.43/1.62  #Demod        : 276
% 3.43/1.62  #Tautology    : 45
% 3.43/1.62  #SimpNegUnit  : 6
% 3.43/1.62  #BackRed      : 3
% 3.43/1.62  
% 3.43/1.62  #Partial instantiations: 0
% 3.43/1.62  #Strategies tried      : 1
% 3.43/1.62  
% 3.43/1.62  Timing (in seconds)
% 3.43/1.62  ----------------------
% 3.43/1.62  Preprocessing        : 0.37
% 3.43/1.62  Parsing              : 0.20
% 3.43/1.62  CNF conversion       : 0.03
% 3.43/1.62  Main loop            : 0.47
% 3.43/1.62  Inferencing          : 0.17
% 3.43/1.62  Reduction            : 0.17
% 3.43/1.62  Demodulation         : 0.13
% 3.43/1.62  BG Simplification    : 0.03
% 3.43/1.62  Subsumption          : 0.08
% 3.43/1.62  Abstraction          : 0.03
% 3.43/1.62  MUC search           : 0.00
% 3.43/1.62  Cooper               : 0.00
% 3.43/1.62  Total                : 0.88
% 3.43/1.62  Index Insertion      : 0.00
% 3.43/1.62  Index Deletion       : 0.00
% 3.43/1.62  Index Matching       : 0.00
% 3.43/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
