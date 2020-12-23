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
% DateTime   : Thu Dec  3 10:23:45 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 604 expanded)
%              Number of leaves         :   32 ( 243 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 (2013 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_153,negated_conjecture,(
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

tff(f_78,axiom,(
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

tff(f_58,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_74,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_113,axiom,(
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

tff(f_131,axiom,(
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

tff(c_44,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_46])).

tff(c_40,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_53,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53,c_34])).

tff(c_70,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_70])).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_73])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_63,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53,c_36])).

tff(c_95,plain,(
    ! [A_42,B_43,D_44] :
      ( r2_funct_2(A_42,B_43,D_44,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(D_44,A_42,B_43)
      | ~ v1_funct_1(D_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_97,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_95])).

tff(c_100,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_97])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_65,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53,c_32])).

tff(c_101,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_funct_1(k2_funct_1(C_45))
      | k2_relset_1(A_46,B_47,C_45) != B_47
      | ~ v2_funct_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(C_45,A_46,B_47)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_101])).

tff(c_107,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_30,c_65,c_104])).

tff(c_108,plain,(
    ! [C_48,B_49,A_50] :
      ( v1_funct_2(k2_funct_1(C_48),B_49,A_50)
      | k2_relset_1(A_50,B_49,C_48) != B_49
      | ~ v2_funct_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ v1_funct_2(C_48,A_50,B_49)
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_111,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_114,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_30,c_65,c_111])).

tff(c_115,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_tops_2(A_51,B_52,C_53) = k2_funct_1(C_53)
      | ~ v2_funct_1(C_53)
      | k2_relset_1(A_51,B_52,C_53) != B_52
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_118,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_121,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_65,c_30,c_118])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_407,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_437,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),k2_struct_0('#skF_2'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),u1_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_407])).

tff(c_456,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),k2_struct_0('#skF_2'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),k2_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_53,c_53,c_53,c_53,c_437])).

tff(c_467,plain,(
    ! [A_95,C_96] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_95),k2_tops_2(u1_struct_0(A_95),k2_struct_0('#skF_2'),C_96)) = k2_struct_0(A_95)
      | ~ v2_funct_1(C_96)
      | k2_relset_1(u1_struct_0(A_95),k2_struct_0('#skF_2'),C_96) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_96,u1_struct_0(A_95),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_96)
      | ~ l1_struct_0(A_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_456])).

tff(c_476,plain,(
    ! [C_96] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_96)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_96)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_96) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_96,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_96)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_467])).

tff(c_496,plain,(
    ! [C_97] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_97)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_97)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_97) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_97,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_54,c_54,c_476])).

tff(c_505,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_496])).

tff(c_509,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_64,c_65,c_30,c_505])).

tff(c_170,plain,(
    ! [A_64,B_65,C_66] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_64),u1_struct_0(B_65),C_66))
      | ~ v2_funct_1(C_66)
      | k2_relset_1(u1_struct_0(A_64),u1_struct_0(B_65),C_66) != k2_struct_0(B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64),u1_struct_0(B_65))))
      | ~ v1_funct_2(C_66,u1_struct_0(A_64),u1_struct_0(B_65))
      | ~ v1_funct_1(C_66)
      | ~ l1_struct_0(B_65)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_177,plain,(
    ! [B_65,C_66] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_65),C_66))
      | ~ v2_funct_1(C_66)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_65),C_66) != k2_struct_0(B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_65))))
      | ~ v1_funct_2(C_66,u1_struct_0('#skF_1'),u1_struct_0(B_65))
      | ~ v1_funct_1(C_66)
      | ~ l1_struct_0(B_65)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_170])).

tff(c_207,plain,(
    ! [B_70,C_71] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_70),C_71))
      | ~ v2_funct_1(C_71)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_70),C_71) != k2_struct_0(B_70)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_71,k2_struct_0('#skF_1'),u1_struct_0(B_70))
      | ~ v1_funct_1(C_71)
      | ~ l1_struct_0(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_54,c_177])).

tff(c_217,plain,(
    ! [C_71] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_71))
      | ~ v2_funct_1(C_71)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_71) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_71,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_71)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_207])).

tff(c_229,plain,(
    ! [C_73] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_73))
      | ~ v2_funct_1(C_73)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_73) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_73,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_53,c_53,c_53,c_217])).

tff(c_236,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_229])).

tff(c_240,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_65,c_30,c_121,c_236])).

tff(c_127,plain,(
    ! [C_54,B_55,A_56] :
      ( m1_subset_1(k2_funct_1(C_54),k1_zfmisc_1(k2_zfmisc_1(B_55,A_56)))
      | k2_relset_1(A_56,B_55,C_54) != B_55
      | ~ v2_funct_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55)))
      | ~ v1_funct_2(C_54,A_56,B_55)
      | ~ v1_funct_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_tops_2(A_15,B_16,C_17) = k2_funct_1(C_17)
      | ~ v2_funct_1(C_17)
      | k2_relset_1(A_15,B_16,C_17) != B_16
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_594,plain,(
    ! [B_110,A_111,C_112] :
      ( k2_tops_2(B_110,A_111,k2_funct_1(C_112)) = k2_funct_1(k2_funct_1(C_112))
      | ~ v2_funct_1(k2_funct_1(C_112))
      | k2_relset_1(B_110,A_111,k2_funct_1(C_112)) != A_111
      | ~ v1_funct_2(k2_funct_1(C_112),B_110,A_111)
      | ~ v1_funct_1(k2_funct_1(C_112))
      | k2_relset_1(A_111,B_110,C_112) != B_110
      | ~ v2_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110)))
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ v1_funct_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_127,c_20])).

tff(c_600,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_594])).

tff(c_604,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_30,c_65,c_107,c_114,c_509,c_240,c_600])).

tff(c_28,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_94,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_54,c_53,c_53,c_53,c_28])).

tff(c_122,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_94])).

tff(c_605,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_122])).

tff(c_612,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_605])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_38,c_30,c_100,c_612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.47  
% 2.89/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.47  
% 3.21/1.47  %Foreground sorts:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Background operators:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Foreground operators:
% 3.21/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.21/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.21/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.47  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.21/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.21/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.21/1.47  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.21/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.47  
% 3.23/1.49  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.23/1.49  tff(f_153, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.23/1.49  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.23/1.49  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.23/1.49  tff(f_58, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.23/1.49  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.23/1.49  tff(f_74, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.23/1.49  tff(f_90, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.23/1.49  tff(f_113, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.23/1.49  tff(f_131, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 3.23/1.49  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.49  tff(c_44, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_46, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.23/1.49  tff(c_54, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_46])).
% 3.23/1.49  tff(c_40, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_53, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_46])).
% 3.23/1.49  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_53, c_34])).
% 3.23/1.49  tff(c_70, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.49  tff(c_73, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_64, c_70])).
% 3.23/1.49  tff(c_76, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_73])).
% 3.23/1.49  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_63, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_53, c_36])).
% 3.23/1.49  tff(c_95, plain, (![A_42, B_43, D_44]: (r2_funct_2(A_42, B_43, D_44, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(D_44, A_42, B_43) | ~v1_funct_1(D_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.49  tff(c_97, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_95])).
% 3.23/1.49  tff(c_100, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_97])).
% 3.23/1.49  tff(c_6, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.23/1.49  tff(c_32, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_65, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_53, c_32])).
% 3.23/1.49  tff(c_101, plain, (![C_45, A_46, B_47]: (v1_funct_1(k2_funct_1(C_45)) | k2_relset_1(A_46, B_47, C_45)!=B_47 | ~v2_funct_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(C_45, A_46, B_47) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.23/1.49  tff(c_104, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_101])).
% 3.23/1.49  tff(c_107, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_30, c_65, c_104])).
% 3.23/1.49  tff(c_108, plain, (![C_48, B_49, A_50]: (v1_funct_2(k2_funct_1(C_48), B_49, A_50) | k2_relset_1(A_50, B_49, C_48)!=B_49 | ~v2_funct_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~v1_funct_2(C_48, A_50, B_49) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.23/1.49  tff(c_111, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_108])).
% 3.23/1.49  tff(c_114, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_30, c_65, c_111])).
% 3.23/1.49  tff(c_115, plain, (![A_51, B_52, C_53]: (k2_tops_2(A_51, B_52, C_53)=k2_funct_1(C_53) | ~v2_funct_1(C_53) | k2_relset_1(A_51, B_52, C_53)!=B_52 | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(C_53, A_51, B_52) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.23/1.49  tff(c_118, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_115])).
% 3.23/1.49  tff(c_121, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_65, c_30, c_118])).
% 3.23/1.49  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_407, plain, (![B_91, A_92, C_93]: (k2_relset_1(u1_struct_0(B_91), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), u1_struct_0(B_91), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0(B_91), C_93)!=k2_struct_0(B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0(B_91)))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0(B_91)) | ~v1_funct_1(C_93) | ~l1_struct_0(B_91) | v2_struct_0(B_91) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.23/1.49  tff(c_437, plain, (![A_92, C_93]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), k2_struct_0('#skF_2'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0('#skF_2')) | ~v1_funct_1(C_93) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_53, c_407])).
% 3.23/1.49  tff(c_456, plain, (![A_92, C_93]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), k2_struct_0('#skF_2'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), k2_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), k2_struct_0('#skF_2')) | ~v1_funct_1(C_93) | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_53, c_53, c_53, c_53, c_437])).
% 3.23/1.49  tff(c_467, plain, (![A_95, C_96]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_95), k2_tops_2(u1_struct_0(A_95), k2_struct_0('#skF_2'), C_96))=k2_struct_0(A_95) | ~v2_funct_1(C_96) | k2_relset_1(u1_struct_0(A_95), k2_struct_0('#skF_2'), C_96)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_96, u1_struct_0(A_95), k2_struct_0('#skF_2')) | ~v1_funct_1(C_96) | ~l1_struct_0(A_95))), inference(negUnitSimplification, [status(thm)], [c_42, c_456])).
% 3.23/1.49  tff(c_476, plain, (![C_96]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_96))=k2_struct_0('#skF_1') | ~v2_funct_1(C_96) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_96)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_96, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_96) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_467])).
% 3.23/1.49  tff(c_496, plain, (![C_97]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_97))=k2_struct_0('#skF_1') | ~v2_funct_1(C_97) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_97)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_97, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_97))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_54, c_54, c_476])).
% 3.23/1.49  tff(c_505, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_121, c_496])).
% 3.23/1.49  tff(c_509, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_64, c_65, c_30, c_505])).
% 3.23/1.49  tff(c_170, plain, (![A_64, B_65, C_66]: (v2_funct_1(k2_tops_2(u1_struct_0(A_64), u1_struct_0(B_65), C_66)) | ~v2_funct_1(C_66) | k2_relset_1(u1_struct_0(A_64), u1_struct_0(B_65), C_66)!=k2_struct_0(B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64), u1_struct_0(B_65)))) | ~v1_funct_2(C_66, u1_struct_0(A_64), u1_struct_0(B_65)) | ~v1_funct_1(C_66) | ~l1_struct_0(B_65) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.23/1.49  tff(c_177, plain, (![B_65, C_66]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_65), C_66)) | ~v2_funct_1(C_66) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_65), C_66)!=k2_struct_0(B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_65)))) | ~v1_funct_2(C_66, u1_struct_0('#skF_1'), u1_struct_0(B_65)) | ~v1_funct_1(C_66) | ~l1_struct_0(B_65) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_170])).
% 3.23/1.49  tff(c_207, plain, (![B_70, C_71]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_70), C_71)) | ~v2_funct_1(C_71) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_70), C_71)!=k2_struct_0(B_70) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_70)))) | ~v1_funct_2(C_71, k2_struct_0('#skF_1'), u1_struct_0(B_70)) | ~v1_funct_1(C_71) | ~l1_struct_0(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_54, c_177])).
% 3.23/1.49  tff(c_217, plain, (![C_71]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_71)) | ~v2_funct_1(C_71) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_71)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_71, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_71) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_207])).
% 3.23/1.49  tff(c_229, plain, (![C_73]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_73)) | ~v2_funct_1(C_73) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_73)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_73, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_73))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_53, c_53, c_53, c_217])).
% 3.23/1.49  tff(c_236, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_229])).
% 3.23/1.49  tff(c_240, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_65, c_30, c_121, c_236])).
% 3.23/1.49  tff(c_127, plain, (![C_54, B_55, A_56]: (m1_subset_1(k2_funct_1(C_54), k1_zfmisc_1(k2_zfmisc_1(B_55, A_56))) | k2_relset_1(A_56, B_55, C_54)!=B_55 | ~v2_funct_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))) | ~v1_funct_2(C_54, A_56, B_55) | ~v1_funct_1(C_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.23/1.49  tff(c_20, plain, (![A_15, B_16, C_17]: (k2_tops_2(A_15, B_16, C_17)=k2_funct_1(C_17) | ~v2_funct_1(C_17) | k2_relset_1(A_15, B_16, C_17)!=B_16 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.23/1.49  tff(c_594, plain, (![B_110, A_111, C_112]: (k2_tops_2(B_110, A_111, k2_funct_1(C_112))=k2_funct_1(k2_funct_1(C_112)) | ~v2_funct_1(k2_funct_1(C_112)) | k2_relset_1(B_110, A_111, k2_funct_1(C_112))!=A_111 | ~v1_funct_2(k2_funct_1(C_112), B_110, A_111) | ~v1_funct_1(k2_funct_1(C_112)) | k2_relset_1(A_111, B_110, C_112)!=B_110 | ~v2_funct_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))) | ~v1_funct_2(C_112, A_111, B_110) | ~v1_funct_1(C_112))), inference(resolution, [status(thm)], [c_127, c_20])).
% 3.23/1.49  tff(c_600, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_594])).
% 3.23/1.49  tff(c_604, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_30, c_65, c_107, c_114, c_509, c_240, c_600])).
% 3.23/1.49  tff(c_28, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.49  tff(c_94, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_54, c_53, c_53, c_53, c_28])).
% 3.23/1.49  tff(c_122, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_94])).
% 3.23/1.49  tff(c_605, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_122])).
% 3.23/1.49  tff(c_612, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_605])).
% 3.23/1.49  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_38, c_30, c_100, c_612])).
% 3.23/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  Inference rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Ref     : 0
% 3.23/1.49  #Sup     : 120
% 3.23/1.49  #Fact    : 0
% 3.23/1.49  #Define  : 0
% 3.23/1.49  #Split   : 1
% 3.23/1.49  #Chain   : 0
% 3.23/1.49  #Close   : 0
% 3.23/1.49  
% 3.23/1.49  Ordering : KBO
% 3.23/1.49  
% 3.23/1.49  Simplification rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Subsume      : 12
% 3.23/1.49  #Demod        : 278
% 3.23/1.49  #Tautology    : 45
% 3.23/1.49  #SimpNegUnit  : 6
% 3.23/1.49  #BackRed      : 2
% 3.23/1.49  
% 3.23/1.49  #Partial instantiations: 0
% 3.23/1.49  #Strategies tried      : 1
% 3.23/1.49  
% 3.23/1.49  Timing (in seconds)
% 3.23/1.49  ----------------------
% 3.23/1.49  Preprocessing        : 0.34
% 3.23/1.49  Parsing              : 0.17
% 3.23/1.49  CNF conversion       : 0.02
% 3.23/1.49  Main loop            : 0.36
% 3.23/1.49  Inferencing          : 0.13
% 3.23/1.49  Reduction            : 0.13
% 3.23/1.49  Demodulation         : 0.10
% 3.23/1.49  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.06
% 3.23/1.49  Abstraction          : 0.03
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.74
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
