%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:35 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   90 (1074 expanded)
%              Number of leaves         :   31 ( 415 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 (3558 expanded)
%              Number of equality atoms :   44 ( 778 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_138,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_116,axiom,(
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

tff(c_46,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_47,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_55,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_47])).

tff(c_42,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_36])).

tff(c_71,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_71])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_38])).

tff(c_113,plain,(
    ! [A_39,B_40,D_41] :
      ( r2_funct_2(A_39,B_40,D_41,D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_41,A_39,B_40)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_115,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_113])).

tff(c_118,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_115])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_65,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_34])).

tff(c_140,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_tops_2(A_48,B_49,C_50) = k2_funct_1(C_50)
      | ~ v2_funct_1(C_50)
      | k2_relset_1(A_48,B_49,C_50) != B_49
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_146,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_140])).

tff(c_150,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_65,c_32,c_146])).

tff(c_105,plain,(
    ! [A_36,B_37,C_38] :
      ( v1_funct_1(k2_tops_2(A_36,B_37,C_38))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_108,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_105])).

tff(c_111,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_108])).

tff(c_153,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_111])).

tff(c_119,plain,(
    ! [A_42,B_43,C_44] :
      ( v1_funct_2(k2_tops_2(A_42,B_43,C_44),B_43,A_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_121,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_119])).

tff(c_124,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_121])).

tff(c_151,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_124])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k2_tops_2(A_14,B_15,C_16),k1_zfmisc_1(k2_zfmisc_1(B_15,A_14)))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_157,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_20])).

tff(c_161,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_70,c_157])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_tops_2(A_11,B_12,C_13) = k2_funct_1(C_13)
      | ~ v2_funct_1(C_13)
      | k2_relset_1(A_11,B_12,C_13) != B_12
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_165,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_161,c_18])).

tff(c_178,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_151,c_165])).

tff(c_219,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_254,plain,(
    ! [B_67,A_68,C_69] :
      ( k2_relset_1(u1_struct_0(B_67),u1_struct_0(A_68),k2_tops_2(u1_struct_0(A_68),u1_struct_0(B_67),C_69)) = k2_struct_0(A_68)
      | ~ v2_funct_1(C_69)
      | k2_relset_1(u1_struct_0(A_68),u1_struct_0(B_67),C_69) != k2_struct_0(B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_67))))
      | ~ v1_funct_2(C_69,u1_struct_0(A_68),u1_struct_0(B_67))
      | ~ v1_funct_1(C_69)
      | ~ l1_struct_0(B_67)
      | v2_struct_0(B_67)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_275,plain,(
    ! [A_68,C_69] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_68),k2_tops_2(u1_struct_0(A_68),u1_struct_0('#skF_2'),C_69)) = k2_struct_0(A_68)
      | ~ v2_funct_1(C_69)
      | k2_relset_1(u1_struct_0(A_68),u1_struct_0('#skF_2'),C_69) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_69,u1_struct_0(A_68),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_69)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_254])).

tff(c_296,plain,(
    ! [A_68,C_69] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_68),k2_tops_2(u1_struct_0(A_68),k2_struct_0('#skF_2'),C_69)) = k2_struct_0(A_68)
      | ~ v2_funct_1(C_69)
      | k2_relset_1(u1_struct_0(A_68),k2_struct_0('#skF_2'),C_69) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_69,u1_struct_0(A_68),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_69)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54,c_54,c_54,c_54,c_275])).

tff(c_320,plain,(
    ! [A_73,C_74] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_73),k2_tops_2(u1_struct_0(A_73),k2_struct_0('#skF_2'),C_74)) = k2_struct_0(A_73)
      | ~ v2_funct_1(C_74)
      | k2_relset_1(u1_struct_0(A_73),k2_struct_0('#skF_2'),C_74) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_74,u1_struct_0(A_73),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_74)
      | ~ l1_struct_0(A_73) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_296])).

tff(c_329,plain,(
    ! [C_74] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_74)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_74)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_74) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_74,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_74)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_320])).

tff(c_349,plain,(
    ! [C_75] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_75)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_75)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_75) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_75,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_55,c_55,c_55,c_55,c_329])).

tff(c_358,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_349])).

tff(c_362,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64,c_70,c_65,c_32,c_358])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_362])).

tff(c_365,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_371,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_374,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40,c_32,c_374])).

tff(c_379,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_30,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_112,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_55,c_54,c_54,c_54,c_30])).

tff(c_152,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_112])).

tff(c_384,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_152])).

tff(c_462,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_384])).

tff(c_465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40,c_32,c_118,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.12/1.48  
% 3.12/1.48  %Foreground sorts:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Background operators:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Foreground operators:
% 3.12/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.12/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.12/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.12/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.48  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.12/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.12/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.12/1.48  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.12/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.48  
% 3.12/1.50  tff(f_138, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.12/1.50  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.12/1.50  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.12/1.50  tff(f_65, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.12/1.50  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.12/1.50  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.12/1.50  tff(f_81, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.12/1.50  tff(f_93, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.12/1.50  tff(f_116, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.12/1.50  tff(c_46, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_47, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.50  tff(c_55, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_47])).
% 3.12/1.50  tff(c_42, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_54, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_47])).
% 3.12/1.50  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_36])).
% 3.12/1.50  tff(c_71, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.50  tff(c_75, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_71])).
% 3.12/1.50  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_38, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_64, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_38])).
% 3.12/1.50  tff(c_113, plain, (![A_39, B_40, D_41]: (r2_funct_2(A_39, B_40, D_41, D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_41, A_39, B_40) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.12/1.50  tff(c_115, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_113])).
% 3.12/1.50  tff(c_118, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_64, c_115])).
% 3.12/1.50  tff(c_8, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.12/1.50  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.50  tff(c_34, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_65, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_34])).
% 3.12/1.50  tff(c_140, plain, (![A_48, B_49, C_50]: (k2_tops_2(A_48, B_49, C_50)=k2_funct_1(C_50) | ~v2_funct_1(C_50) | k2_relset_1(A_48, B_49, C_50)!=B_49 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.12/1.50  tff(c_146, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_140])).
% 3.12/1.50  tff(c_150, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_64, c_65, c_32, c_146])).
% 3.12/1.50  tff(c_105, plain, (![A_36, B_37, C_38]: (v1_funct_1(k2_tops_2(A_36, B_37, C_38)) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(C_38, A_36, B_37) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.12/1.50  tff(c_108, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_105])).
% 3.12/1.50  tff(c_111, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_64, c_108])).
% 3.12/1.50  tff(c_153, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_111])).
% 3.12/1.50  tff(c_119, plain, (![A_42, B_43, C_44]: (v1_funct_2(k2_tops_2(A_42, B_43, C_44), B_43, A_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(C_44, A_42, B_43) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.12/1.50  tff(c_121, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_119])).
% 3.12/1.50  tff(c_124, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_64, c_121])).
% 3.12/1.50  tff(c_151, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_124])).
% 3.12/1.50  tff(c_20, plain, (![A_14, B_15, C_16]: (m1_subset_1(k2_tops_2(A_14, B_15, C_16), k1_zfmisc_1(k2_zfmisc_1(B_15, A_14))) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.12/1.50  tff(c_157, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_150, c_20])).
% 3.12/1.50  tff(c_161, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_64, c_70, c_157])).
% 3.12/1.50  tff(c_18, plain, (![A_11, B_12, C_13]: (k2_tops_2(A_11, B_12, C_13)=k2_funct_1(C_13) | ~v2_funct_1(C_13) | k2_relset_1(A_11, B_12, C_13)!=B_12 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(C_13, A_11, B_12) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.12/1.50  tff(c_165, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_161, c_18])).
% 3.12/1.50  tff(c_178, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_151, c_165])).
% 3.12/1.50  tff(c_219, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_178])).
% 3.12/1.50  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_254, plain, (![B_67, A_68, C_69]: (k2_relset_1(u1_struct_0(B_67), u1_struct_0(A_68), k2_tops_2(u1_struct_0(A_68), u1_struct_0(B_67), C_69))=k2_struct_0(A_68) | ~v2_funct_1(C_69) | k2_relset_1(u1_struct_0(A_68), u1_struct_0(B_67), C_69)!=k2_struct_0(B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(B_67)))) | ~v1_funct_2(C_69, u1_struct_0(A_68), u1_struct_0(B_67)) | ~v1_funct_1(C_69) | ~l1_struct_0(B_67) | v2_struct_0(B_67) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.50  tff(c_275, plain, (![A_68, C_69]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_68), k2_tops_2(u1_struct_0(A_68), u1_struct_0('#skF_2'), C_69))=k2_struct_0(A_68) | ~v2_funct_1(C_69) | k2_relset_1(u1_struct_0(A_68), u1_struct_0('#skF_2'), C_69)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_69, u1_struct_0(A_68), u1_struct_0('#skF_2')) | ~v1_funct_1(C_69) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_68))), inference(superposition, [status(thm), theory('equality')], [c_54, c_254])).
% 3.12/1.50  tff(c_296, plain, (![A_68, C_69]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_68), k2_tops_2(u1_struct_0(A_68), k2_struct_0('#skF_2'), C_69))=k2_struct_0(A_68) | ~v2_funct_1(C_69) | k2_relset_1(u1_struct_0(A_68), k2_struct_0('#skF_2'), C_69)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_69, u1_struct_0(A_68), k2_struct_0('#skF_2')) | ~v1_funct_1(C_69) | v2_struct_0('#skF_2') | ~l1_struct_0(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54, c_54, c_54, c_54, c_275])).
% 3.12/1.50  tff(c_320, plain, (![A_73, C_74]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_73), k2_tops_2(u1_struct_0(A_73), k2_struct_0('#skF_2'), C_74))=k2_struct_0(A_73) | ~v2_funct_1(C_74) | k2_relset_1(u1_struct_0(A_73), k2_struct_0('#skF_2'), C_74)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_74, u1_struct_0(A_73), k2_struct_0('#skF_2')) | ~v1_funct_1(C_74) | ~l1_struct_0(A_73))), inference(negUnitSimplification, [status(thm)], [c_44, c_296])).
% 3.12/1.50  tff(c_329, plain, (![C_74]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_74))=k2_struct_0('#skF_1') | ~v2_funct_1(C_74) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_74)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_74, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_74) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_320])).
% 3.12/1.50  tff(c_349, plain, (![C_75]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_75))=k2_struct_0('#skF_1') | ~v2_funct_1(C_75) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_75)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_75, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_75))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_55, c_55, c_55, c_55, c_329])).
% 3.12/1.50  tff(c_358, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_150, c_349])).
% 3.12/1.50  tff(c_362, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_64, c_70, c_65, c_32, c_358])).
% 3.12/1.50  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_362])).
% 3.12/1.50  tff(c_365, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_178])).
% 3.12/1.50  tff(c_371, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_365])).
% 3.12/1.50  tff(c_374, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_371])).
% 3.12/1.50  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_40, c_32, c_374])).
% 3.12/1.50  tff(c_379, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_365])).
% 3.12/1.50  tff(c_30, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.12/1.50  tff(c_112, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_55, c_54, c_54, c_54, c_30])).
% 3.12/1.50  tff(c_152, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_112])).
% 3.12/1.50  tff(c_384, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_152])).
% 3.12/1.50  tff(c_462, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_384])).
% 3.12/1.50  tff(c_465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_40, c_32, c_118, c_462])).
% 3.12/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.50  
% 3.12/1.50  Inference rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Ref     : 0
% 3.12/1.50  #Sup     : 87
% 3.12/1.50  #Fact    : 0
% 3.12/1.50  #Define  : 0
% 3.12/1.50  #Split   : 2
% 3.12/1.50  #Chain   : 0
% 3.12/1.50  #Close   : 0
% 3.12/1.50  
% 3.12/1.50  Ordering : KBO
% 3.12/1.50  
% 3.12/1.50  Simplification rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Subsume      : 0
% 3.12/1.50  #Demod        : 229
% 3.12/1.50  #Tautology    : 39
% 3.12/1.50  #SimpNegUnit  : 5
% 3.12/1.50  #BackRed      : 7
% 3.12/1.50  
% 3.12/1.50  #Partial instantiations: 0
% 3.12/1.50  #Strategies tried      : 1
% 3.12/1.50  
% 3.12/1.50  Timing (in seconds)
% 3.12/1.50  ----------------------
% 3.12/1.50  Preprocessing        : 0.36
% 3.12/1.51  Parsing              : 0.19
% 3.12/1.51  CNF conversion       : 0.03
% 3.12/1.51  Main loop            : 0.36
% 3.12/1.51  Inferencing          : 0.12
% 3.12/1.51  Reduction            : 0.13
% 3.12/1.51  Demodulation         : 0.10
% 3.12/1.51  BG Simplification    : 0.02
% 3.12/1.51  Subsumption          : 0.06
% 3.12/1.51  Abstraction          : 0.02
% 3.12/1.51  MUC search           : 0.00
% 3.12/1.51  Cooper               : 0.00
% 3.12/1.51  Total                : 0.76
% 3.12/1.51  Index Insertion      : 0.00
% 3.12/1.51  Index Deletion       : 0.00
% 3.12/1.51  Index Matching       : 0.00
% 3.12/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
