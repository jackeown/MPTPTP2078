%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:45 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   95 (1072 expanded)
%              Number of leaves         :   32 ( 419 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 (3690 expanded)
%              Number of equality atoms :   59 ( 785 expanded)
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

tff(f_147,negated_conjecture,(
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

tff(f_90,axiom,(
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

tff(f_70,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_86,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_125,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_50])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_57,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_38])).

tff(c_69,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_68,c_69])).

tff(c_75,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_72])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_67,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_40])).

tff(c_111,plain,(
    ! [A_39,B_40,D_41] :
      ( r2_funct_2(A_39,B_40,D_41,D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_41,A_39,B_40)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_113,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_111])).

tff(c_116,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67,c_113])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_76,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_36])).

tff(c_117,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_funct_1(k2_funct_1(C_42))
      | k2_relset_1(A_43,B_44,C_42) != B_44
      | ~ v2_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(C_42,A_43,B_44)
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_120,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_123,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67,c_34,c_76,c_120])).

tff(c_124,plain,(
    ! [C_45,B_46,A_47] :
      ( v1_funct_2(k2_funct_1(C_45),B_46,A_47)
      | k2_relset_1(A_47,B_46,C_45) != B_46
      | ~ v2_funct_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46)))
      | ~ v1_funct_2(C_45,A_47,B_46)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_127,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_124])).

tff(c_130,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67,c_34,c_76,c_127])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [C_51,B_52,A_53] :
      ( m1_subset_1(k2_funct_1(C_51),k1_zfmisc_1(k2_zfmisc_1(B_52,A_53)))
      | k2_relset_1(A_53,B_52,C_51) != B_52
      | ~ v2_funct_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52)))
      | ~ v1_funct_2(C_51,A_53,B_52)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_funct_1(k2_funct_1(C_14))
      | k2_relset_1(A_12,B_13,C_14) != B_13
      | ~ v2_funct_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_205,plain,(
    ! [C_67,B_68,A_69] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_67)))
      | k2_relset_1(B_68,A_69,k2_funct_1(C_67)) != A_69
      | ~ v2_funct_1(k2_funct_1(C_67))
      | ~ v1_funct_2(k2_funct_1(C_67),B_68,A_69)
      | ~ v1_funct_1(k2_funct_1(C_67))
      | k2_relset_1(A_69,B_68,C_67) != B_68
      | ~ v2_funct_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68)))
      | ~ v1_funct_2(C_67,A_69,B_68)
      | ~ v1_funct_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_143,c_22])).

tff(c_211,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_205])).

tff(c_215,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67,c_34,c_76,c_123,c_130,c_211])).

tff(c_267,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_270,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_34,c_270])).

tff(c_275,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_306,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_131,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_tops_2(A_48,B_49,C_50) = k2_funct_1(C_50)
      | ~ v2_funct_1(C_50)
      | k2_relset_1(A_48,B_49,C_50) != B_49
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_134,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_131])).

tff(c_137,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67,c_76,c_34,c_134])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_334,plain,(
    ! [B_77,A_78,C_79] :
      ( k2_relset_1(u1_struct_0(B_77),u1_struct_0(A_78),k2_tops_2(u1_struct_0(A_78),u1_struct_0(B_77),C_79)) = k2_struct_0(A_78)
      | ~ v2_funct_1(C_79)
      | k2_relset_1(u1_struct_0(A_78),u1_struct_0(B_77),C_79) != k2_struct_0(B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0(B_77))))
      | ~ v1_funct_2(C_79,u1_struct_0(A_78),u1_struct_0(B_77))
      | ~ v1_funct_1(C_79)
      | ~ l1_struct_0(B_77)
      | v2_struct_0(B_77)
      | ~ l1_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_355,plain,(
    ! [A_78,C_79] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_78),k2_tops_2(u1_struct_0(A_78),u1_struct_0('#skF_2'),C_79)) = k2_struct_0(A_78)
      | ~ v2_funct_1(C_79)
      | k2_relset_1(u1_struct_0(A_78),u1_struct_0('#skF_2'),C_79) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_79,u1_struct_0(A_78),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_79)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_334])).

tff(c_376,plain,(
    ! [A_78,C_79] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_78),k2_tops_2(u1_struct_0(A_78),k2_struct_0('#skF_2'),C_79)) = k2_struct_0(A_78)
      | ~ v2_funct_1(C_79)
      | k2_relset_1(u1_struct_0(A_78),k2_struct_0('#skF_2'),C_79) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_79,u1_struct_0(A_78),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_79)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_57,c_57,c_57,c_57,c_355])).

tff(c_396,plain,(
    ! [A_83,C_84] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_83),k2_tops_2(u1_struct_0(A_83),k2_struct_0('#skF_2'),C_84)) = k2_struct_0(A_83)
      | ~ v2_funct_1(C_84)
      | k2_relset_1(u1_struct_0(A_83),k2_struct_0('#skF_2'),C_84) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_84,u1_struct_0(A_83),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_84)
      | ~ l1_struct_0(A_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_376])).

tff(c_405,plain,(
    ! [C_84] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_84)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_84)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_84) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_84,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_84)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_396])).

tff(c_425,plain,(
    ! [C_85] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_85)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_85)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_85) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_85,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58,c_58,c_58,c_58,c_405])).

tff(c_434,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_425])).

tff(c_438,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67,c_68,c_76,c_34,c_434])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_438])).

tff(c_442,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_276,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_tops_2(A_16,B_17,C_18) = k2_funct_1(C_18)
      | ~ v2_funct_1(C_18)
      | k2_relset_1(A_16,B_17,C_18) != B_17
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_670,plain,(
    ! [B_105,A_106,C_107] :
      ( k2_tops_2(B_105,A_106,k2_funct_1(C_107)) = k2_funct_1(k2_funct_1(C_107))
      | ~ v2_funct_1(k2_funct_1(C_107))
      | k2_relset_1(B_105,A_106,k2_funct_1(C_107)) != A_106
      | ~ v1_funct_2(k2_funct_1(C_107),B_105,A_106)
      | ~ v1_funct_1(k2_funct_1(C_107))
      | k2_relset_1(A_106,B_105,C_107) != B_105
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ v1_funct_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_143,c_26])).

tff(c_676,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_670])).

tff(c_680,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67,c_34,c_76,c_123,c_130,c_442,c_276,c_676])).

tff(c_32,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_110,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_57,c_57,c_57,c_32])).

tff(c_138,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_110])).

tff(c_681,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_138])).

tff(c_688,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_681])).

tff(c_691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_34,c_116,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.52  
% 3.26/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.53  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.53  
% 3.26/1.53  %Foreground sorts:
% 3.26/1.53  
% 3.26/1.53  
% 3.26/1.53  %Background operators:
% 3.26/1.53  
% 3.26/1.53  
% 3.26/1.53  %Foreground operators:
% 3.26/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.26/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.26/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.26/1.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.26/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.53  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.26/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.26/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.26/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.26/1.53  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.26/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.53  
% 3.52/1.55  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.52/1.55  tff(f_147, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.52/1.55  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.52/1.55  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.52/1.55  tff(f_70, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.52/1.55  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.52/1.55  tff(f_86, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.52/1.55  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.52/1.55  tff(f_102, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.52/1.55  tff(f_125, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.52/1.55  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.55  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_50, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.52/1.55  tff(c_58, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_50])).
% 3.52/1.55  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_57, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_50])).
% 3.52/1.55  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_38])).
% 3.52/1.55  tff(c_69, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.55  tff(c_72, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_68, c_69])).
% 3.52/1.55  tff(c_75, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_72])).
% 3.52/1.55  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_67, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_40])).
% 3.52/1.55  tff(c_111, plain, (![A_39, B_40, D_41]: (r2_funct_2(A_39, B_40, D_41, D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_41, A_39, B_40) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.52/1.55  tff(c_113, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_111])).
% 3.52/1.55  tff(c_116, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67, c_113])).
% 3.52/1.55  tff(c_12, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.52/1.55  tff(c_36, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_76, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_36])).
% 3.52/1.55  tff(c_117, plain, (![C_42, A_43, B_44]: (v1_funct_1(k2_funct_1(C_42)) | k2_relset_1(A_43, B_44, C_42)!=B_44 | ~v2_funct_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(C_42, A_43, B_44) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_120, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_117])).
% 3.52/1.55  tff(c_123, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67, c_34, c_76, c_120])).
% 3.52/1.55  tff(c_124, plain, (![C_45, B_46, A_47]: (v1_funct_2(k2_funct_1(C_45), B_46, A_47) | k2_relset_1(A_47, B_46, C_45)!=B_46 | ~v2_funct_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))) | ~v1_funct_2(C_45, A_47, B_46) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_127, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_124])).
% 3.52/1.55  tff(c_130, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67, c_34, c_76, c_127])).
% 3.52/1.55  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.52/1.55  tff(c_143, plain, (![C_51, B_52, A_53]: (m1_subset_1(k2_funct_1(C_51), k1_zfmisc_1(k2_zfmisc_1(B_52, A_53))) | k2_relset_1(A_53, B_52, C_51)!=B_52 | ~v2_funct_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))) | ~v1_funct_2(C_51, A_53, B_52) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_22, plain, (![C_14, A_12, B_13]: (v1_funct_1(k2_funct_1(C_14)) | k2_relset_1(A_12, B_13, C_14)!=B_13 | ~v2_funct_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_2(C_14, A_12, B_13) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_205, plain, (![C_67, B_68, A_69]: (v1_funct_1(k2_funct_1(k2_funct_1(C_67))) | k2_relset_1(B_68, A_69, k2_funct_1(C_67))!=A_69 | ~v2_funct_1(k2_funct_1(C_67)) | ~v1_funct_2(k2_funct_1(C_67), B_68, A_69) | ~v1_funct_1(k2_funct_1(C_67)) | k2_relset_1(A_69, B_68, C_67)!=B_68 | ~v2_funct_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))) | ~v1_funct_2(C_67, A_69, B_68) | ~v1_funct_1(C_67))), inference(resolution, [status(thm)], [c_143, c_22])).
% 3.52/1.55  tff(c_211, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_205])).
% 3.52/1.55  tff(c_215, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67, c_34, c_76, c_123, c_130, c_211])).
% 3.52/1.55  tff(c_267, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_215])).
% 3.52/1.55  tff(c_270, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_267])).
% 3.52/1.55  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_34, c_270])).
% 3.52/1.55  tff(c_275, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_215])).
% 3.52/1.55  tff(c_306, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_275])).
% 3.52/1.55  tff(c_131, plain, (![A_48, B_49, C_50]: (k2_tops_2(A_48, B_49, C_50)=k2_funct_1(C_50) | ~v2_funct_1(C_50) | k2_relset_1(A_48, B_49, C_50)!=B_49 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.52/1.55  tff(c_134, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_131])).
% 3.52/1.55  tff(c_137, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67, c_76, c_34, c_134])).
% 3.52/1.55  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_334, plain, (![B_77, A_78, C_79]: (k2_relset_1(u1_struct_0(B_77), u1_struct_0(A_78), k2_tops_2(u1_struct_0(A_78), u1_struct_0(B_77), C_79))=k2_struct_0(A_78) | ~v2_funct_1(C_79) | k2_relset_1(u1_struct_0(A_78), u1_struct_0(B_77), C_79)!=k2_struct_0(B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0(B_77)))) | ~v1_funct_2(C_79, u1_struct_0(A_78), u1_struct_0(B_77)) | ~v1_funct_1(C_79) | ~l1_struct_0(B_77) | v2_struct_0(B_77) | ~l1_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.52/1.55  tff(c_355, plain, (![A_78, C_79]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_78), k2_tops_2(u1_struct_0(A_78), u1_struct_0('#skF_2'), C_79))=k2_struct_0(A_78) | ~v2_funct_1(C_79) | k2_relset_1(u1_struct_0(A_78), u1_struct_0('#skF_2'), C_79)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_79, u1_struct_0(A_78), u1_struct_0('#skF_2')) | ~v1_funct_1(C_79) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_78))), inference(superposition, [status(thm), theory('equality')], [c_57, c_334])).
% 3.52/1.55  tff(c_376, plain, (![A_78, C_79]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_78), k2_tops_2(u1_struct_0(A_78), k2_struct_0('#skF_2'), C_79))=k2_struct_0(A_78) | ~v2_funct_1(C_79) | k2_relset_1(u1_struct_0(A_78), k2_struct_0('#skF_2'), C_79)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_79, u1_struct_0(A_78), k2_struct_0('#skF_2')) | ~v1_funct_1(C_79) | v2_struct_0('#skF_2') | ~l1_struct_0(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_57, c_57, c_57, c_57, c_355])).
% 3.52/1.55  tff(c_396, plain, (![A_83, C_84]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_83), k2_tops_2(u1_struct_0(A_83), k2_struct_0('#skF_2'), C_84))=k2_struct_0(A_83) | ~v2_funct_1(C_84) | k2_relset_1(u1_struct_0(A_83), k2_struct_0('#skF_2'), C_84)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_84, u1_struct_0(A_83), k2_struct_0('#skF_2')) | ~v1_funct_1(C_84) | ~l1_struct_0(A_83))), inference(negUnitSimplification, [status(thm)], [c_46, c_376])).
% 3.52/1.55  tff(c_405, plain, (![C_84]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_84))=k2_struct_0('#skF_1') | ~v2_funct_1(C_84) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_84)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_84, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_84) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_396])).
% 3.52/1.55  tff(c_425, plain, (![C_85]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_85))=k2_struct_0('#skF_1') | ~v2_funct_1(C_85) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_85)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_85, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_85))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58, c_58, c_58, c_58, c_405])).
% 3.52/1.55  tff(c_434, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_137, c_425])).
% 3.52/1.55  tff(c_438, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67, c_68, c_76, c_34, c_434])).
% 3.52/1.55  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_438])).
% 3.52/1.55  tff(c_442, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_275])).
% 3.52/1.55  tff(c_276, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_215])).
% 3.52/1.55  tff(c_26, plain, (![A_16, B_17, C_18]: (k2_tops_2(A_16, B_17, C_18)=k2_funct_1(C_18) | ~v2_funct_1(C_18) | k2_relset_1(A_16, B_17, C_18)!=B_17 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.52/1.55  tff(c_670, plain, (![B_105, A_106, C_107]: (k2_tops_2(B_105, A_106, k2_funct_1(C_107))=k2_funct_1(k2_funct_1(C_107)) | ~v2_funct_1(k2_funct_1(C_107)) | k2_relset_1(B_105, A_106, k2_funct_1(C_107))!=A_106 | ~v1_funct_2(k2_funct_1(C_107), B_105, A_106) | ~v1_funct_1(k2_funct_1(C_107)) | k2_relset_1(A_106, B_105, C_107)!=B_105 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_107, A_106, B_105) | ~v1_funct_1(C_107))), inference(resolution, [status(thm)], [c_143, c_26])).
% 3.52/1.55  tff(c_676, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_670])).
% 3.52/1.55  tff(c_680, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67, c_34, c_76, c_123, c_130, c_442, c_276, c_676])).
% 3.52/1.55  tff(c_32, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.52/1.55  tff(c_110, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_57, c_57, c_57, c_32])).
% 3.52/1.55  tff(c_138, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_110])).
% 3.52/1.55  tff(c_681, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_680, c_138])).
% 3.52/1.55  tff(c_688, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_681])).
% 3.52/1.55  tff(c_691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_34, c_116, c_688])).
% 3.52/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  Inference rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Ref     : 0
% 3.52/1.55  #Sup     : 136
% 3.52/1.55  #Fact    : 0
% 3.52/1.55  #Define  : 0
% 3.52/1.55  #Split   : 3
% 3.52/1.55  #Chain   : 0
% 3.52/1.55  #Close   : 0
% 3.52/1.55  
% 3.52/1.55  Ordering : KBO
% 3.52/1.55  
% 3.52/1.55  Simplification rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Subsume      : 13
% 3.52/1.55  #Demod        : 326
% 3.52/1.55  #Tautology    : 65
% 3.52/1.55  #SimpNegUnit  : 11
% 3.52/1.55  #BackRed      : 2
% 3.52/1.55  
% 3.52/1.55  #Partial instantiations: 0
% 3.52/1.55  #Strategies tried      : 1
% 3.52/1.55  
% 3.52/1.55  Timing (in seconds)
% 3.52/1.55  ----------------------
% 3.52/1.55  Preprocessing        : 0.35
% 3.52/1.55  Parsing              : 0.18
% 3.52/1.55  CNF conversion       : 0.02
% 3.52/1.55  Main loop            : 0.41
% 3.52/1.55  Inferencing          : 0.14
% 3.52/1.55  Reduction            : 0.14
% 3.52/1.55  Demodulation         : 0.11
% 3.52/1.55  BG Simplification    : 0.03
% 3.52/1.55  Subsumption          : 0.07
% 3.52/1.55  Abstraction          : 0.02
% 3.52/1.55  MUC search           : 0.00
% 3.52/1.55  Cooper               : 0.00
% 3.52/1.55  Total                : 0.80
% 3.52/1.55  Index Insertion      : 0.00
% 3.52/1.55  Index Deletion       : 0.00
% 3.52/1.55  Index Matching       : 0.00
% 3.52/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
