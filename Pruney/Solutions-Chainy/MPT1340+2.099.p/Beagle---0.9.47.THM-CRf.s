%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:45 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  100 (1245 expanded)
%              Number of leaves         :   32 ( 461 expanded)
%              Depth                    :   15
%              Number of atoms          :  257 (4028 expanded)
%              Number of equality atoms :   51 ( 877 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_149,negated_conjecture,(
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

tff(f_62,axiom,(
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
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_109,axiom,(
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

tff(f_127,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_46])).

tff(c_40,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_53,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_34])).

tff(c_61,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_75])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_55,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_36])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_55])).

tff(c_97,plain,(
    ! [A_42,B_43,D_44] :
      ( r2_funct_2(A_42,B_43,D_44,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(D_44,A_42,B_43)
      | ~ v1_funct_1(D_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_97])).

tff(c_102,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66,c_99])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_68,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53,c_32])).

tff(c_133,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_139,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_133])).

tff(c_143,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66,c_68,c_30,c_139])).

tff(c_103,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_1(k2_tops_2(A_45,B_46,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_106,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_103])).

tff(c_109,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66,c_106])).

tff(c_145,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_109])).

tff(c_110,plain,(
    ! [A_48,B_49,C_50] :
      ( v1_funct_2(k2_tops_2(A_48,B_49,C_50),B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_112,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_110])).

tff(c_115,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66,c_112])).

tff(c_144,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_115])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k2_tops_2(A_15,B_16,C_17),k1_zfmisc_1(k2_zfmisc_1(B_16,A_15)))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_150,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_16])).

tff(c_154,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66,c_61,c_150])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_tops_2(A_12,B_13,C_14) = k2_funct_1(C_14)
      | ~ v2_funct_1(C_14)
      | k2_relset_1(A_12,B_13,C_14) != B_13
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_158,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_154,c_14])).

tff(c_171,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_144,c_158])).

tff(c_214,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_528,plain,(
    ! [B_100,A_101,C_102] :
      ( k2_relset_1(u1_struct_0(B_100),u1_struct_0(A_101),k2_tops_2(u1_struct_0(A_101),u1_struct_0(B_100),C_102)) = k2_struct_0(A_101)
      | ~ v2_funct_1(C_102)
      | k2_relset_1(u1_struct_0(A_101),u1_struct_0(B_100),C_102) != k2_struct_0(B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),u1_struct_0(B_100))))
      | ~ v1_funct_2(C_102,u1_struct_0(A_101),u1_struct_0(B_100))
      | ~ v1_funct_1(C_102)
      | ~ l1_struct_0(B_100)
      | v2_struct_0(B_100)
      | ~ l1_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_549,plain,(
    ! [A_101,C_102] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_101),k2_tops_2(u1_struct_0(A_101),u1_struct_0('#skF_2'),C_102)) = k2_struct_0(A_101)
      | ~ v2_funct_1(C_102)
      | k2_relset_1(u1_struct_0(A_101),u1_struct_0('#skF_2'),C_102) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_102,u1_struct_0(A_101),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_102)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_528])).

tff(c_570,plain,(
    ! [A_101,C_102] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_101),k2_tops_2(u1_struct_0(A_101),k2_struct_0('#skF_2'),C_102)) = k2_struct_0(A_101)
      | ~ v2_funct_1(C_102)
      | k2_relset_1(u1_struct_0(A_101),k2_struct_0('#skF_2'),C_102) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_102,u1_struct_0(A_101),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_102)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_53,c_53,c_53,c_53,c_549])).

tff(c_579,plain,(
    ! [A_103,C_104] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_103),k2_tops_2(u1_struct_0(A_103),k2_struct_0('#skF_2'),C_104)) = k2_struct_0(A_103)
      | ~ v2_funct_1(C_104)
      | k2_relset_1(u1_struct_0(A_103),k2_struct_0('#skF_2'),C_104) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_103),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_104)
      | ~ l1_struct_0(A_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_570])).

tff(c_588,plain,(
    ! [C_104] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_104)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_104)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_104) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_104,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_104)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_579])).

tff(c_608,plain,(
    ! [C_105] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_105)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_105)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_105) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_105,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_54,c_54,c_588])).

tff(c_617,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_608])).

tff(c_621,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66,c_61,c_68,c_30,c_617])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_621])).

tff(c_624,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_630,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_659,plain,(
    ! [A_112,B_113,C_114] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_112),u1_struct_0(B_113),C_114))
      | ~ v2_funct_1(C_114)
      | k2_relset_1(u1_struct_0(A_112),u1_struct_0(B_113),C_114) != k2_struct_0(B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112),u1_struct_0(B_113))))
      | ~ v1_funct_2(C_114,u1_struct_0(A_112),u1_struct_0(B_113))
      | ~ v1_funct_1(C_114)
      | ~ l1_struct_0(B_113)
      | ~ l1_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_675,plain,(
    ! [A_112,C_114] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_112),u1_struct_0('#skF_2'),C_114))
      | ~ v2_funct_1(C_114)
      | k2_relset_1(u1_struct_0(A_112),u1_struct_0('#skF_2'),C_114) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_114,u1_struct_0(A_112),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_114)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_659])).

tff(c_740,plain,(
    ! [A_125,C_126] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_125),k2_struct_0('#skF_2'),C_126))
      | ~ v2_funct_1(C_126)
      | k2_relset_1(u1_struct_0(A_125),k2_struct_0('#skF_2'),C_126) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_126,u1_struct_0(A_125),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_126)
      | ~ l1_struct_0(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_53,c_53,c_53,c_675])).

tff(c_747,plain,(
    ! [C_126] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_126))
      | ~ v2_funct_1(C_126)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_126) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_126,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_126)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_740])).

tff(c_756,plain,(
    ! [C_127] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_127))
      | ~ v2_funct_1(C_127)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_127) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_127,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_54,c_747])).

tff(c_763,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_756])).

tff(c_767,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66,c_68,c_30,c_143,c_763])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_767])).

tff(c_770,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_28,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_96,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_54,c_53,c_53,c_53,c_28])).

tff(c_146,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_96])).

tff(c_775,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_146])).

tff(c_828,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_775])).

tff(c_831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_38,c_30,c_102,c_828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.52  
% 3.21/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.52  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.52  
% 3.21/1.52  %Foreground sorts:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Background operators:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Foreground operators:
% 3.21/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.21/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.21/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.52  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.21/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.21/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.21/1.52  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.21/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.52  
% 3.52/1.54  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.52/1.54  tff(f_149, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.52/1.54  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.52/1.54  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.52/1.54  tff(f_58, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.52/1.54  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.52/1.54  tff(f_74, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.52/1.54  tff(f_86, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.52/1.54  tff(f_109, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.52/1.54  tff(f_127, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 3.52/1.54  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.54  tff(c_44, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_46, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.54  tff(c_54, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_46])).
% 3.52/1.54  tff(c_40, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_53, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_46])).
% 3.52/1.54  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_34])).
% 3.52/1.54  tff(c_61, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_60])).
% 3.52/1.54  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.54  tff(c_75, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_61, c_2])).
% 3.52/1.54  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_75])).
% 3.52/1.54  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_55, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_36])).
% 3.52/1.54  tff(c_66, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_55])).
% 3.52/1.54  tff(c_97, plain, (![A_42, B_43, D_44]: (r2_funct_2(A_42, B_43, D_44, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(D_44, A_42, B_43) | ~v1_funct_1(D_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.52/1.54  tff(c_99, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_97])).
% 3.52/1.54  tff(c_102, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66, c_99])).
% 3.52/1.54  tff(c_6, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.52/1.54  tff(c_32, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_68, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_53, c_32])).
% 3.52/1.54  tff(c_133, plain, (![A_54, B_55, C_56]: (k2_tops_2(A_54, B_55, C_56)=k2_funct_1(C_56) | ~v2_funct_1(C_56) | k2_relset_1(A_54, B_55, C_56)!=B_55 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.54  tff(c_139, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_133])).
% 3.52/1.54  tff(c_143, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66, c_68, c_30, c_139])).
% 3.52/1.54  tff(c_103, plain, (![A_45, B_46, C_47]: (v1_funct_1(k2_tops_2(A_45, B_46, C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.54  tff(c_106, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_103])).
% 3.52/1.54  tff(c_109, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66, c_106])).
% 3.52/1.54  tff(c_145, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_109])).
% 3.52/1.54  tff(c_110, plain, (![A_48, B_49, C_50]: (v1_funct_2(k2_tops_2(A_48, B_49, C_50), B_49, A_48) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.54  tff(c_112, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_110])).
% 3.52/1.54  tff(c_115, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66, c_112])).
% 3.52/1.54  tff(c_144, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_115])).
% 3.52/1.54  tff(c_16, plain, (![A_15, B_16, C_17]: (m1_subset_1(k2_tops_2(A_15, B_16, C_17), k1_zfmisc_1(k2_zfmisc_1(B_16, A_15))) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.54  tff(c_150, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_16])).
% 3.52/1.54  tff(c_154, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66, c_61, c_150])).
% 3.52/1.54  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_tops_2(A_12, B_13, C_14)=k2_funct_1(C_14) | ~v2_funct_1(C_14) | k2_relset_1(A_12, B_13, C_14)!=B_13 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_2(C_14, A_12, B_13) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.54  tff(c_158, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_154, c_14])).
% 3.52/1.54  tff(c_171, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_144, c_158])).
% 3.52/1.54  tff(c_214, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_171])).
% 3.52/1.54  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_528, plain, (![B_100, A_101, C_102]: (k2_relset_1(u1_struct_0(B_100), u1_struct_0(A_101), k2_tops_2(u1_struct_0(A_101), u1_struct_0(B_100), C_102))=k2_struct_0(A_101) | ~v2_funct_1(C_102) | k2_relset_1(u1_struct_0(A_101), u1_struct_0(B_100), C_102)!=k2_struct_0(B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101), u1_struct_0(B_100)))) | ~v1_funct_2(C_102, u1_struct_0(A_101), u1_struct_0(B_100)) | ~v1_funct_1(C_102) | ~l1_struct_0(B_100) | v2_struct_0(B_100) | ~l1_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.52/1.54  tff(c_549, plain, (![A_101, C_102]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_101), k2_tops_2(u1_struct_0(A_101), u1_struct_0('#skF_2'), C_102))=k2_struct_0(A_101) | ~v2_funct_1(C_102) | k2_relset_1(u1_struct_0(A_101), u1_struct_0('#skF_2'), C_102)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_102, u1_struct_0(A_101), u1_struct_0('#skF_2')) | ~v1_funct_1(C_102) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_101))), inference(superposition, [status(thm), theory('equality')], [c_53, c_528])).
% 3.52/1.54  tff(c_570, plain, (![A_101, C_102]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_101), k2_tops_2(u1_struct_0(A_101), k2_struct_0('#skF_2'), C_102))=k2_struct_0(A_101) | ~v2_funct_1(C_102) | k2_relset_1(u1_struct_0(A_101), k2_struct_0('#skF_2'), C_102)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_102, u1_struct_0(A_101), k2_struct_0('#skF_2')) | ~v1_funct_1(C_102) | v2_struct_0('#skF_2') | ~l1_struct_0(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_53, c_53, c_53, c_53, c_549])).
% 3.52/1.54  tff(c_579, plain, (![A_103, C_104]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_103), k2_tops_2(u1_struct_0(A_103), k2_struct_0('#skF_2'), C_104))=k2_struct_0(A_103) | ~v2_funct_1(C_104) | k2_relset_1(u1_struct_0(A_103), k2_struct_0('#skF_2'), C_104)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_104, u1_struct_0(A_103), k2_struct_0('#skF_2')) | ~v1_funct_1(C_104) | ~l1_struct_0(A_103))), inference(negUnitSimplification, [status(thm)], [c_42, c_570])).
% 3.52/1.54  tff(c_588, plain, (![C_104]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_104))=k2_struct_0('#skF_1') | ~v2_funct_1(C_104) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_104)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_104, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_104) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_579])).
% 3.52/1.54  tff(c_608, plain, (![C_105]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_105))=k2_struct_0('#skF_1') | ~v2_funct_1(C_105) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_105)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_105, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_105))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_54, c_54, c_588])).
% 3.52/1.54  tff(c_617, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_608])).
% 3.52/1.54  tff(c_621, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66, c_61, c_68, c_30, c_617])).
% 3.52/1.54  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_621])).
% 3.52/1.54  tff(c_624, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_171])).
% 3.52/1.54  tff(c_630, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_624])).
% 3.52/1.54  tff(c_659, plain, (![A_112, B_113, C_114]: (v2_funct_1(k2_tops_2(u1_struct_0(A_112), u1_struct_0(B_113), C_114)) | ~v2_funct_1(C_114) | k2_relset_1(u1_struct_0(A_112), u1_struct_0(B_113), C_114)!=k2_struct_0(B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112), u1_struct_0(B_113)))) | ~v1_funct_2(C_114, u1_struct_0(A_112), u1_struct_0(B_113)) | ~v1_funct_1(C_114) | ~l1_struct_0(B_113) | ~l1_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.54  tff(c_675, plain, (![A_112, C_114]: (v2_funct_1(k2_tops_2(u1_struct_0(A_112), u1_struct_0('#skF_2'), C_114)) | ~v2_funct_1(C_114) | k2_relset_1(u1_struct_0(A_112), u1_struct_0('#skF_2'), C_114)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_114, u1_struct_0(A_112), u1_struct_0('#skF_2')) | ~v1_funct_1(C_114) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_112))), inference(superposition, [status(thm), theory('equality')], [c_53, c_659])).
% 3.52/1.54  tff(c_740, plain, (![A_125, C_126]: (v2_funct_1(k2_tops_2(u1_struct_0(A_125), k2_struct_0('#skF_2'), C_126)) | ~v2_funct_1(C_126) | k2_relset_1(u1_struct_0(A_125), k2_struct_0('#skF_2'), C_126)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_126, u1_struct_0(A_125), k2_struct_0('#skF_2')) | ~v1_funct_1(C_126) | ~l1_struct_0(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_53, c_53, c_53, c_675])).
% 3.52/1.54  tff(c_747, plain, (![C_126]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_126)) | ~v2_funct_1(C_126) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_126)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_126, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_126) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_740])).
% 3.52/1.54  tff(c_756, plain, (![C_127]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_127)) | ~v2_funct_1(C_127) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_127)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_127, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_127))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_54, c_747])).
% 3.52/1.54  tff(c_763, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_756])).
% 3.52/1.54  tff(c_767, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66, c_68, c_30, c_143, c_763])).
% 3.52/1.54  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_630, c_767])).
% 3.52/1.54  tff(c_770, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_624])).
% 3.52/1.54  tff(c_28, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.52/1.54  tff(c_96, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_54, c_53, c_53, c_53, c_28])).
% 3.52/1.54  tff(c_146, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_96])).
% 3.52/1.54  tff(c_775, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_770, c_146])).
% 3.52/1.54  tff(c_828, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_775])).
% 3.52/1.54  tff(c_831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_38, c_30, c_102, c_828])).
% 3.52/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.54  
% 3.52/1.54  Inference rules
% 3.52/1.54  ----------------------
% 3.52/1.54  #Ref     : 0
% 3.52/1.54  #Sup     : 156
% 3.52/1.54  #Fact    : 0
% 3.52/1.54  #Define  : 0
% 3.52/1.54  #Split   : 2
% 3.52/1.54  #Chain   : 0
% 3.52/1.54  #Close   : 0
% 3.52/1.54  
% 3.52/1.54  Ordering : KBO
% 3.52/1.54  
% 3.52/1.54  Simplification rules
% 3.52/1.54  ----------------------
% 3.52/1.54  #Subsume      : 12
% 3.52/1.54  #Demod        : 436
% 3.52/1.54  #Tautology    : 52
% 3.52/1.54  #SimpNegUnit  : 8
% 3.52/1.54  #BackRed      : 9
% 3.52/1.54  
% 3.52/1.54  #Partial instantiations: 0
% 3.52/1.54  #Strategies tried      : 1
% 3.52/1.54  
% 3.52/1.54  Timing (in seconds)
% 3.52/1.54  ----------------------
% 3.52/1.54  Preprocessing        : 0.35
% 3.52/1.54  Parsing              : 0.18
% 3.52/1.54  CNF conversion       : 0.02
% 3.52/1.54  Main loop            : 0.42
% 3.52/1.54  Inferencing          : 0.15
% 3.52/1.54  Reduction            : 0.16
% 3.52/1.54  Demodulation         : 0.12
% 3.52/1.54  BG Simplification    : 0.03
% 3.52/1.54  Subsumption          : 0.07
% 3.52/1.54  Abstraction          : 0.02
% 3.52/1.54  MUC search           : 0.00
% 3.52/1.54  Cooper               : 0.00
% 3.52/1.54  Total                : 0.81
% 3.52/1.54  Index Insertion      : 0.00
% 3.52/1.54  Index Deletion       : 0.00
% 3.52/1.54  Index Matching       : 0.00
% 3.52/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
