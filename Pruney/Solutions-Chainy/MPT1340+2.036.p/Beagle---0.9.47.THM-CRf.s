%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:35 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  122 (1580 expanded)
%              Number of leaves         :   43 ( 613 expanded)
%              Depth                    :   14
%              Number of atoms          :  283 (5368 expanded)
%              Number of equality atoms :   80 (1191 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

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

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

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

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_69,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_77,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_69])).

tff(c_76,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_69])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_94,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_58])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_14])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_60])).

tff(c_202,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_funct_2(A_78,B_79,D_80,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(D_80,A_78,B_79)
      | ~ v1_funct_1(D_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_204,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_202])).

tff(c_207,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_204])).

tff(c_12,plain,(
    ! [A_4] :
      ( k2_funct_1(k2_funct_1(A_4)) = A_4
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_88,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_56])).

tff(c_218,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_funct_1(k2_funct_1(C_81))
      | k2_relset_1(A_82,B_83,C_81) != B_83
      | ~ v2_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(C_81,A_82,B_83)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_221,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_218])).

tff(c_224,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_88,c_221])).

tff(c_248,plain,(
    ! [C_90,B_91,A_92] :
      ( v1_funct_2(k2_funct_1(C_90),B_91,A_92)
      | k2_relset_1(A_92,B_91,C_90) != B_91
      | ~ v2_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91)))
      | ~ v1_funct_2(C_90,A_92,B_91)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_251,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_248])).

tff(c_254,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_88,c_251])).

tff(c_143,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k8_relset_1(A_52,B_53,C_54,D_55) = k10_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_146,plain,(
    ! [D_55] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_55) = k10_relat_1('#skF_3',D_55) ),
    inference(resolution,[status(thm)],[c_94,c_143])).

tff(c_180,plain,(
    ! [A_69,B_70,C_71] :
      ( k8_relset_1(A_69,B_70,C_71,B_70) = k1_relset_1(A_69,B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_182,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_180])).

tff(c_184,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k10_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_182])).

tff(c_195,plain,(
    ! [B_75,A_76,C_77] :
      ( k1_xboole_0 = B_75
      | k1_relset_1(A_76,B_75,C_77) = A_76
      | ~ v1_funct_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_198,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_94,c_195])).

tff(c_201,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_184,c_198])).

tff(c_208,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_10,plain,(
    ! [B_3,A_2] :
      ( k9_relat_1(k2_funct_1(B_3),A_2) = k10_relat_1(B_3,A_2)
      | ~ v2_funct_1(B_3)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_301,plain,(
    ! [C_99,B_100,A_101] :
      ( m1_subset_1(k2_funct_1(C_99),k1_zfmisc_1(k2_zfmisc_1(B_100,A_101)))
      | k2_relset_1(A_101,B_100,C_99) != B_100
      | ~ v2_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_99,A_101,B_100)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k7_relset_1(A_8,B_9,C_10,D_11) = k9_relat_1(C_10,D_11)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_377,plain,(
    ! [B_109,A_110,C_111,D_112] :
      ( k7_relset_1(B_109,A_110,k2_funct_1(C_111),D_112) = k9_relat_1(k2_funct_1(C_111),D_112)
      | k2_relset_1(A_110,B_109,C_111) != B_109
      | ~ v2_funct_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ v1_funct_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_301,c_16])).

tff(c_381,plain,(
    ! [D_112] :
      ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_112) = k9_relat_1(k2_funct_1('#skF_3'),D_112)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_94,c_377])).

tff(c_385,plain,(
    ! [D_112] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_112) = k9_relat_1(k2_funct_1('#skF_3'),D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_88,c_381])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_relset_1(A_16,B_17,C_18,A_16) = k2_relset_1(A_16,B_17,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_425,plain,(
    ! [B_123,A_124,C_125] :
      ( k7_relset_1(B_123,A_124,k2_funct_1(C_125),B_123) = k2_relset_1(B_123,A_124,k2_funct_1(C_125))
      | k2_relset_1(A_124,B_123,C_125) != B_123
      | ~ v2_funct_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(C_125,A_124,B_123)
      | ~ v1_funct_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_301,c_22])).

tff(c_429,plain,
    ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) = k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_425])).

tff(c_433,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_88,c_385,c_429])).

tff(c_44,plain,(
    ! [C_28,A_26,B_27] :
      ( v1_funct_1(k2_funct_1(C_28))
      | k2_relset_1(A_26,B_27,C_28) != B_27
      | ~ v2_funct_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_481,plain,(
    ! [C_138,B_139,A_140] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_138)))
      | k2_relset_1(B_139,A_140,k2_funct_1(C_138)) != A_140
      | ~ v2_funct_1(k2_funct_1(C_138))
      | ~ v1_funct_2(k2_funct_1(C_138),B_139,A_140)
      | ~ v1_funct_1(k2_funct_1(C_138))
      | k2_relset_1(A_140,B_139,C_138) != B_139
      | ~ v2_funct_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139)))
      | ~ v1_funct_2(C_138,A_140,B_139)
      | ~ v1_funct_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_301,c_44])).

tff(c_487,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_481])).

tff(c_491,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_88,c_224,c_254,c_433,c_487])).

tff(c_492,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_495,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_492])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_62,c_54,c_495])).

tff(c_500,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_509,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_512,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_509])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_62,c_54,c_208,c_512])).

tff(c_517,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_523,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_433])).

tff(c_501,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_tops_2(A_31,B_32,C_33) = k2_funct_1(C_33)
      | ~ v2_funct_1(C_33)
      | k2_relset_1(A_31,B_32,C_33) != B_32
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_558,plain,(
    ! [B_147,A_148,C_149] :
      ( k2_tops_2(B_147,A_148,k2_funct_1(C_149)) = k2_funct_1(k2_funct_1(C_149))
      | ~ v2_funct_1(k2_funct_1(C_149))
      | k2_relset_1(B_147,A_148,k2_funct_1(C_149)) != A_148
      | ~ v1_funct_2(k2_funct_1(C_149),B_147,A_148)
      | ~ v1_funct_1(k2_funct_1(C_149))
      | k2_relset_1(A_148,B_147,C_149) != B_147
      | ~ v2_funct_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147)))
      | ~ v1_funct_2(C_149,A_148,B_147)
      | ~ v1_funct_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_301,c_50])).

tff(c_564,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_558])).

tff(c_568,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_88,c_224,c_254,c_523,c_501,c_564])).

tff(c_289,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_tops_2(A_96,B_97,C_98) = k2_funct_1(C_98)
      | ~ v2_funct_1(C_98)
      | k2_relset_1(A_96,B_97,C_98) != B_97
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_292,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_289])).

tff(c_295,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_88,c_54,c_292])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_128,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_77,c_76,c_76,c_76,c_52])).

tff(c_296,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_128])).

tff(c_569,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_296])).

tff(c_576,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_569])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_62,c_54,c_207,c_576])).

tff(c_580,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_48,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k2_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_595,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_48])).

tff(c_599,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2,c_595])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:57:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.48  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.48  
% 3.21/1.48  %Foreground sorts:
% 3.21/1.48  
% 3.21/1.48  
% 3.21/1.48  %Background operators:
% 3.21/1.48  
% 3.21/1.48  
% 3.21/1.48  %Foreground operators:
% 3.21/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.21/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.21/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.21/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.21/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.48  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.21/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.21/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.21/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.21/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.21/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.21/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.48  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.21/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.48  
% 3.21/1.50  tff(f_168, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.21/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.21/1.50  tff(f_126, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.21/1.50  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.21/1.50  tff(f_106, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.21/1.50  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.21/1.50  tff(f_122, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.21/1.50  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.21/1.50  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.21/1.50  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.21/1.50  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 3.21/1.50  tff(f_38, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.21/1.50  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.21/1.50  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.21/1.50  tff(f_134, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.21/1.50  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.21/1.50  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_69, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.21/1.50  tff(c_77, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_69])).
% 3.21/1.50  tff(c_76, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_69])).
% 3.21/1.50  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_94, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_58])).
% 3.21/1.50  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.50  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_14])).
% 3.21/1.50  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_86, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_60])).
% 3.21/1.50  tff(c_202, plain, (![A_78, B_79, D_80]: (r2_funct_2(A_78, B_79, D_80, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(D_80, A_78, B_79) | ~v1_funct_1(D_80))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.21/1.50  tff(c_204, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_202])).
% 3.21/1.50  tff(c_207, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_204])).
% 3.21/1.50  tff(c_12, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.21/1.50  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_88, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_56])).
% 3.21/1.50  tff(c_218, plain, (![C_81, A_82, B_83]: (v1_funct_1(k2_funct_1(C_81)) | k2_relset_1(A_82, B_83, C_81)!=B_83 | ~v2_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(C_81, A_82, B_83) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.21/1.50  tff(c_221, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_218])).
% 3.21/1.50  tff(c_224, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_88, c_221])).
% 3.21/1.50  tff(c_248, plain, (![C_90, B_91, A_92]: (v1_funct_2(k2_funct_1(C_90), B_91, A_92) | k2_relset_1(A_92, B_91, C_90)!=B_91 | ~v2_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))) | ~v1_funct_2(C_90, A_92, B_91) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.21/1.50  tff(c_251, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_248])).
% 3.21/1.50  tff(c_254, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_88, c_251])).
% 3.21/1.50  tff(c_143, plain, (![A_52, B_53, C_54, D_55]: (k8_relset_1(A_52, B_53, C_54, D_55)=k10_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.21/1.50  tff(c_146, plain, (![D_55]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_55)=k10_relat_1('#skF_3', D_55))), inference(resolution, [status(thm)], [c_94, c_143])).
% 3.21/1.50  tff(c_180, plain, (![A_69, B_70, C_71]: (k8_relset_1(A_69, B_70, C_71, B_70)=k1_relset_1(A_69, B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.50  tff(c_182, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_94, c_180])).
% 3.21/1.50  tff(c_184, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k10_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_182])).
% 3.21/1.50  tff(c_195, plain, (![B_75, A_76, C_77]: (k1_xboole_0=B_75 | k1_relset_1(A_76, B_75, C_77)=A_76 | ~v1_funct_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.50  tff(c_198, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_94, c_195])).
% 3.21/1.50  tff(c_201, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_184, c_198])).
% 3.21/1.50  tff(c_208, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_201])).
% 3.21/1.50  tff(c_10, plain, (![B_3, A_2]: (k9_relat_1(k2_funct_1(B_3), A_2)=k10_relat_1(B_3, A_2) | ~v2_funct_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.50  tff(c_4, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.50  tff(c_301, plain, (![C_99, B_100, A_101]: (m1_subset_1(k2_funct_1(C_99), k1_zfmisc_1(k2_zfmisc_1(B_100, A_101))) | k2_relset_1(A_101, B_100, C_99)!=B_100 | ~v2_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_99, A_101, B_100) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.21/1.50  tff(c_16, plain, (![A_8, B_9, C_10, D_11]: (k7_relset_1(A_8, B_9, C_10, D_11)=k9_relat_1(C_10, D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.50  tff(c_377, plain, (![B_109, A_110, C_111, D_112]: (k7_relset_1(B_109, A_110, k2_funct_1(C_111), D_112)=k9_relat_1(k2_funct_1(C_111), D_112) | k2_relset_1(A_110, B_109, C_111)!=B_109 | ~v2_funct_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_2(C_111, A_110, B_109) | ~v1_funct_1(C_111))), inference(resolution, [status(thm)], [c_301, c_16])).
% 3.21/1.50  tff(c_381, plain, (![D_112]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_112)=k9_relat_1(k2_funct_1('#skF_3'), D_112) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_94, c_377])).
% 3.21/1.50  tff(c_385, plain, (![D_112]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_112)=k9_relat_1(k2_funct_1('#skF_3'), D_112))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_88, c_381])).
% 3.21/1.50  tff(c_22, plain, (![A_16, B_17, C_18]: (k7_relset_1(A_16, B_17, C_18, A_16)=k2_relset_1(A_16, B_17, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.50  tff(c_425, plain, (![B_123, A_124, C_125]: (k7_relset_1(B_123, A_124, k2_funct_1(C_125), B_123)=k2_relset_1(B_123, A_124, k2_funct_1(C_125)) | k2_relset_1(A_124, B_123, C_125)!=B_123 | ~v2_funct_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(C_125, A_124, B_123) | ~v1_funct_1(C_125))), inference(resolution, [status(thm)], [c_301, c_22])).
% 3.21/1.50  tff(c_429, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))=k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_425])).
% 3.21/1.50  tff(c_433, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_88, c_385, c_429])).
% 3.21/1.50  tff(c_44, plain, (![C_28, A_26, B_27]: (v1_funct_1(k2_funct_1(C_28)) | k2_relset_1(A_26, B_27, C_28)!=B_27 | ~v2_funct_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.21/1.50  tff(c_481, plain, (![C_138, B_139, A_140]: (v1_funct_1(k2_funct_1(k2_funct_1(C_138))) | k2_relset_1(B_139, A_140, k2_funct_1(C_138))!=A_140 | ~v2_funct_1(k2_funct_1(C_138)) | ~v1_funct_2(k2_funct_1(C_138), B_139, A_140) | ~v1_funct_1(k2_funct_1(C_138)) | k2_relset_1(A_140, B_139, C_138)!=B_139 | ~v2_funct_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))) | ~v1_funct_2(C_138, A_140, B_139) | ~v1_funct_1(C_138))), inference(resolution, [status(thm)], [c_301, c_44])).
% 3.21/1.50  tff(c_487, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_481])).
% 3.21/1.50  tff(c_491, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_88, c_224, c_254, c_433, c_487])).
% 3.21/1.50  tff(c_492, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_491])).
% 3.21/1.50  tff(c_495, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_492])).
% 3.21/1.50  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_62, c_54, c_495])).
% 3.21/1.50  tff(c_500, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_491])).
% 3.21/1.50  tff(c_509, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_500])).
% 3.21/1.50  tff(c_512, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_509])).
% 3.21/1.50  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_62, c_54, c_208, c_512])).
% 3.21/1.50  tff(c_517, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_500])).
% 3.21/1.50  tff(c_523, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_433])).
% 3.21/1.50  tff(c_501, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_491])).
% 3.21/1.50  tff(c_50, plain, (![A_31, B_32, C_33]: (k2_tops_2(A_31, B_32, C_33)=k2_funct_1(C_33) | ~v2_funct_1(C_33) | k2_relset_1(A_31, B_32, C_33)!=B_32 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.50  tff(c_558, plain, (![B_147, A_148, C_149]: (k2_tops_2(B_147, A_148, k2_funct_1(C_149))=k2_funct_1(k2_funct_1(C_149)) | ~v2_funct_1(k2_funct_1(C_149)) | k2_relset_1(B_147, A_148, k2_funct_1(C_149))!=A_148 | ~v1_funct_2(k2_funct_1(C_149), B_147, A_148) | ~v1_funct_1(k2_funct_1(C_149)) | k2_relset_1(A_148, B_147, C_149)!=B_147 | ~v2_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))) | ~v1_funct_2(C_149, A_148, B_147) | ~v1_funct_1(C_149))), inference(resolution, [status(thm)], [c_301, c_50])).
% 3.21/1.50  tff(c_564, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_558])).
% 3.21/1.50  tff(c_568, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_88, c_224, c_254, c_523, c_501, c_564])).
% 3.21/1.50  tff(c_289, plain, (![A_96, B_97, C_98]: (k2_tops_2(A_96, B_97, C_98)=k2_funct_1(C_98) | ~v2_funct_1(C_98) | k2_relset_1(A_96, B_97, C_98)!=B_97 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.50  tff(c_292, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_289])).
% 3.21/1.50  tff(c_295, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_88, c_54, c_292])).
% 3.21/1.50  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.21/1.50  tff(c_128, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_77, c_76, c_76, c_76, c_52])).
% 3.21/1.50  tff(c_296, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_128])).
% 3.21/1.50  tff(c_569, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_568, c_296])).
% 3.21/1.50  tff(c_576, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_569])).
% 3.21/1.50  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_62, c_54, c_207, c_576])).
% 3.21/1.50  tff(c_580, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_201])).
% 3.21/1.50  tff(c_48, plain, (![A_30]: (~v1_xboole_0(k2_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.21/1.50  tff(c_595, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_580, c_48])).
% 3.21/1.50  tff(c_599, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2, c_595])).
% 3.21/1.50  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_599])).
% 3.21/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  Inference rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Ref     : 0
% 3.21/1.50  #Sup     : 124
% 3.21/1.50  #Fact    : 0
% 3.21/1.50  #Define  : 0
% 3.21/1.50  #Split   : 3
% 3.21/1.50  #Chain   : 0
% 3.21/1.50  #Close   : 0
% 3.21/1.50  
% 3.21/1.50  Ordering : KBO
% 3.21/1.50  
% 3.21/1.50  Simplification rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Subsume      : 9
% 3.21/1.50  #Demod        : 145
% 3.21/1.50  #Tautology    : 61
% 3.21/1.50  #SimpNegUnit  : 1
% 3.21/1.50  #BackRed      : 14
% 3.21/1.50  
% 3.21/1.50  #Partial instantiations: 0
% 3.21/1.50  #Strategies tried      : 1
% 3.21/1.50  
% 3.21/1.50  Timing (in seconds)
% 3.21/1.50  ----------------------
% 3.21/1.50  Preprocessing        : 0.35
% 3.21/1.50  Parsing              : 0.19
% 3.21/1.50  CNF conversion       : 0.02
% 3.21/1.50  Main loop            : 0.37
% 3.21/1.50  Inferencing          : 0.13
% 3.21/1.50  Reduction            : 0.12
% 3.21/1.50  Demodulation         : 0.08
% 3.21/1.50  BG Simplification    : 0.02
% 3.21/1.50  Subsumption          : 0.07
% 3.21/1.50  Abstraction          : 0.02
% 3.21/1.50  MUC search           : 0.00
% 3.21/1.50  Cooper               : 0.00
% 3.21/1.50  Total                : 0.76
% 3.21/1.50  Index Insertion      : 0.00
% 3.21/1.50  Index Deletion       : 0.00
% 3.21/1.50  Index Matching       : 0.00
% 3.21/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
