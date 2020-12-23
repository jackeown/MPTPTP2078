%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:34 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  124 (1587 expanded)
%              Number of leaves         :   43 ( 615 expanded)
%              Depth                    :   14
%              Number of atoms          :  286 (5386 expanded)
%              Number of equality atoms :   80 (1195 expanded)
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_76,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_69])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_100,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_58])).

tff(c_106,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_110,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_106])).

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

tff(c_225,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_funct_2(A_78,B_79,D_80,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(D_80,A_78,B_79)
      | ~ v1_funct_1(D_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_227,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_225])).

tff(c_230,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_227])).

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

tff(c_101,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_56])).

tff(c_231,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_funct_1(k2_funct_1(C_81))
      | k2_relset_1(A_82,B_83,C_81) != B_83
      | ~ v2_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(C_81,A_82,B_83)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_234,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_231])).

tff(c_237,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_101,c_234])).

tff(c_238,plain,(
    ! [C_84,B_85,A_86] :
      ( v1_funct_2(k2_funct_1(C_84),B_85,A_86)
      | k2_relset_1(A_86,B_85,C_84) != B_85
      | ~ v2_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85)))
      | ~ v1_funct_2(C_84,A_86,B_85)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_241,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_238])).

tff(c_244,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_101,c_241])).

tff(c_168,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k8_relset_1(A_57,B_58,C_59,D_60) = k10_relat_1(C_59,D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_171,plain,(
    ! [D_60] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_60) = k10_relat_1('#skF_3',D_60) ),
    inference(resolution,[status(thm)],[c_100,c_168])).

tff(c_182,plain,(
    ! [A_64,B_65,C_66] :
      ( k8_relset_1(A_64,B_65,C_66,B_65) = k1_relset_1(A_64,B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_184,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_182])).

tff(c_186,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k10_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_184])).

tff(c_201,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_204,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_100,c_201])).

tff(c_207,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_186,c_204])).

tff(c_208,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_207])).

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

tff(c_314,plain,(
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

tff(c_414,plain,(
    ! [B_116,A_117,C_118,D_119] :
      ( k7_relset_1(B_116,A_117,k2_funct_1(C_118),D_119) = k9_relat_1(k2_funct_1(C_118),D_119)
      | k2_relset_1(A_117,B_116,C_118) != B_116
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ v1_funct_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_314,c_16])).

tff(c_418,plain,(
    ! [D_119] :
      ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_119) = k9_relat_1(k2_funct_1('#skF_3'),D_119)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_100,c_414])).

tff(c_422,plain,(
    ! [D_119] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_119) = k9_relat_1(k2_funct_1('#skF_3'),D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_101,c_418])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_relset_1(A_16,B_17,C_18,A_16) = k2_relset_1(A_16,B_17,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_445,plain,(
    ! [B_124,A_125,C_126] :
      ( k7_relset_1(B_124,A_125,k2_funct_1(C_126),B_124) = k2_relset_1(B_124,A_125,k2_funct_1(C_126))
      | k2_relset_1(A_125,B_124,C_126) != B_124
      | ~ v2_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_2(C_126,A_125,B_124)
      | ~ v1_funct_1(C_126) ) ),
    inference(resolution,[status(thm)],[c_314,c_22])).

tff(c_449,plain,
    ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) = k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_445])).

tff(c_453,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_101,c_422,c_449])).

tff(c_44,plain,(
    ! [C_28,A_26,B_27] :
      ( v1_funct_1(k2_funct_1(C_28))
      | k2_relset_1(A_26,B_27,C_28) != B_27
      | ~ v2_funct_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_494,plain,(
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
    inference(resolution,[status(thm)],[c_314,c_44])).

tff(c_500,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_494])).

tff(c_504,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_101,c_237,c_244,c_453,c_500])).

tff(c_505,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_508,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_505])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_62,c_54,c_508])).

tff(c_513,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_515,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_518,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_515])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_62,c_54,c_208,c_518])).

tff(c_523,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_529,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_453])).

tff(c_514,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_tops_2(A_31,B_32,C_33) = k2_funct_1(C_33)
      | ~ v2_funct_1(C_33)
      | k2_relset_1(A_31,B_32,C_33) != B_32
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_571,plain,(
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
    inference(resolution,[status(thm)],[c_314,c_50])).

tff(c_577,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_571])).

tff(c_581,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_54,c_101,c_237,c_244,c_529,c_514,c_577])).

tff(c_257,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_tops_2(A_91,B_92,C_93) = k2_funct_1(C_93)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(A_91,B_92,C_93) != B_92
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(C_93,A_91,B_92)
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_260,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_257])).

tff(c_263,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_101,c_54,c_260])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_112,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_77,c_76,c_76,c_76,c_52])).

tff(c_264,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_112])).

tff(c_582,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_264])).

tff(c_589,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_582])).

tff(c_592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_62,c_54,c_230,c_589])).

tff(c_593,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_87,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_93,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_87])).

tff(c_97,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_93])).

tff(c_98,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_97])).

tff(c_602,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_98])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.60  
% 3.26/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.60  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.60  
% 3.26/1.60  %Foreground sorts:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Background operators:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Foreground operators:
% 3.26/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.26/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.26/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.26/1.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.60  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.26/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.60  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.26/1.60  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.26/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.26/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.26/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.26/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.26/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.60  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.26/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.60  
% 3.60/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.60/1.62  tff(f_168, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.60/1.62  tff(f_126, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.60/1.62  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.60/1.62  tff(f_106, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.60/1.62  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.60/1.62  tff(f_122, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.60/1.62  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.60/1.62  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.60/1.62  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.60/1.62  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 3.60/1.62  tff(f_38, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.60/1.62  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.60/1.62  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.60/1.62  tff(f_134, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.60/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.60/1.62  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_69, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.60/1.62  tff(c_77, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_69])).
% 3.60/1.62  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_76, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_69])).
% 3.60/1.62  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_100, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_58])).
% 3.60/1.62  tff(c_106, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.60/1.62  tff(c_110, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_106])).
% 3.60/1.62  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_86, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_60])).
% 3.60/1.62  tff(c_225, plain, (![A_78, B_79, D_80]: (r2_funct_2(A_78, B_79, D_80, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(D_80, A_78, B_79) | ~v1_funct_1(D_80))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.60/1.62  tff(c_227, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_225])).
% 3.60/1.62  tff(c_230, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_227])).
% 3.60/1.62  tff(c_12, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.60/1.62  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_101, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_56])).
% 3.60/1.62  tff(c_231, plain, (![C_81, A_82, B_83]: (v1_funct_1(k2_funct_1(C_81)) | k2_relset_1(A_82, B_83, C_81)!=B_83 | ~v2_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(C_81, A_82, B_83) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.60/1.62  tff(c_234, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_231])).
% 3.60/1.62  tff(c_237, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_101, c_234])).
% 3.60/1.62  tff(c_238, plain, (![C_84, B_85, A_86]: (v1_funct_2(k2_funct_1(C_84), B_85, A_86) | k2_relset_1(A_86, B_85, C_84)!=B_85 | ~v2_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))) | ~v1_funct_2(C_84, A_86, B_85) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.60/1.62  tff(c_241, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_238])).
% 3.60/1.62  tff(c_244, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_101, c_241])).
% 3.60/1.62  tff(c_168, plain, (![A_57, B_58, C_59, D_60]: (k8_relset_1(A_57, B_58, C_59, D_60)=k10_relat_1(C_59, D_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.60/1.62  tff(c_171, plain, (![D_60]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_60)=k10_relat_1('#skF_3', D_60))), inference(resolution, [status(thm)], [c_100, c_168])).
% 3.60/1.62  tff(c_182, plain, (![A_64, B_65, C_66]: (k8_relset_1(A_64, B_65, C_66, B_65)=k1_relset_1(A_64, B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.60/1.62  tff(c_184, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_100, c_182])).
% 3.60/1.62  tff(c_186, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k10_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_184])).
% 3.60/1.62  tff(c_201, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.62  tff(c_204, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_100, c_201])).
% 3.60/1.62  tff(c_207, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_186, c_204])).
% 3.60/1.62  tff(c_208, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_207])).
% 3.60/1.62  tff(c_10, plain, (![B_3, A_2]: (k9_relat_1(k2_funct_1(B_3), A_2)=k10_relat_1(B_3, A_2) | ~v2_funct_1(B_3) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.60/1.62  tff(c_4, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.60/1.62  tff(c_314, plain, (![C_99, B_100, A_101]: (m1_subset_1(k2_funct_1(C_99), k1_zfmisc_1(k2_zfmisc_1(B_100, A_101))) | k2_relset_1(A_101, B_100, C_99)!=B_100 | ~v2_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_99, A_101, B_100) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.60/1.62  tff(c_16, plain, (![A_8, B_9, C_10, D_11]: (k7_relset_1(A_8, B_9, C_10, D_11)=k9_relat_1(C_10, D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.60/1.62  tff(c_414, plain, (![B_116, A_117, C_118, D_119]: (k7_relset_1(B_116, A_117, k2_funct_1(C_118), D_119)=k9_relat_1(k2_funct_1(C_118), D_119) | k2_relset_1(A_117, B_116, C_118)!=B_116 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(C_118, A_117, B_116) | ~v1_funct_1(C_118))), inference(resolution, [status(thm)], [c_314, c_16])).
% 3.60/1.62  tff(c_418, plain, (![D_119]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_119)=k9_relat_1(k2_funct_1('#skF_3'), D_119) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_100, c_414])).
% 3.60/1.62  tff(c_422, plain, (![D_119]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_119)=k9_relat_1(k2_funct_1('#skF_3'), D_119))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_101, c_418])).
% 3.60/1.62  tff(c_22, plain, (![A_16, B_17, C_18]: (k7_relset_1(A_16, B_17, C_18, A_16)=k2_relset_1(A_16, B_17, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.60/1.62  tff(c_445, plain, (![B_124, A_125, C_126]: (k7_relset_1(B_124, A_125, k2_funct_1(C_126), B_124)=k2_relset_1(B_124, A_125, k2_funct_1(C_126)) | k2_relset_1(A_125, B_124, C_126)!=B_124 | ~v2_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_2(C_126, A_125, B_124) | ~v1_funct_1(C_126))), inference(resolution, [status(thm)], [c_314, c_22])).
% 3.60/1.62  tff(c_449, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))=k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_445])).
% 3.60/1.62  tff(c_453, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_101, c_422, c_449])).
% 3.60/1.62  tff(c_44, plain, (![C_28, A_26, B_27]: (v1_funct_1(k2_funct_1(C_28)) | k2_relset_1(A_26, B_27, C_28)!=B_27 | ~v2_funct_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.60/1.62  tff(c_494, plain, (![C_138, B_139, A_140]: (v1_funct_1(k2_funct_1(k2_funct_1(C_138))) | k2_relset_1(B_139, A_140, k2_funct_1(C_138))!=A_140 | ~v2_funct_1(k2_funct_1(C_138)) | ~v1_funct_2(k2_funct_1(C_138), B_139, A_140) | ~v1_funct_1(k2_funct_1(C_138)) | k2_relset_1(A_140, B_139, C_138)!=B_139 | ~v2_funct_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))) | ~v1_funct_2(C_138, A_140, B_139) | ~v1_funct_1(C_138))), inference(resolution, [status(thm)], [c_314, c_44])).
% 3.60/1.62  tff(c_500, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_494])).
% 3.60/1.62  tff(c_504, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_101, c_237, c_244, c_453, c_500])).
% 3.60/1.62  tff(c_505, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_504])).
% 3.60/1.62  tff(c_508, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_505])).
% 3.60/1.62  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_62, c_54, c_508])).
% 3.60/1.62  tff(c_513, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_504])).
% 3.60/1.62  tff(c_515, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_513])).
% 3.60/1.62  tff(c_518, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_515])).
% 3.60/1.62  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_62, c_54, c_208, c_518])).
% 3.60/1.62  tff(c_523, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_513])).
% 3.60/1.62  tff(c_529, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_453])).
% 3.60/1.62  tff(c_514, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_504])).
% 3.60/1.62  tff(c_50, plain, (![A_31, B_32, C_33]: (k2_tops_2(A_31, B_32, C_33)=k2_funct_1(C_33) | ~v2_funct_1(C_33) | k2_relset_1(A_31, B_32, C_33)!=B_32 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.60/1.62  tff(c_571, plain, (![B_147, A_148, C_149]: (k2_tops_2(B_147, A_148, k2_funct_1(C_149))=k2_funct_1(k2_funct_1(C_149)) | ~v2_funct_1(k2_funct_1(C_149)) | k2_relset_1(B_147, A_148, k2_funct_1(C_149))!=A_148 | ~v1_funct_2(k2_funct_1(C_149), B_147, A_148) | ~v1_funct_1(k2_funct_1(C_149)) | k2_relset_1(A_148, B_147, C_149)!=B_147 | ~v2_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))) | ~v1_funct_2(C_149, A_148, B_147) | ~v1_funct_1(C_149))), inference(resolution, [status(thm)], [c_314, c_50])).
% 3.60/1.62  tff(c_577, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_571])).
% 3.60/1.62  tff(c_581, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_54, c_101, c_237, c_244, c_529, c_514, c_577])).
% 3.60/1.62  tff(c_257, plain, (![A_91, B_92, C_93]: (k2_tops_2(A_91, B_92, C_93)=k2_funct_1(C_93) | ~v2_funct_1(C_93) | k2_relset_1(A_91, B_92, C_93)!=B_92 | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(C_93, A_91, B_92) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.60/1.62  tff(c_260, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_257])).
% 3.60/1.62  tff(c_263, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_101, c_54, c_260])).
% 3.60/1.62  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_112, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_77, c_76, c_76, c_76, c_52])).
% 3.60/1.62  tff(c_264, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_112])).
% 3.60/1.62  tff(c_582, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_264])).
% 3.60/1.62  tff(c_589, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_582])).
% 3.60/1.62  tff(c_592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_62, c_54, c_230, c_589])).
% 3.60/1.62  tff(c_593, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_207])).
% 3.60/1.62  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.60/1.62  tff(c_87, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.60/1.62  tff(c_93, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_87])).
% 3.60/1.62  tff(c_97, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_93])).
% 3.60/1.62  tff(c_98, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_97])).
% 3.60/1.62  tff(c_602, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_593, c_98])).
% 3.60/1.62  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_602])).
% 3.60/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.62  
% 3.60/1.62  Inference rules
% 3.60/1.62  ----------------------
% 3.60/1.62  #Ref     : 0
% 3.60/1.62  #Sup     : 123
% 3.60/1.62  #Fact    : 0
% 3.60/1.62  #Define  : 0
% 3.60/1.62  #Split   : 4
% 3.60/1.62  #Chain   : 0
% 3.60/1.62  #Close   : 0
% 3.60/1.62  
% 3.60/1.62  Ordering : KBO
% 3.60/1.62  
% 3.60/1.62  Simplification rules
% 3.60/1.62  ----------------------
% 3.60/1.62  #Subsume      : 9
% 3.60/1.62  #Demod        : 146
% 3.60/1.62  #Tautology    : 60
% 3.60/1.62  #SimpNegUnit  : 1
% 3.60/1.62  #BackRed      : 14
% 3.60/1.62  
% 3.60/1.62  #Partial instantiations: 0
% 3.60/1.62  #Strategies tried      : 1
% 3.60/1.62  
% 3.60/1.62  Timing (in seconds)
% 3.60/1.62  ----------------------
% 3.60/1.63  Preprocessing        : 0.41
% 3.60/1.63  Parsing              : 0.22
% 3.60/1.63  CNF conversion       : 0.02
% 3.60/1.63  Main loop            : 0.37
% 3.60/1.63  Inferencing          : 0.13
% 3.60/1.63  Reduction            : 0.12
% 3.60/1.63  Demodulation         : 0.09
% 3.60/1.63  BG Simplification    : 0.02
% 3.60/1.63  Subsumption          : 0.07
% 3.60/1.63  Abstraction          : 0.02
% 3.60/1.63  MUC search           : 0.00
% 3.60/1.63  Cooper               : 0.00
% 3.60/1.63  Total                : 0.83
% 3.60/1.63  Index Insertion      : 0.00
% 3.60/1.63  Index Deletion       : 0.00
% 3.60/1.63  Index Matching       : 0.00
% 3.60/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
