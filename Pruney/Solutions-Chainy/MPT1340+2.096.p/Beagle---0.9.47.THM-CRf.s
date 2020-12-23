%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:44 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  126 (1618 expanded)
%              Number of leaves         :   44 ( 616 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 (5415 expanded)
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

tff(f_173,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_111,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_127,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_95,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_72,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_80,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_72])).

tff(c_79,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_72])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_60])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_85,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_62])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_85])).

tff(c_219,plain,(
    ! [A_81,B_82,D_83] :
      ( r2_funct_2(A_81,B_82,D_83,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_2(D_83,A_81,B_82)
      | ~ v1_funct_1(D_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_221,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_219])).

tff(c_224,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_221])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_funct_1(k2_funct_1(A_9)) = A_9
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_92,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_79,c_58])).

tff(c_225,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_funct_1(k2_funct_1(C_84))
      | k2_relset_1(A_85,B_86,C_84) != B_86
      | ~ v2_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_228,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_225])).

tff(c_231,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_56,c_92,c_228])).

tff(c_238,plain,(
    ! [C_89,B_90,A_91] :
      ( v1_funct_2(k2_funct_1(C_89),B_90,A_91)
      | k2_relset_1(A_91,B_90,C_89) != B_90
      | ~ v2_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90)))
      | ~ v1_funct_2(C_89,A_91,B_90)
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_241,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_238])).

tff(c_244,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_56,c_92,c_241])).

tff(c_162,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k8_relset_1(A_60,B_61,C_62,D_63) = k10_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_165,plain,(
    ! [D_63] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_63) = k10_relat_1('#skF_3',D_63) ),
    inference(resolution,[status(thm)],[c_98,c_162])).

tff(c_177,plain,(
    ! [A_69,B_70,C_71] :
      ( k8_relset_1(A_69,B_70,C_71,B_70) = k1_relset_1(A_69,B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_179,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_177])).

tff(c_181,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k10_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_179])).

tff(c_195,plain,(
    ! [B_75,A_76,C_77] :
      ( k1_xboole_0 = B_75
      | k1_relset_1(A_76,B_75,C_77) = A_76
      | ~ v1_funct_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_198,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_98,c_195])).

tff(c_201,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_181,c_198])).

tff(c_202,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k9_relat_1(k2_funct_1(B_8),A_7) = k10_relat_1(B_8,A_7)
      | ~ v2_funct_1(B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_308,plain,(
    ! [C_102,B_103,A_104] :
      ( m1_subset_1(k2_funct_1(C_102),k1_zfmisc_1(k2_zfmisc_1(B_103,A_104)))
      | k2_relset_1(A_104,B_103,C_102) != B_103
      | ~ v2_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_2(C_102,A_104,B_103)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k7_relset_1(A_10,B_11,C_12,D_13) = k9_relat_1(C_12,D_13)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_386,plain,(
    ! [B_112,A_113,C_114,D_115] :
      ( k7_relset_1(B_112,A_113,k2_funct_1(C_114),D_115) = k9_relat_1(k2_funct_1(C_114),D_115)
      | k2_relset_1(A_113,B_112,C_114) != B_112
      | ~ v2_funct_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112)))
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ v1_funct_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_308,c_18])).

tff(c_390,plain,(
    ! [D_115] :
      ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_115) = k9_relat_1(k2_funct_1('#skF_3'),D_115)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_98,c_386])).

tff(c_394,plain,(
    ! [D_115] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_115) = k9_relat_1(k2_funct_1('#skF_3'),D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_56,c_92,c_390])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] :
      ( k7_relset_1(A_18,B_19,C_20,A_18) = k2_relset_1(A_18,B_19,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_447,plain,(
    ! [B_129,A_130,C_131] :
      ( k7_relset_1(B_129,A_130,k2_funct_1(C_131),B_129) = k2_relset_1(B_129,A_130,k2_funct_1(C_131))
      | k2_relset_1(A_130,B_129,C_131) != B_129
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_2(C_131,A_130,B_129)
      | ~ v1_funct_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_308,c_24])).

tff(c_451,plain,
    ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) = k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_447])).

tff(c_455,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_56,c_92,c_394,c_451])).

tff(c_46,plain,(
    ! [C_30,A_28,B_29] :
      ( v1_funct_1(k2_funct_1(C_30))
      | k2_relset_1(A_28,B_29,C_30) != B_29
      | ~ v2_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_490,plain,(
    ! [C_141,B_142,A_143] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_141)))
      | k2_relset_1(B_142,A_143,k2_funct_1(C_141)) != A_143
      | ~ v2_funct_1(k2_funct_1(C_141))
      | ~ v1_funct_2(k2_funct_1(C_141),B_142,A_143)
      | ~ v1_funct_1(k2_funct_1(C_141))
      | k2_relset_1(A_143,B_142,C_141) != B_142
      | ~ v2_funct_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142)))
      | ~ v1_funct_2(C_141,A_143,B_142)
      | ~ v1_funct_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_308,c_46])).

tff(c_496,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_490])).

tff(c_500,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_56,c_92,c_231,c_244,c_455,c_496])).

tff(c_508,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_511,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_508])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_64,c_56,c_511])).

tff(c_516,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_518,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_521,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_518])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_64,c_56,c_202,c_521])).

tff(c_526,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_532,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_455])).

tff(c_517,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_52,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_tops_2(A_33,B_34,C_35) = k2_funct_1(C_35)
      | ~ v2_funct_1(C_35)
      | k2_relset_1(A_33,B_34,C_35) != B_34
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_562,plain,(
    ! [B_150,A_151,C_152] :
      ( k2_tops_2(B_150,A_151,k2_funct_1(C_152)) = k2_funct_1(k2_funct_1(C_152))
      | ~ v2_funct_1(k2_funct_1(C_152))
      | k2_relset_1(B_150,A_151,k2_funct_1(C_152)) != A_151
      | ~ v1_funct_2(k2_funct_1(C_152),B_150,A_151)
      | ~ v1_funct_1(k2_funct_1(C_152))
      | k2_relset_1(A_151,B_150,C_152) != B_150
      | ~ v2_funct_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150)))
      | ~ v1_funct_2(C_152,A_151,B_150)
      | ~ v1_funct_1(C_152) ) ),
    inference(resolution,[status(thm)],[c_308,c_52])).

tff(c_568,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_562])).

tff(c_572,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_56,c_92,c_231,c_244,c_532,c_517,c_568])).

tff(c_296,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_tops_2(A_99,B_100,C_101) = k2_funct_1(C_101)
      | ~ v2_funct_1(C_101)
      | k2_relset_1(A_99,B_100,C_101) != B_100
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_2(C_101,A_99,B_100)
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_299,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_296])).

tff(c_302,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86,c_92,c_56,c_299])).

tff(c_54,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_107,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_80,c_79,c_79,c_79,c_54])).

tff(c_303,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_107])).

tff(c_578,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_303])).

tff(c_585,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_578])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_64,c_56,c_224,c_585])).

tff(c_589,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_50,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(k2_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_603,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_50])).

tff(c_607,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2,c_603])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  
% 3.24/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.47  
% 3.24/1.47  %Foreground sorts:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Background operators:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Foreground operators:
% 3.24/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.24/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.24/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.24/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.47  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.24/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.47  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.24/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.24/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.24/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.24/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.24/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.24/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.47  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.24/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.47  
% 3.24/1.49  tff(f_173, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.24/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.49  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.24/1.49  tff(f_131, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.24/1.49  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.24/1.49  tff(f_111, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.24/1.49  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.24/1.49  tff(f_127, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.24/1.49  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.24/1.49  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.24/1.49  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.24/1.49  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 3.24/1.49  tff(f_47, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.24/1.49  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.24/1.49  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.24/1.49  tff(f_139, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.24/1.49  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_66, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.24/1.49  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.49  tff(c_70, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_72, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.49  tff(c_80, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_72])).
% 3.24/1.49  tff(c_79, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_72])).
% 3.24/1.49  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_60])).
% 3.24/1.49  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.49  tff(c_101, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_98, c_4])).
% 3.24/1.49  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_101])).
% 3.24/1.49  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_85, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_62])).
% 3.24/1.49  tff(c_86, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_85])).
% 3.24/1.49  tff(c_219, plain, (![A_81, B_82, D_83]: (r2_funct_2(A_81, B_82, D_83, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_2(D_83, A_81, B_82) | ~v1_funct_1(D_83))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.24/1.49  tff(c_221, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_219])).
% 3.24/1.49  tff(c_224, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_221])).
% 3.24/1.49  tff(c_16, plain, (![A_9]: (k2_funct_1(k2_funct_1(A_9))=A_9 | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.24/1.49  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_92, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_79, c_58])).
% 3.24/1.49  tff(c_225, plain, (![C_84, A_85, B_86]: (v1_funct_1(k2_funct_1(C_84)) | k2_relset_1(A_85, B_86, C_84)!=B_86 | ~v2_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.24/1.49  tff(c_228, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_225])).
% 3.24/1.49  tff(c_231, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_56, c_92, c_228])).
% 3.24/1.49  tff(c_238, plain, (![C_89, B_90, A_91]: (v1_funct_2(k2_funct_1(C_89), B_90, A_91) | k2_relset_1(A_91, B_90, C_89)!=B_90 | ~v2_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))) | ~v1_funct_2(C_89, A_91, B_90) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.24/1.49  tff(c_241, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_238])).
% 3.24/1.49  tff(c_244, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_56, c_92, c_241])).
% 3.24/1.49  tff(c_162, plain, (![A_60, B_61, C_62, D_63]: (k8_relset_1(A_60, B_61, C_62, D_63)=k10_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.24/1.49  tff(c_165, plain, (![D_63]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_63)=k10_relat_1('#skF_3', D_63))), inference(resolution, [status(thm)], [c_98, c_162])).
% 3.24/1.49  tff(c_177, plain, (![A_69, B_70, C_71]: (k8_relset_1(A_69, B_70, C_71, B_70)=k1_relset_1(A_69, B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.24/1.49  tff(c_179, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_98, c_177])).
% 3.24/1.49  tff(c_181, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k10_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_179])).
% 3.24/1.49  tff(c_195, plain, (![B_75, A_76, C_77]: (k1_xboole_0=B_75 | k1_relset_1(A_76, B_75, C_77)=A_76 | ~v1_funct_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.49  tff(c_198, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_98, c_195])).
% 3.24/1.49  tff(c_201, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_181, c_198])).
% 3.24/1.49  tff(c_202, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_201])).
% 3.24/1.49  tff(c_14, plain, (![B_8, A_7]: (k9_relat_1(k2_funct_1(B_8), A_7)=k10_relat_1(B_8, A_7) | ~v2_funct_1(B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.24/1.49  tff(c_8, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.24/1.49  tff(c_308, plain, (![C_102, B_103, A_104]: (m1_subset_1(k2_funct_1(C_102), k1_zfmisc_1(k2_zfmisc_1(B_103, A_104))) | k2_relset_1(A_104, B_103, C_102)!=B_103 | ~v2_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_2(C_102, A_104, B_103) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.24/1.49  tff(c_18, plain, (![A_10, B_11, C_12, D_13]: (k7_relset_1(A_10, B_11, C_12, D_13)=k9_relat_1(C_12, D_13) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.49  tff(c_386, plain, (![B_112, A_113, C_114, D_115]: (k7_relset_1(B_112, A_113, k2_funct_1(C_114), D_115)=k9_relat_1(k2_funct_1(C_114), D_115) | k2_relset_1(A_113, B_112, C_114)!=B_112 | ~v2_funct_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))) | ~v1_funct_2(C_114, A_113, B_112) | ~v1_funct_1(C_114))), inference(resolution, [status(thm)], [c_308, c_18])).
% 3.24/1.49  tff(c_390, plain, (![D_115]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_115)=k9_relat_1(k2_funct_1('#skF_3'), D_115) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_386])).
% 3.24/1.49  tff(c_394, plain, (![D_115]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_115)=k9_relat_1(k2_funct_1('#skF_3'), D_115))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_56, c_92, c_390])).
% 3.24/1.49  tff(c_24, plain, (![A_18, B_19, C_20]: (k7_relset_1(A_18, B_19, C_20, A_18)=k2_relset_1(A_18, B_19, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.24/1.49  tff(c_447, plain, (![B_129, A_130, C_131]: (k7_relset_1(B_129, A_130, k2_funct_1(C_131), B_129)=k2_relset_1(B_129, A_130, k2_funct_1(C_131)) | k2_relset_1(A_130, B_129, C_131)!=B_129 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(C_131, A_130, B_129) | ~v1_funct_1(C_131))), inference(resolution, [status(thm)], [c_308, c_24])).
% 3.24/1.49  tff(c_451, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))=k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_447])).
% 3.24/1.49  tff(c_455, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_56, c_92, c_394, c_451])).
% 3.24/1.49  tff(c_46, plain, (![C_30, A_28, B_29]: (v1_funct_1(k2_funct_1(C_30)) | k2_relset_1(A_28, B_29, C_30)!=B_29 | ~v2_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.24/1.49  tff(c_490, plain, (![C_141, B_142, A_143]: (v1_funct_1(k2_funct_1(k2_funct_1(C_141))) | k2_relset_1(B_142, A_143, k2_funct_1(C_141))!=A_143 | ~v2_funct_1(k2_funct_1(C_141)) | ~v1_funct_2(k2_funct_1(C_141), B_142, A_143) | ~v1_funct_1(k2_funct_1(C_141)) | k2_relset_1(A_143, B_142, C_141)!=B_142 | ~v2_funct_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))) | ~v1_funct_2(C_141, A_143, B_142) | ~v1_funct_1(C_141))), inference(resolution, [status(thm)], [c_308, c_46])).
% 3.24/1.49  tff(c_496, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_490])).
% 3.24/1.49  tff(c_500, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_56, c_92, c_231, c_244, c_455, c_496])).
% 3.24/1.49  tff(c_508, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_500])).
% 3.24/1.49  tff(c_511, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_508])).
% 3.24/1.49  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_64, c_56, c_511])).
% 3.24/1.49  tff(c_516, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_500])).
% 3.24/1.49  tff(c_518, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_516])).
% 3.24/1.49  tff(c_521, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_518])).
% 3.24/1.49  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_64, c_56, c_202, c_521])).
% 3.24/1.49  tff(c_526, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_516])).
% 3.24/1.49  tff(c_532, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_455])).
% 3.24/1.49  tff(c_517, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_500])).
% 3.24/1.49  tff(c_52, plain, (![A_33, B_34, C_35]: (k2_tops_2(A_33, B_34, C_35)=k2_funct_1(C_35) | ~v2_funct_1(C_35) | k2_relset_1(A_33, B_34, C_35)!=B_34 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.24/1.49  tff(c_562, plain, (![B_150, A_151, C_152]: (k2_tops_2(B_150, A_151, k2_funct_1(C_152))=k2_funct_1(k2_funct_1(C_152)) | ~v2_funct_1(k2_funct_1(C_152)) | k2_relset_1(B_150, A_151, k2_funct_1(C_152))!=A_151 | ~v1_funct_2(k2_funct_1(C_152), B_150, A_151) | ~v1_funct_1(k2_funct_1(C_152)) | k2_relset_1(A_151, B_150, C_152)!=B_150 | ~v2_funct_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))) | ~v1_funct_2(C_152, A_151, B_150) | ~v1_funct_1(C_152))), inference(resolution, [status(thm)], [c_308, c_52])).
% 3.24/1.49  tff(c_568, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_562])).
% 3.24/1.49  tff(c_572, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_56, c_92, c_231, c_244, c_532, c_517, c_568])).
% 3.24/1.49  tff(c_296, plain, (![A_99, B_100, C_101]: (k2_tops_2(A_99, B_100, C_101)=k2_funct_1(C_101) | ~v2_funct_1(C_101) | k2_relset_1(A_99, B_100, C_101)!=B_100 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_2(C_101, A_99, B_100) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.24/1.49  tff(c_299, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_296])).
% 3.24/1.49  tff(c_302, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86, c_92, c_56, c_299])).
% 3.24/1.49  tff(c_54, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.24/1.49  tff(c_107, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_80, c_79, c_79, c_79, c_54])).
% 3.24/1.49  tff(c_303, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_107])).
% 3.24/1.49  tff(c_578, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_303])).
% 3.24/1.49  tff(c_585, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_578])).
% 3.24/1.49  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_64, c_56, c_224, c_585])).
% 3.24/1.49  tff(c_589, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_201])).
% 3.24/1.49  tff(c_50, plain, (![A_32]: (~v1_xboole_0(k2_struct_0(A_32)) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.49  tff(c_603, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_589, c_50])).
% 3.24/1.49  tff(c_607, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2, c_603])).
% 3.24/1.49  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_607])).
% 3.24/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  Inference rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Ref     : 0
% 3.24/1.49  #Sup     : 124
% 3.24/1.49  #Fact    : 0
% 3.24/1.49  #Define  : 0
% 3.24/1.49  #Split   : 3
% 3.24/1.49  #Chain   : 0
% 3.24/1.49  #Close   : 0
% 3.24/1.49  
% 3.24/1.49  Ordering : KBO
% 3.24/1.49  
% 3.24/1.49  Simplification rules
% 3.24/1.49  ----------------------
% 3.39/1.49  #Subsume      : 9
% 3.39/1.49  #Demod        : 146
% 3.39/1.49  #Tautology    : 61
% 3.39/1.49  #SimpNegUnit  : 1
% 3.39/1.49  #BackRed      : 14
% 3.39/1.49  
% 3.39/1.49  #Partial instantiations: 0
% 3.39/1.49  #Strategies tried      : 1
% 3.39/1.49  
% 3.39/1.49  Timing (in seconds)
% 3.39/1.49  ----------------------
% 3.39/1.50  Preprocessing        : 0.35
% 3.39/1.50  Parsing              : 0.18
% 3.39/1.50  CNF conversion       : 0.02
% 3.39/1.50  Main loop            : 0.37
% 3.39/1.50  Inferencing          : 0.13
% 3.39/1.50  Reduction            : 0.12
% 3.39/1.50  Demodulation         : 0.08
% 3.39/1.50  BG Simplification    : 0.03
% 3.39/1.50  Subsumption          : 0.07
% 3.39/1.50  Abstraction          : 0.02
% 3.39/1.50  MUC search           : 0.00
% 3.39/1.50  Cooper               : 0.00
% 3.39/1.50  Total                : 0.76
% 3.39/1.50  Index Insertion      : 0.00
% 3.39/1.50  Index Deletion       : 0.00
% 3.39/1.50  Index Matching       : 0.00
% 3.39/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
