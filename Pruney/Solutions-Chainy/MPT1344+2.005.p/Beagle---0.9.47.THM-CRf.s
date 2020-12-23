%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:48 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 868 expanded)
%              Number of leaves         :   36 ( 341 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 (2864 expanded)
%              Number of equality atoms :   48 ( 802 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                        & v2_funct_1(C) )
                     => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k7_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_2)).

tff(f_78,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_120,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_50])).

tff(c_46,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_57,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_40])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_83])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_42])).

tff(c_36,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_75,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57,c_36])).

tff(c_213,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_tops_2(A_83,B_84,C_85) = k2_funct_1(C_85)
      | ~ v2_funct_1(C_85)
      | k2_relset_1(A_83,B_84,C_85) != B_84
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_219,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_213])).

tff(c_223,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_75,c_34,c_219])).

tff(c_157,plain,(
    ! [A_69,B_70,C_71] :
      ( m1_subset_1(k2_tops_2(A_69,B_70,C_71),k1_zfmisc_1(k2_zfmisc_1(B_70,A_69)))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_71,A_69,B_70)
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_169,plain,(
    ! [A_69,B_70,C_71] :
      ( v1_relat_1(k2_tops_2(A_69,B_70,C_71))
      | ~ v1_relat_1(k2_zfmisc_1(B_70,A_69))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_71,A_69,B_70)
      | ~ v1_funct_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_177,plain,(
    ! [A_72,B_73,C_74] :
      ( v1_relat_1(k2_tops_2(A_72,B_73,C_74))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(C_74,A_72,B_73)
      | ~ v1_funct_1(C_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_169])).

tff(c_183,plain,
    ( v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_177])).

tff(c_187,plain,(
    v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_183])).

tff(c_224,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_187])).

tff(c_188,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_funct_1(k2_funct_1(C_75))
      | k2_relset_1(A_76,B_77,C_75) != B_77
      | ~ v2_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_2(C_75,A_76,B_77)
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_194,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_188])).

tff(c_198,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_34,c_75,c_194])).

tff(c_202,plain,(
    ! [C_80,B_81,A_82] :
      ( v1_funct_2(k2_funct_1(C_80),B_81,A_82)
      | k2_relset_1(A_82,B_81,C_80) != B_81
      | ~ v2_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81)))
      | ~ v1_funct_2(C_80,A_82,B_81)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_208,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_202])).

tff(c_212,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_34,c_75,c_208])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1(k2_tops_2(A_24,B_25,C_26),k1_zfmisc_1(k2_zfmisc_1(B_25,A_24)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_233,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_24])).

tff(c_237,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_80,c_233])).

tff(c_18,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_funct_1(k2_funct_1(C_19))
      | k2_relset_1(A_17,B_18,C_19) != B_18
      | ~ v2_funct_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_247,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_237,c_18])).

tff(c_271,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_212,c_247])).

tff(c_344,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_383,plain,(
    ! [A_98,B_99,C_100] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_98),u1_struct_0(B_99),C_100))
      | ~ v2_funct_1(C_100)
      | k2_relset_1(u1_struct_0(A_98),u1_struct_0(B_99),C_100) != k2_struct_0(B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),u1_struct_0(B_99))))
      | ~ v1_funct_2(C_100,u1_struct_0(A_98),u1_struct_0(B_99))
      | ~ v1_funct_1(C_100)
      | ~ l1_struct_0(B_99)
      | ~ l1_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_394,plain,(
    ! [B_99,C_100] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_99),C_100))
      | ~ v2_funct_1(C_100)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_99),C_100) != k2_struct_0(B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_99))))
      | ~ v1_funct_2(C_100,u1_struct_0('#skF_1'),u1_struct_0(B_99))
      | ~ v1_funct_1(C_100)
      | ~ l1_struct_0(B_99)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_383])).

tff(c_669,plain,(
    ! [B_145,C_146] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_145),C_146))
      | ~ v2_funct_1(C_146)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_145),C_146) != k2_struct_0(B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_145))))
      | ~ v1_funct_2(C_146,k2_struct_0('#skF_1'),u1_struct_0(B_145))
      | ~ v1_funct_1(C_146)
      | ~ l1_struct_0(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58,c_58,c_58,c_394])).

tff(c_683,plain,(
    ! [C_146] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_146))
      | ~ v2_funct_1(C_146)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_146) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_146,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_146)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_669])).

tff(c_690,plain,(
    ! [C_147] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_147))
      | ~ v2_funct_1(C_147)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_147) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_147,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_57,c_57,c_57,c_683])).

tff(c_701,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_690])).

tff(c_706,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_75,c_34,c_223,c_701])).

tff(c_708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_706])).

tff(c_710,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_8,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,(
    ! [B_51,A_52] :
      ( k10_relat_1(k2_funct_1(B_51),A_52) = k9_relat_1(B_51,A_52)
      | ~ v2_funct_1(B_51)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_113,plain,(
    ! [A_8,A_52] :
      ( k9_relat_1(k2_funct_1(A_8),A_52) = k10_relat_1(A_8,A_52)
      | ~ v2_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(k2_funct_1(A_8))
      | ~ v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_104])).

tff(c_712,plain,(
    ! [A_52] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_52) = k10_relat_1('#skF_3',A_52)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_710,c_113])).

tff(c_715,plain,(
    ! [A_52] : k9_relat_1(k2_funct_1('#skF_3'),A_52) = k10_relat_1('#skF_3',A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_44,c_34,c_224,c_198,c_712])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k7_relset_1(A_9,B_10,C_11,D_12) = k9_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_282,plain,(
    ! [D_12] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_12) = k9_relat_1(k2_funct_1('#skF_3'),D_12) ),
    inference(resolution,[status(thm)],[c_237,c_10])).

tff(c_130,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k8_relset_1(A_58,B_59,C_60,D_61) = k10_relat_1(C_60,D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_133,plain,(
    ! [D_61] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_61) = k10_relat_1('#skF_3',D_61) ),
    inference(resolution,[status(thm)],[c_80,c_130])).

tff(c_32,plain,(
    k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_116,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_57,c_57,c_57,c_32])).

tff(c_134,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_116])).

tff(c_227,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_134])).

tff(c_286,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_227])).

tff(c_722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.51  
% 3.29/1.51  %Foreground sorts:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Background operators:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Foreground operators:
% 3.29/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.29/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.29/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.29/1.51  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.29/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.29/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.29/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.29/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.29/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.51  
% 3.29/1.53  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.29/1.53  tff(f_142, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k7_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_2)).
% 3.29/1.53  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.29/1.53  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.29/1.53  tff(f_90, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.29/1.53  tff(f_102, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.29/1.53  tff(f_74, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.29/1.53  tff(f_120, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 3.29/1.53  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.29/1.53  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 3.29/1.53  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.29/1.53  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.29/1.53  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.29/1.53  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_50, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.29/1.53  tff(c_58, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_50])).
% 3.29/1.53  tff(c_46, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_57, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_50])).
% 3.29/1.53  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_40])).
% 3.29/1.53  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_83, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_80, c_2])).
% 3.29/1.53  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_83])).
% 3.29/1.53  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_42, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_68, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_42])).
% 3.29/1.53  tff(c_36, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_75, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57, c_36])).
% 3.29/1.53  tff(c_213, plain, (![A_83, B_84, C_85]: (k2_tops_2(A_83, B_84, C_85)=k2_funct_1(C_85) | ~v2_funct_1(C_85) | k2_relset_1(A_83, B_84, C_85)!=B_84 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.53  tff(c_219, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_213])).
% 3.29/1.53  tff(c_223, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_75, c_34, c_219])).
% 3.29/1.53  tff(c_157, plain, (![A_69, B_70, C_71]: (m1_subset_1(k2_tops_2(A_69, B_70, C_71), k1_zfmisc_1(k2_zfmisc_1(B_70, A_69))) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_71, A_69, B_70) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.53  tff(c_169, plain, (![A_69, B_70, C_71]: (v1_relat_1(k2_tops_2(A_69, B_70, C_71)) | ~v1_relat_1(k2_zfmisc_1(B_70, A_69)) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_71, A_69, B_70) | ~v1_funct_1(C_71))), inference(resolution, [status(thm)], [c_157, c_2])).
% 3.29/1.53  tff(c_177, plain, (![A_72, B_73, C_74]: (v1_relat_1(k2_tops_2(A_72, B_73, C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(C_74, A_72, B_73) | ~v1_funct_1(C_74))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_169])).
% 3.29/1.53  tff(c_183, plain, (v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_177])).
% 3.29/1.53  tff(c_187, plain, (v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_183])).
% 3.29/1.53  tff(c_224, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_187])).
% 3.29/1.53  tff(c_188, plain, (![C_75, A_76, B_77]: (v1_funct_1(k2_funct_1(C_75)) | k2_relset_1(A_76, B_77, C_75)!=B_77 | ~v2_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_2(C_75, A_76, B_77) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.29/1.53  tff(c_194, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_188])).
% 3.29/1.53  tff(c_198, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_34, c_75, c_194])).
% 3.29/1.53  tff(c_202, plain, (![C_80, B_81, A_82]: (v1_funct_2(k2_funct_1(C_80), B_81, A_82) | k2_relset_1(A_82, B_81, C_80)!=B_81 | ~v2_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))) | ~v1_funct_2(C_80, A_82, B_81) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.29/1.53  tff(c_208, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_202])).
% 3.29/1.53  tff(c_212, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_34, c_75, c_208])).
% 3.29/1.53  tff(c_24, plain, (![A_24, B_25, C_26]: (m1_subset_1(k2_tops_2(A_24, B_25, C_26), k1_zfmisc_1(k2_zfmisc_1(B_25, A_24))) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.53  tff(c_233, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_223, c_24])).
% 3.29/1.53  tff(c_237, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_80, c_233])).
% 3.29/1.53  tff(c_18, plain, (![C_19, A_17, B_18]: (v1_funct_1(k2_funct_1(C_19)) | k2_relset_1(A_17, B_18, C_19)!=B_18 | ~v2_funct_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.29/1.53  tff(c_247, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_237, c_18])).
% 3.29/1.53  tff(c_271, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_212, c_247])).
% 3.29/1.53  tff(c_344, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_271])).
% 3.29/1.53  tff(c_383, plain, (![A_98, B_99, C_100]: (v2_funct_1(k2_tops_2(u1_struct_0(A_98), u1_struct_0(B_99), C_100)) | ~v2_funct_1(C_100) | k2_relset_1(u1_struct_0(A_98), u1_struct_0(B_99), C_100)!=k2_struct_0(B_99) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98), u1_struct_0(B_99)))) | ~v1_funct_2(C_100, u1_struct_0(A_98), u1_struct_0(B_99)) | ~v1_funct_1(C_100) | ~l1_struct_0(B_99) | ~l1_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.29/1.53  tff(c_394, plain, (![B_99, C_100]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_99), C_100)) | ~v2_funct_1(C_100) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_99), C_100)!=k2_struct_0(B_99) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_99)))) | ~v1_funct_2(C_100, u1_struct_0('#skF_1'), u1_struct_0(B_99)) | ~v1_funct_1(C_100) | ~l1_struct_0(B_99) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_383])).
% 3.29/1.53  tff(c_669, plain, (![B_145, C_146]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_145), C_146)) | ~v2_funct_1(C_146) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_145), C_146)!=k2_struct_0(B_145) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_145)))) | ~v1_funct_2(C_146, k2_struct_0('#skF_1'), u1_struct_0(B_145)) | ~v1_funct_1(C_146) | ~l1_struct_0(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58, c_58, c_58, c_394])).
% 3.29/1.53  tff(c_683, plain, (![C_146]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_146)) | ~v2_funct_1(C_146) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_146)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_146, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_146) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_669])).
% 3.29/1.53  tff(c_690, plain, (![C_147]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_147)) | ~v2_funct_1(C_147) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_147)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_147, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_147))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_57, c_57, c_57, c_683])).
% 3.29/1.53  tff(c_701, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_690])).
% 3.29/1.53  tff(c_706, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_75, c_34, c_223, c_701])).
% 3.29/1.53  tff(c_708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_706])).
% 3.29/1.53  tff(c_710, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_271])).
% 3.29/1.53  tff(c_8, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.29/1.53  tff(c_104, plain, (![B_51, A_52]: (k10_relat_1(k2_funct_1(B_51), A_52)=k9_relat_1(B_51, A_52) | ~v2_funct_1(B_51) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.29/1.53  tff(c_113, plain, (![A_8, A_52]: (k9_relat_1(k2_funct_1(A_8), A_52)=k10_relat_1(A_8, A_52) | ~v2_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(k2_funct_1(A_8)) | ~v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_104])).
% 3.29/1.53  tff(c_712, plain, (![A_52]: (k9_relat_1(k2_funct_1('#skF_3'), A_52)=k10_relat_1('#skF_3', A_52) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_710, c_113])).
% 3.29/1.53  tff(c_715, plain, (![A_52]: (k9_relat_1(k2_funct_1('#skF_3'), A_52)=k10_relat_1('#skF_3', A_52))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_44, c_34, c_224, c_198, c_712])).
% 3.29/1.53  tff(c_10, plain, (![A_9, B_10, C_11, D_12]: (k7_relset_1(A_9, B_10, C_11, D_12)=k9_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.29/1.53  tff(c_282, plain, (![D_12]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_12)=k9_relat_1(k2_funct_1('#skF_3'), D_12))), inference(resolution, [status(thm)], [c_237, c_10])).
% 3.29/1.53  tff(c_130, plain, (![A_58, B_59, C_60, D_61]: (k8_relset_1(A_58, B_59, C_60, D_61)=k10_relat_1(C_60, D_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/1.53  tff(c_133, plain, (![D_61]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_61)=k10_relat_1('#skF_3', D_61))), inference(resolution, [status(thm)], [c_80, c_130])).
% 3.29/1.53  tff(c_32, plain, (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.53  tff(c_116, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_57, c_57, c_57, c_32])).
% 3.29/1.53  tff(c_134, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_116])).
% 3.29/1.53  tff(c_227, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_134])).
% 3.29/1.53  tff(c_286, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_227])).
% 3.29/1.53  tff(c_722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_715, c_286])).
% 3.29/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  Inference rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Ref     : 0
% 3.29/1.53  #Sup     : 141
% 3.29/1.53  #Fact    : 0
% 3.29/1.53  #Define  : 0
% 3.29/1.53  #Split   : 3
% 3.29/1.53  #Chain   : 0
% 3.29/1.53  #Close   : 0
% 3.29/1.53  
% 3.29/1.53  Ordering : KBO
% 3.29/1.53  
% 3.29/1.53  Simplification rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Subsume      : 11
% 3.29/1.53  #Demod        : 205
% 3.29/1.53  #Tautology    : 40
% 3.29/1.53  #SimpNegUnit  : 1
% 3.29/1.53  #BackRed      : 9
% 3.29/1.53  
% 3.29/1.53  #Partial instantiations: 0
% 3.29/1.53  #Strategies tried      : 1
% 3.29/1.53  
% 3.29/1.53  Timing (in seconds)
% 3.29/1.53  ----------------------
% 3.29/1.54  Preprocessing        : 0.34
% 3.29/1.54  Parsing              : 0.18
% 3.29/1.54  CNF conversion       : 0.02
% 3.29/1.54  Main loop            : 0.40
% 3.29/1.54  Inferencing          : 0.14
% 3.29/1.54  Reduction            : 0.13
% 3.29/1.54  Demodulation         : 0.10
% 3.29/1.54  BG Simplification    : 0.03
% 3.29/1.54  Subsumption          : 0.07
% 3.29/1.54  Abstraction          : 0.02
% 3.29/1.54  MUC search           : 0.00
% 3.29/1.54  Cooper               : 0.00
% 3.29/1.54  Total                : 0.78
% 3.29/1.54  Index Insertion      : 0.00
% 3.29/1.54  Index Deletion       : 0.00
% 3.29/1.54  Index Matching       : 0.00
% 3.29/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
