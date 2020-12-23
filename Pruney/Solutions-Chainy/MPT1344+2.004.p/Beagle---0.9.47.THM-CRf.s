%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:48 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 405 expanded)
%              Number of leaves         :   35 ( 166 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 (1255 expanded)
%              Number of equality atoms :   34 ( 353 expanded)
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

tff(f_120,negated_conjecture,(
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

tff(f_74,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_48])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_55,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_48])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_73,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_38])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_79,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_40])).

tff(c_34,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_80,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_34])).

tff(c_198,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_tops_2(A_69,B_70,C_71) = k2_funct_1(C_71)
      | ~ v2_funct_1(C_71)
      | k2_relset_1(A_69,B_70,C_71) != B_70
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_71,A_69,B_70)
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_204,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_198])).

tff(c_208,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_80,c_32,c_204])).

tff(c_154,plain,(
    ! [A_57,B_58,C_59] :
      ( v1_funct_1(k2_tops_2(A_57,B_58,C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_157,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_154])).

tff(c_160,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_157])).

tff(c_211,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_160])).

tff(c_167,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k2_tops_2(A_63,B_64,C_65),k1_zfmisc_1(k2_zfmisc_1(B_64,A_63)))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_funct_2(C_65,A_63,B_64)
      | ~ v1_funct_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_179,plain,(
    ! [A_63,B_64,C_65] :
      ( v1_relat_1(k2_tops_2(A_63,B_64,C_65))
      | ~ v1_relat_1(k2_zfmisc_1(B_64,A_63))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_funct_2(C_65,A_63,B_64)
      | ~ v1_funct_1(C_65) ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_187,plain,(
    ! [A_66,B_67,C_68] :
      ( v1_relat_1(k2_tops_2(A_66,B_67,C_68))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_68,A_66,B_67)
      | ~ v1_funct_1(C_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_193,plain,
    ( v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_187])).

tff(c_197,plain,(
    v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_193])).

tff(c_209,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_197])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_9] :
      ( k2_funct_1(k2_funct_1(A_9)) = A_9
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,(
    ! [B_45,A_46] :
      ( k10_relat_1(k2_funct_1(B_45),A_46) = k9_relat_1(B_45,A_46)
      | ~ v2_funct_1(B_45)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_257,plain,(
    ! [A_72,A_73] :
      ( k9_relat_1(k2_funct_1(A_72),A_73) = k10_relat_1(A_72,A_73)
      | ~ v2_funct_1(k2_funct_1(A_72))
      | ~ v1_funct_1(k2_funct_1(A_72))
      | ~ v1_relat_1(k2_funct_1(A_72))
      | ~ v2_funct_1(A_72)
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_115])).

tff(c_283,plain,(
    ! [A_76,A_77] :
      ( k9_relat_1(k2_funct_1(A_76),A_77) = k10_relat_1(A_76,A_77)
      | ~ v1_funct_1(k2_funct_1(A_76))
      | ~ v1_relat_1(k2_funct_1(A_76))
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_285,plain,(
    ! [A_77] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_77) = k10_relat_1('#skF_3',A_77)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_209,c_283])).

tff(c_292,plain,(
    ! [A_77] : k9_relat_1(k2_funct_1('#skF_3'),A_77) = k10_relat_1('#skF_3',A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42,c_32,c_211,c_285])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k2_tops_2(A_22,B_23,C_24),k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_216,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_24])).

tff(c_220,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_73,c_216])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k7_relset_1(A_10,B_11,C_12,D_13) = k9_relat_1(C_12,D_13)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_253,plain,(
    ! [D_13] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_13) = k9_relat_1(k2_funct_1('#skF_3'),D_13) ),
    inference(resolution,[status(thm)],[c_220,c_16])).

tff(c_140,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k8_relset_1(A_52,B_53,C_54,D_55) = k10_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_143,plain,(
    ! [D_55] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_55) = k10_relat_1('#skF_3',D_55) ),
    inference(resolution,[status(thm)],[c_73,c_140])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_87,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_56,c_55,c_55,c_55,c_30])).

tff(c_144,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_87])).

tff(c_212,plain,(
    k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_144])).

tff(c_272,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_4') != k10_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_212])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.65/1.40  
% 2.65/1.40  %Foreground sorts:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Background operators:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Foreground operators:
% 2.65/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.65/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.65/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.40  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.65/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.65/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.65/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.65/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.40  
% 2.65/1.42  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.65/1.42  tff(f_120, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k7_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_2)).
% 2.65/1.42  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.65/1.42  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.65/1.42  tff(f_86, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 2.65/1.42  tff(f_98, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 2.65/1.42  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 2.65/1.42  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 2.65/1.42  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 2.65/1.42  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.65/1.42  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.65/1.42  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.65/1.42  tff(c_46, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_48, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.65/1.42  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_48])).
% 2.65/1.42  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_55, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_48])).
% 2.65/1.42  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_73, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_38])).
% 2.65/1.42  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.42  tff(c_76, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.65/1.42  tff(c_79, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_76])).
% 2.65/1.42  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_66, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_40])).
% 2.65/1.42  tff(c_34, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_80, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_34])).
% 2.65/1.42  tff(c_198, plain, (![A_69, B_70, C_71]: (k2_tops_2(A_69, B_70, C_71)=k2_funct_1(C_71) | ~v2_funct_1(C_71) | k2_relset_1(A_69, B_70, C_71)!=B_70 | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_71, A_69, B_70) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.42  tff(c_204, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_73, c_198])).
% 2.65/1.42  tff(c_208, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_80, c_32, c_204])).
% 2.65/1.42  tff(c_154, plain, (![A_57, B_58, C_59]: (v1_funct_1(k2_tops_2(A_57, B_58, C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.65/1.42  tff(c_157, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_73, c_154])).
% 2.65/1.42  tff(c_160, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_157])).
% 2.65/1.42  tff(c_211, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_160])).
% 2.65/1.42  tff(c_167, plain, (![A_63, B_64, C_65]: (m1_subset_1(k2_tops_2(A_63, B_64, C_65), k1_zfmisc_1(k2_zfmisc_1(B_64, A_63))) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~v1_funct_2(C_65, A_63, B_64) | ~v1_funct_1(C_65))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.65/1.42  tff(c_179, plain, (![A_63, B_64, C_65]: (v1_relat_1(k2_tops_2(A_63, B_64, C_65)) | ~v1_relat_1(k2_zfmisc_1(B_64, A_63)) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~v1_funct_2(C_65, A_63, B_64) | ~v1_funct_1(C_65))), inference(resolution, [status(thm)], [c_167, c_2])).
% 2.65/1.42  tff(c_187, plain, (![A_66, B_67, C_68]: (v1_relat_1(k2_tops_2(A_66, B_67, C_68)) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_68, A_66, B_67) | ~v1_funct_1(C_68))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_179])).
% 2.65/1.42  tff(c_193, plain, (v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_73, c_187])).
% 2.65/1.42  tff(c_197, plain, (v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_193])).
% 2.65/1.42  tff(c_209, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_197])).
% 2.65/1.42  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.42  tff(c_14, plain, (![A_9]: (k2_funct_1(k2_funct_1(A_9))=A_9 | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.65/1.42  tff(c_115, plain, (![B_45, A_46]: (k10_relat_1(k2_funct_1(B_45), A_46)=k9_relat_1(B_45, A_46) | ~v2_funct_1(B_45) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.65/1.42  tff(c_257, plain, (![A_72, A_73]: (k9_relat_1(k2_funct_1(A_72), A_73)=k10_relat_1(A_72, A_73) | ~v2_funct_1(k2_funct_1(A_72)) | ~v1_funct_1(k2_funct_1(A_72)) | ~v1_relat_1(k2_funct_1(A_72)) | ~v2_funct_1(A_72) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_14, c_115])).
% 2.65/1.42  tff(c_283, plain, (![A_76, A_77]: (k9_relat_1(k2_funct_1(A_76), A_77)=k10_relat_1(A_76, A_77) | ~v1_funct_1(k2_funct_1(A_76)) | ~v1_relat_1(k2_funct_1(A_76)) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(resolution, [status(thm)], [c_6, c_257])).
% 2.65/1.42  tff(c_285, plain, (![A_77]: (k9_relat_1(k2_funct_1('#skF_3'), A_77)=k10_relat_1('#skF_3', A_77) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_209, c_283])).
% 2.65/1.42  tff(c_292, plain, (![A_77]: (k9_relat_1(k2_funct_1('#skF_3'), A_77)=k10_relat_1('#skF_3', A_77))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42, c_32, c_211, c_285])).
% 2.65/1.42  tff(c_24, plain, (![A_22, B_23, C_24]: (m1_subset_1(k2_tops_2(A_22, B_23, C_24), k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.65/1.42  tff(c_216, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_208, c_24])).
% 2.65/1.42  tff(c_220, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_73, c_216])).
% 2.65/1.42  tff(c_16, plain, (![A_10, B_11, C_12, D_13]: (k7_relset_1(A_10, B_11, C_12, D_13)=k9_relat_1(C_12, D_13) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.65/1.42  tff(c_253, plain, (![D_13]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_13)=k9_relat_1(k2_funct_1('#skF_3'), D_13))), inference(resolution, [status(thm)], [c_220, c_16])).
% 2.65/1.42  tff(c_140, plain, (![A_52, B_53, C_54, D_55]: (k8_relset_1(A_52, B_53, C_54, D_55)=k10_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.65/1.42  tff(c_143, plain, (![D_55]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_55)=k10_relat_1('#skF_3', D_55))), inference(resolution, [status(thm)], [c_73, c_140])).
% 2.65/1.42  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.65/1.42  tff(c_87, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_56, c_55, c_55, c_55, c_30])).
% 2.65/1.42  tff(c_144, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_87])).
% 2.65/1.42  tff(c_212, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_144])).
% 2.65/1.42  tff(c_272, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_4')!=k10_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_212])).
% 2.65/1.42  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_292, c_272])).
% 2.65/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.42  
% 2.65/1.42  Inference rules
% 2.65/1.42  ----------------------
% 2.65/1.42  #Ref     : 0
% 2.65/1.42  #Sup     : 56
% 2.65/1.42  #Fact    : 0
% 2.65/1.42  #Define  : 0
% 2.65/1.42  #Split   : 2
% 2.65/1.42  #Chain   : 0
% 2.65/1.42  #Close   : 0
% 2.65/1.42  
% 2.65/1.42  Ordering : KBO
% 2.65/1.42  
% 2.65/1.42  Simplification rules
% 2.65/1.42  ----------------------
% 2.65/1.42  #Subsume      : 1
% 2.65/1.42  #Demod        : 50
% 2.65/1.42  #Tautology    : 26
% 2.65/1.42  #SimpNegUnit  : 0
% 2.65/1.42  #BackRed      : 9
% 2.65/1.42  
% 2.65/1.42  #Partial instantiations: 0
% 2.65/1.42  #Strategies tried      : 1
% 2.65/1.42  
% 2.65/1.42  Timing (in seconds)
% 2.65/1.42  ----------------------
% 2.65/1.42  Preprocessing        : 0.35
% 2.65/1.42  Parsing              : 0.19
% 2.65/1.42  CNF conversion       : 0.03
% 2.65/1.43  Main loop            : 0.25
% 2.65/1.43  Inferencing          : 0.09
% 2.65/1.43  Reduction            : 0.08
% 2.65/1.43  Demodulation         : 0.06
% 2.65/1.43  BG Simplification    : 0.02
% 2.65/1.43  Subsumption          : 0.04
% 2.65/1.43  Abstraction          : 0.02
% 2.65/1.43  MUC search           : 0.00
% 2.65/1.43  Cooper               : 0.00
% 2.65/1.43  Total                : 0.64
% 2.65/1.43  Index Insertion      : 0.00
% 2.65/1.43  Index Deletion       : 0.00
% 2.65/1.43  Index Matching       : 0.00
% 2.65/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
