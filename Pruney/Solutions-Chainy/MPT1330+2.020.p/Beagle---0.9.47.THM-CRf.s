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
% DateTime   : Thu Dec  3 10:23:11 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 614 expanded)
%              Number of leaves         :   38 ( 226 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 (1593 expanded)
%              Number of equality atoms :   51 ( 621 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(c_34,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_47,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_47])).

tff(c_42,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_36])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v1_relat_1(B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_2))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_79,c_4])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_100,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_79,c_100])).

tff(c_106,plain,(
    ! [B_48,A_49] :
      ( k1_relat_1(B_48) = A_49
      | ~ v1_partfun1(B_48,A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_109,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_106])).

tff(c_112,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_109])).

tff(c_113,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_65,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_38])).

tff(c_155,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_partfun1(C_64,A_65)
      | ~ v1_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | v1_xboole_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_158,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_79,c_155])).

tff(c_161,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_158])).

tff(c_162,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_161])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_165])).

tff(c_170,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_174,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_79])).

tff(c_220,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k8_relset_1(A_70,B_71,C_72,D_73) = k10_relat_1(C_72,D_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_223,plain,(
    ! [D_73] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_73) = k10_relat_1('#skF_3',D_73) ),
    inference(resolution,[status(thm)],[c_174,c_220])).

tff(c_32,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_99,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_32])).

tff(c_173,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_99])).

tff(c_228,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_173])).

tff(c_215,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_219,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_215])).

tff(c_246,plain,(
    ! [A_78,B_79,C_80] :
      ( k8_relset_1(A_78,B_79,C_80,B_79) = k1_relset_1(A_78,B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_248,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_246])).

tff(c_250,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_219,c_248])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_250])).

tff(c_254,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_260,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_54])).

tff(c_253,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_255,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_55])).

tff(c_286,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_255,c_36])).

tff(c_322,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_326,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_322])).

tff(c_335,plain,(
    ! [A_102,B_103,C_104] :
      ( k8_relset_1(A_102,B_103,C_104,B_103) = k1_relset_1(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_337,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_335])).

tff(c_339,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_337])).

tff(c_313,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_255,c_254,c_253,c_32])).

tff(c_340,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_313])).

tff(c_287,plain,(
    ! [B_84,A_85] :
      ( v1_relat_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_290,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_286,c_287])).

tff(c_293,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_290])).

tff(c_8,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_297,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_293,c_8])).

tff(c_331,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k8_relset_1(A_98,B_99,C_100,D_101) = k10_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_345,plain,(
    ! [D_105] : k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',D_105) = k10_relat_1('#skF_3',D_105) ),
    inference(resolution,[status(thm)],[c_286,c_331])).

tff(c_351,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_339])).

tff(c_359,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_351])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:08:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.75  
% 3.08/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.75  
% 3.08/1.75  %Foreground sorts:
% 3.08/1.75  
% 3.08/1.75  
% 3.08/1.75  %Background operators:
% 3.08/1.75  
% 3.08/1.75  
% 3.08/1.75  %Foreground operators:
% 3.08/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.75  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.08/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.08/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.08/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.75  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.08/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.75  
% 3.18/1.78  tff(f_107, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.18/1.78  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.18/1.78  tff(f_88, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.18/1.78  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.18/1.78  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.18/1.78  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.18/1.78  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.18/1.78  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.18/1.78  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.18/1.78  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.18/1.78  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.18/1.78  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 3.18/1.78  tff(c_34, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.78  tff(c_64, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.18/1.78  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.78  tff(c_44, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.78  tff(c_47, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.18/1.78  tff(c_55, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_47])).
% 3.18/1.78  tff(c_42, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.78  tff(c_54, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_47])).
% 3.18/1.78  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.78  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_36])).
% 3.18/1.78  tff(c_4, plain, (![B_4, A_2]: (v1_relat_1(B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_2)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.18/1.78  tff(c_82, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_79, c_4])).
% 3.18/1.78  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_82])).
% 3.18/1.78  tff(c_100, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.18/1.78  tff(c_104, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_79, c_100])).
% 3.18/1.78  tff(c_106, plain, (![B_48, A_49]: (k1_relat_1(B_48)=A_49 | ~v1_partfun1(B_48, A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.18/1.78  tff(c_109, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_106])).
% 3.18/1.78  tff(c_112, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_109])).
% 3.18/1.78  tff(c_113, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_112])).
% 3.18/1.78  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.78  tff(c_38, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.78  tff(c_65, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_38])).
% 3.18/1.78  tff(c_155, plain, (![C_64, A_65, B_66]: (v1_partfun1(C_64, A_65) | ~v1_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | v1_xboole_0(B_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.78  tff(c_158, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_79, c_155])).
% 3.18/1.78  tff(c_161, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_158])).
% 3.18/1.78  tff(c_162, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_113, c_161])).
% 3.18/1.78  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.78  tff(c_165, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_162, c_2])).
% 3.18/1.78  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_165])).
% 3.18/1.78  tff(c_170, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_112])).
% 3.18/1.78  tff(c_174, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_79])).
% 3.18/1.78  tff(c_220, plain, (![A_70, B_71, C_72, D_73]: (k8_relset_1(A_70, B_71, C_72, D_73)=k10_relat_1(C_72, D_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.78  tff(c_223, plain, (![D_73]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_73)=k10_relat_1('#skF_3', D_73))), inference(resolution, [status(thm)], [c_174, c_220])).
% 3.18/1.78  tff(c_32, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.78  tff(c_99, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_32])).
% 3.18/1.78  tff(c_173, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_99])).
% 3.18/1.78  tff(c_228, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_173])).
% 3.18/1.78  tff(c_215, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.78  tff(c_219, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_174, c_215])).
% 3.18/1.78  tff(c_246, plain, (![A_78, B_79, C_80]: (k8_relset_1(A_78, B_79, C_80, B_79)=k1_relset_1(A_78, B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.78  tff(c_248, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_174, c_246])).
% 3.18/1.78  tff(c_250, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_219, c_248])).
% 3.18/1.78  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_250])).
% 3.18/1.78  tff(c_254, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.18/1.78  tff(c_260, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_254, c_54])).
% 3.18/1.78  tff(c_253, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.18/1.78  tff(c_255, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_253, c_55])).
% 3.18/1.78  tff(c_286, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_255, c_36])).
% 3.18/1.78  tff(c_322, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.78  tff(c_326, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_322])).
% 3.18/1.78  tff(c_335, plain, (![A_102, B_103, C_104]: (k8_relset_1(A_102, B_103, C_104, B_103)=k1_relset_1(A_102, B_103, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.78  tff(c_337, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_286, c_335])).
% 3.18/1.78  tff(c_339, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_337])).
% 3.18/1.78  tff(c_313, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_260, c_255, c_254, c_253, c_32])).
% 3.18/1.78  tff(c_340, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_339, c_313])).
% 3.18/1.78  tff(c_287, plain, (![B_84, A_85]: (v1_relat_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.18/1.78  tff(c_290, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_287])).
% 3.18/1.78  tff(c_293, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_290])).
% 3.18/1.78  tff(c_8, plain, (![A_7]: (k10_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.18/1.78  tff(c_297, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_293, c_8])).
% 3.18/1.78  tff(c_331, plain, (![A_98, B_99, C_100, D_101]: (k8_relset_1(A_98, B_99, C_100, D_101)=k10_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.78  tff(c_345, plain, (![D_105]: (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', D_105)=k10_relat_1('#skF_3', D_105))), inference(resolution, [status(thm)], [c_286, c_331])).
% 3.18/1.78  tff(c_351, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_345, c_339])).
% 3.18/1.78  tff(c_359, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_297, c_351])).
% 3.18/1.78  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_340, c_359])).
% 3.18/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.78  
% 3.18/1.78  Inference rules
% 3.18/1.78  ----------------------
% 3.18/1.78  #Ref     : 0
% 3.18/1.78  #Sup     : 78
% 3.18/1.78  #Fact    : 0
% 3.18/1.78  #Define  : 0
% 3.18/1.78  #Split   : 3
% 3.18/1.78  #Chain   : 0
% 3.18/1.78  #Close   : 0
% 3.18/1.78  
% 3.18/1.78  Ordering : KBO
% 3.18/1.79  
% 3.18/1.79  Simplification rules
% 3.18/1.79  ----------------------
% 3.18/1.79  #Subsume      : 0
% 3.18/1.79  #Demod        : 47
% 3.18/1.79  #Tautology    : 49
% 3.18/1.79  #SimpNegUnit  : 4
% 3.18/1.79  #BackRed      : 11
% 3.18/1.79  
% 3.18/1.79  #Partial instantiations: 0
% 3.18/1.79  #Strategies tried      : 1
% 3.18/1.79  
% 3.18/1.79  Timing (in seconds)
% 3.18/1.79  ----------------------
% 3.18/1.79  Preprocessing        : 0.51
% 3.18/1.79  Parsing              : 0.26
% 3.18/1.79  CNF conversion       : 0.04
% 3.18/1.79  Main loop            : 0.38
% 3.18/1.79  Inferencing          : 0.14
% 3.18/1.79  Reduction            : 0.13
% 3.18/1.79  Demodulation         : 0.09
% 3.18/1.79  BG Simplification    : 0.02
% 3.18/1.79  Subsumption          : 0.04
% 3.18/1.79  Abstraction          : 0.02
% 3.18/1.79  MUC search           : 0.00
% 3.18/1.79  Cooper               : 0.00
% 3.18/1.79  Total                : 0.96
% 3.18/1.79  Index Insertion      : 0.00
% 3.18/1.79  Index Deletion       : 0.00
% 3.18/1.79  Index Matching       : 0.00
% 3.18/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
