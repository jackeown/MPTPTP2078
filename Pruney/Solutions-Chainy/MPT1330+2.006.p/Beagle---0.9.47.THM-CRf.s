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
% DateTime   : Thu Dec  3 10:23:09 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 999 expanded)
%              Number of leaves         :   42 ( 359 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 (2335 expanded)
%              Number of equality atoms :   66 ( 950 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > np__0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(np__0,type,(
    np__0: $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_128,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_109,axiom,(
    v1_xboole_0(np__0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc0_boole)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_106,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_114,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_106])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_113,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_106])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_129,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_113,c_48])).

tff(c_224,plain,(
    ! [C_67,B_68,A_69] :
      ( v1_xboole_0(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(B_68,A_69)))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_238,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_129,c_224])).

tff(c_243,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_130,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_130])).

tff(c_168,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_182,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_129,c_168])).

tff(c_290,plain,(
    ! [B_78,A_79] :
      ( k1_relat_1(B_78) = A_79
      | ~ v1_partfun1(B_78,A_79)
      | ~ v4_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_299,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_290])).

tff(c_308,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_299])).

tff(c_409,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_119,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_50])).

tff(c_120,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_119])).

tff(c_595,plain,(
    ! [C_117,A_118,B_119] :
      ( v1_partfun1(C_117,A_118)
      | ~ v1_funct_2(C_117,A_118,B_119)
      | ~ v1_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | v1_xboole_0(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_601,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_129,c_595])).

tff(c_614,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_120,c_601])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_409,c_614])).

tff(c_617,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_44,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_184,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_113,c_44])).

tff(c_621,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_617,c_184])).

tff(c_322,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_336,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_322])).

tff(c_619,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_336])).

tff(c_622,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_129])).

tff(c_675,plain,(
    ! [A_120,B_121,C_122] :
      ( k8_relset_1(A_120,B_121,C_122,B_121) = k1_relset_1(A_120,B_121,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_677,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_622,c_675])).

tff(c_688,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_677])).

tff(c_762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_688])).

tff(c_763,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_779,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_763,c_2])).

tff(c_46,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_83,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_788,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_83])).

tff(c_764,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_859,plain,(
    ! [A_143] :
      ( A_143 = '#skF_3'
      | ~ v1_xboole_0(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_2])).

tff(c_862,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_764,c_859])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_862])).

tff(c_871,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_906,plain,(
    ! [A_148] :
      ( u1_struct_0(A_148) = k2_struct_0(A_148)
      | ~ l1_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_909,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_906])).

tff(c_914,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_909])).

tff(c_941,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_914,c_48])).

tff(c_42,plain,(
    v1_xboole_0(np__0) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    np__0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_68])).

tff(c_73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_42])).

tff(c_1010,plain,(
    ! [C_169,B_170,A_171] :
      ( v1_xboole_0(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(B_170,A_171)))
      | ~ v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1016,plain,(
    ! [C_169] :
      ( v1_xboole_0(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1010])).

tff(c_1041,plain,(
    ! [C_176] :
      ( v1_xboole_0(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1016])).

tff(c_1049,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_941,c_1041])).

tff(c_1058,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1049,c_2])).

tff(c_1073,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1058,c_8])).

tff(c_12,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_1163,plain,(
    ! [A_182,B_183,C_184] :
      ( k1_relset_1(A_182,B_183,C_184) = k1_relat_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1171,plain,(
    ! [A_182,B_183] : k1_relset_1(A_182,B_183,k2_zfmisc_1(A_182,B_183)) = k1_relat_1(k2_zfmisc_1(A_182,B_183)) ),
    inference(resolution,[status(thm)],[c_57,c_1163])).

tff(c_1214,plain,(
    ! [A_186,B_187,C_188] :
      ( k8_relset_1(A_186,B_187,C_188,B_187) = k1_relset_1(A_186,B_187,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1222,plain,(
    ! [A_186,B_187] : k8_relset_1(A_186,B_187,k2_zfmisc_1(A_186,B_187),B_187) = k1_relset_1(A_186,B_187,k2_zfmisc_1(A_186,B_187)) ),
    inference(resolution,[status(thm)],[c_57,c_1214])).

tff(c_1547,plain,(
    ! [A_239,B_240] : k8_relset_1(A_239,B_240,k2_zfmisc_1(A_239,B_240),B_240) = k1_relat_1(k2_zfmisc_1(A_239,B_240)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_1222])).

tff(c_1559,plain,(
    ! [A_4] : k1_relat_1(k2_zfmisc_1(A_4,'#skF_3')) = k8_relset_1(A_4,'#skF_3','#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_1547])).

tff(c_1565,plain,(
    ! [A_4] : k8_relset_1(A_4,'#skF_3','#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_1559])).

tff(c_870,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_912,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_906])).

tff(c_916,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_912])).

tff(c_986,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_914,c_871,c_870,c_44])).

tff(c_1063,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1058,c_1058,c_1058,c_986])).

tff(c_1567,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_1063])).

tff(c_917,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_50])).

tff(c_943,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_917])).

tff(c_1067,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1058,c_943])).

tff(c_1305,plain,(
    ! [A_206,B_207] :
      ( k1_relset_1(A_206,A_206,B_207) = A_206
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v1_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1318,plain,(
    ! [A_206] :
      ( k1_relset_1(A_206,A_206,k2_zfmisc_1(A_206,A_206)) = A_206
      | ~ v1_funct_2(k2_zfmisc_1(A_206,A_206),A_206,A_206)
      | ~ v1_funct_1(k2_zfmisc_1(A_206,A_206)) ) ),
    inference(resolution,[status(thm)],[c_57,c_1305])).

tff(c_1997,plain,(
    ! [A_274] :
      ( k1_relat_1(k2_zfmisc_1(A_274,A_274)) = A_274
      | ~ v1_funct_2(k2_zfmisc_1(A_274,A_274),A_274,A_274)
      | ~ v1_funct_1(k2_zfmisc_1(A_274,A_274)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_1318])).

tff(c_2013,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_3','#skF_3')
    | ~ v1_funct_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_1997])).

tff(c_2019,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1073,c_1067,c_1073,c_2013])).

tff(c_2021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1567,c_2019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.60  
% 3.59/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > np__0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.59/1.61  
% 3.59/1.61  %Foreground sorts:
% 3.59/1.61  
% 3.59/1.61  
% 3.59/1.61  %Background operators:
% 3.59/1.61  
% 3.59/1.61  
% 3.59/1.61  %Foreground operators:
% 3.59/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.59/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.59/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.59/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.59/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.59/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.61  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.59/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.59/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.59/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.59/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.59/1.61  tff(np__0, type, np__0: $i).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.59/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.59/1.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.59/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.61  
% 3.59/1.62  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.59/1.62  tff(f_128, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 3.59/1.62  tff(f_108, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.59/1.62  tff(f_64, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.59/1.62  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.59/1.62  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.59/1.62  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.59/1.62  tff(f_88, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.59/1.62  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.59/1.62  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.59/1.62  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.59/1.62  tff(f_109, axiom, v1_xboole_0(np__0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', spc0_boole)).
% 3.59/1.62  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.59/1.62  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.59/1.62  tff(f_104, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 3.59/1.62  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.59/1.62  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.62  tff(c_106, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.59/1.62  tff(c_114, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_106])).
% 3.59/1.62  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.62  tff(c_113, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_106])).
% 3.59/1.62  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.62  tff(c_129, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_113, c_48])).
% 3.59/1.62  tff(c_224, plain, (![C_67, B_68, A_69]: (v1_xboole_0(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(B_68, A_69))) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.59/1.62  tff(c_238, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_129, c_224])).
% 3.59/1.62  tff(c_243, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_238])).
% 3.59/1.62  tff(c_130, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.59/1.62  tff(c_142, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_130])).
% 3.59/1.62  tff(c_168, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.59/1.62  tff(c_182, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_129, c_168])).
% 3.59/1.62  tff(c_290, plain, (![B_78, A_79]: (k1_relat_1(B_78)=A_79 | ~v1_partfun1(B_78, A_79) | ~v4_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.59/1.62  tff(c_299, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_182, c_290])).
% 3.59/1.62  tff(c_308, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_299])).
% 3.59/1.62  tff(c_409, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_308])).
% 3.59/1.62  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.62  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.62  tff(c_119, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_50])).
% 3.59/1.62  tff(c_120, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_119])).
% 3.59/1.62  tff(c_595, plain, (![C_117, A_118, B_119]: (v1_partfun1(C_117, A_118) | ~v1_funct_2(C_117, A_118, B_119) | ~v1_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | v1_xboole_0(B_119))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.59/1.62  tff(c_601, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_129, c_595])).
% 3.59/1.62  tff(c_614, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_120, c_601])).
% 3.59/1.62  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_409, c_614])).
% 3.59/1.62  tff(c_617, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_308])).
% 3.59/1.62  tff(c_44, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.62  tff(c_184, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_113, c_44])).
% 3.59/1.62  tff(c_621, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_617, c_184])).
% 3.59/1.62  tff(c_322, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.59/1.62  tff(c_336, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_322])).
% 3.59/1.62  tff(c_619, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_336])).
% 3.59/1.62  tff(c_622, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_617, c_129])).
% 3.59/1.62  tff(c_675, plain, (![A_120, B_121, C_122]: (k8_relset_1(A_120, B_121, C_122, B_121)=k1_relset_1(A_120, B_121, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.59/1.62  tff(c_677, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_622, c_675])).
% 3.59/1.62  tff(c_688, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_619, c_677])).
% 3.59/1.62  tff(c_762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_621, c_688])).
% 3.59/1.62  tff(c_763, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_238])).
% 3.59/1.62  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.59/1.62  tff(c_779, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_763, c_2])).
% 3.59/1.62  tff(c_46, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.62  tff(c_83, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.59/1.62  tff(c_788, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_779, c_83])).
% 3.59/1.62  tff(c_764, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_238])).
% 3.59/1.62  tff(c_859, plain, (![A_143]: (A_143='#skF_3' | ~v1_xboole_0(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_779, c_2])).
% 3.59/1.62  tff(c_862, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_764, c_859])).
% 3.59/1.62  tff(c_869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_788, c_862])).
% 3.59/1.62  tff(c_871, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.59/1.62  tff(c_906, plain, (![A_148]: (u1_struct_0(A_148)=k2_struct_0(A_148) | ~l1_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.59/1.62  tff(c_909, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_906])).
% 3.59/1.62  tff(c_914, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_871, c_909])).
% 3.59/1.62  tff(c_941, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_914, c_48])).
% 3.59/1.62  tff(c_42, plain, (v1_xboole_0(np__0)), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.59/1.62  tff(c_68, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.59/1.62  tff(c_72, plain, (np__0=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_68])).
% 3.59/1.62  tff(c_73, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_42])).
% 3.59/1.62  tff(c_1010, plain, (![C_169, B_170, A_171]: (v1_xboole_0(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(B_170, A_171))) | ~v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.59/1.62  tff(c_1016, plain, (![C_169]: (v1_xboole_0(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1010])).
% 3.59/1.62  tff(c_1041, plain, (![C_176]: (v1_xboole_0(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_1016])).
% 3.59/1.62  tff(c_1049, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_941, c_1041])).
% 3.59/1.62  tff(c_1058, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1049, c_2])).
% 3.59/1.62  tff(c_1073, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1058, c_8])).
% 3.59/1.62  tff(c_12, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.59/1.62  tff(c_14, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.62  tff(c_57, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 3.59/1.62  tff(c_1163, plain, (![A_182, B_183, C_184]: (k1_relset_1(A_182, B_183, C_184)=k1_relat_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.59/1.62  tff(c_1171, plain, (![A_182, B_183]: (k1_relset_1(A_182, B_183, k2_zfmisc_1(A_182, B_183))=k1_relat_1(k2_zfmisc_1(A_182, B_183)))), inference(resolution, [status(thm)], [c_57, c_1163])).
% 3.59/1.62  tff(c_1214, plain, (![A_186, B_187, C_188]: (k8_relset_1(A_186, B_187, C_188, B_187)=k1_relset_1(A_186, B_187, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.59/1.62  tff(c_1222, plain, (![A_186, B_187]: (k8_relset_1(A_186, B_187, k2_zfmisc_1(A_186, B_187), B_187)=k1_relset_1(A_186, B_187, k2_zfmisc_1(A_186, B_187)))), inference(resolution, [status(thm)], [c_57, c_1214])).
% 3.59/1.62  tff(c_1547, plain, (![A_239, B_240]: (k8_relset_1(A_239, B_240, k2_zfmisc_1(A_239, B_240), B_240)=k1_relat_1(k2_zfmisc_1(A_239, B_240)))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_1222])).
% 3.59/1.62  tff(c_1559, plain, (![A_4]: (k1_relat_1(k2_zfmisc_1(A_4, '#skF_3'))=k8_relset_1(A_4, '#skF_3', '#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_1547])).
% 3.59/1.62  tff(c_1565, plain, (![A_4]: (k8_relset_1(A_4, '#skF_3', '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_1559])).
% 3.59/1.62  tff(c_870, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.59/1.62  tff(c_912, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_906])).
% 3.59/1.62  tff(c_916, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_870, c_912])).
% 3.59/1.62  tff(c_986, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_916, c_914, c_871, c_870, c_44])).
% 3.59/1.62  tff(c_1063, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1058, c_1058, c_1058, c_986])).
% 3.59/1.62  tff(c_1567, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1565, c_1063])).
% 3.59/1.62  tff(c_917, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_914, c_50])).
% 3.59/1.62  tff(c_943, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_916, c_917])).
% 3.59/1.62  tff(c_1067, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1058, c_943])).
% 3.59/1.62  tff(c_1305, plain, (![A_206, B_207]: (k1_relset_1(A_206, A_206, B_207)=A_206 | ~m1_subset_1(B_207, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v1_funct_2(B_207, A_206, A_206) | ~v1_funct_1(B_207))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.59/1.62  tff(c_1318, plain, (![A_206]: (k1_relset_1(A_206, A_206, k2_zfmisc_1(A_206, A_206))=A_206 | ~v1_funct_2(k2_zfmisc_1(A_206, A_206), A_206, A_206) | ~v1_funct_1(k2_zfmisc_1(A_206, A_206)))), inference(resolution, [status(thm)], [c_57, c_1305])).
% 3.59/1.62  tff(c_1997, plain, (![A_274]: (k1_relat_1(k2_zfmisc_1(A_274, A_274))=A_274 | ~v1_funct_2(k2_zfmisc_1(A_274, A_274), A_274, A_274) | ~v1_funct_1(k2_zfmisc_1(A_274, A_274)))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_1318])).
% 3.59/1.62  tff(c_2013, plain, (k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))='#skF_3' | ~v1_funct_2('#skF_3', '#skF_3', '#skF_3') | ~v1_funct_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_1997])).
% 3.59/1.62  tff(c_2019, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1073, c_1067, c_1073, c_2013])).
% 3.59/1.62  tff(c_2021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1567, c_2019])).
% 3.59/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.62  
% 3.59/1.62  Inference rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Ref     : 0
% 3.59/1.62  #Sup     : 488
% 3.59/1.62  #Fact    : 0
% 3.59/1.62  #Define  : 0
% 3.59/1.62  #Split   : 5
% 3.59/1.62  #Chain   : 0
% 3.59/1.62  #Close   : 0
% 3.59/1.62  
% 3.59/1.62  Ordering : KBO
% 3.59/1.62  
% 3.59/1.62  Simplification rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Subsume      : 100
% 3.59/1.62  #Demod        : 254
% 3.59/1.62  #Tautology    : 223
% 3.59/1.62  #SimpNegUnit  : 13
% 3.59/1.62  #BackRed      : 48
% 3.59/1.62  
% 3.59/1.62  #Partial instantiations: 0
% 3.59/1.62  #Strategies tried      : 1
% 3.59/1.62  
% 3.59/1.62  Timing (in seconds)
% 3.59/1.63  ----------------------
% 3.59/1.63  Preprocessing        : 0.33
% 3.59/1.63  Parsing              : 0.18
% 3.98/1.63  CNF conversion       : 0.02
% 3.98/1.63  Main loop            : 0.53
% 3.98/1.63  Inferencing          : 0.19
% 3.98/1.63  Reduction            : 0.17
% 3.98/1.63  Demodulation         : 0.12
% 3.98/1.63  BG Simplification    : 0.03
% 3.98/1.63  Subsumption          : 0.09
% 3.98/1.63  Abstraction          : 0.03
% 3.98/1.63  MUC search           : 0.00
% 3.98/1.63  Cooper               : 0.00
% 3.98/1.63  Total                : 0.90
% 3.98/1.63  Index Insertion      : 0.00
% 3.98/1.63  Index Deletion       : 0.00
% 3.98/1.63  Index Matching       : 0.00
% 3.98/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
