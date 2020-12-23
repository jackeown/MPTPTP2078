%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:09 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 996 expanded)
%              Number of leaves         :   43 ( 358 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 (2332 expanded)
%              Number of equality atoms :   68 ( 947 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_110,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_118,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_110])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_117,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_110])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_129,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_117,c_48])).

tff(c_239,plain,(
    ! [C_70,B_71,A_72] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(B_71,A_72)))
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_253,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_129,c_239])).

tff(c_257,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_130,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_142,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_130])).

tff(c_168,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_182,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_129,c_168])).

tff(c_265,plain,(
    ! [B_74,A_75] :
      ( k1_relat_1(B_74) = A_75
      | ~ v1_partfun1(B_74,A_75)
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_274,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_265])).

tff(c_283,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_274])).

tff(c_342,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_119,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_50])).

tff(c_128,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_119])).

tff(c_572,plain,(
    ! [C_121,A_122,B_123] :
      ( v1_partfun1(C_121,A_122)
      | ~ v1_funct_2(C_121,A_122,B_123)
      | ~ v1_funct_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | v1_xboole_0(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_578,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_129,c_572])).

tff(c_591,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_128,c_578])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_342,c_591])).

tff(c_594,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_44,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_184,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_117,c_44])).

tff(c_598,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_594,c_184])).

tff(c_322,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_336,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_322])).

tff(c_596,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_336])).

tff(c_599,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_129])).

tff(c_807,plain,(
    ! [A_144,B_145,C_146] :
      ( k8_relset_1(A_144,B_145,C_146,B_145) = k1_relset_1(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_811,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_599,c_807])).

tff(c_820,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_811])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_820])).

tff(c_823,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_831,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_823,c_4])).

tff(c_46,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_83,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_842,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_83])).

tff(c_824,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_951,plain,(
    ! [A_153] :
      ( A_153 = '#skF_3'
      | ~ v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_823,c_6])).

tff(c_954,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_824,c_951])).

tff(c_961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_954])).

tff(c_963,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_994,plain,(
    ! [A_156] :
      ( u1_struct_0(A_156) = k2_struct_0(A_156)
      | ~ l1_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_997,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_994])).

tff(c_1002,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_997])).

tff(c_1034,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1002,c_48])).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_68,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_68])).

tff(c_73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2])).

tff(c_1119,plain,(
    ! [C_183,B_184,A_185] :
      ( v1_xboole_0(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(B_184,A_185)))
      | ~ v1_xboole_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1125,plain,(
    ! [C_183] :
      ( v1_xboole_0(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1119])).

tff(c_1133,plain,(
    ! [C_186] :
      ( v1_xboole_0(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1125])).

tff(c_1141,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1034,c_1133])).

tff(c_1150,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1141,c_4])).

tff(c_1165,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1150,c_10])).

tff(c_14,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_1255,plain,(
    ! [A_192,B_193,C_194] :
      ( k1_relset_1(A_192,B_193,C_194) = k1_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1263,plain,(
    ! [A_192,B_193] : k1_relset_1(A_192,B_193,k2_zfmisc_1(A_192,B_193)) = k1_relat_1(k2_zfmisc_1(A_192,B_193)) ),
    inference(resolution,[status(thm)],[c_57,c_1255])).

tff(c_1347,plain,(
    ! [A_203,B_204,C_205] :
      ( k8_relset_1(A_203,B_204,C_205,B_204) = k1_relset_1(A_203,B_204,C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1355,plain,(
    ! [A_203,B_204] : k8_relset_1(A_203,B_204,k2_zfmisc_1(A_203,B_204),B_204) = k1_relset_1(A_203,B_204,k2_zfmisc_1(A_203,B_204)) ),
    inference(resolution,[status(thm)],[c_57,c_1347])).

tff(c_1536,plain,(
    ! [A_229,B_230] : k8_relset_1(A_229,B_230,k2_zfmisc_1(A_229,B_230),B_230) = k1_relat_1(k2_zfmisc_1(A_229,B_230)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1355])).

tff(c_1548,plain,(
    ! [A_4] : k1_relat_1(k2_zfmisc_1(A_4,'#skF_3')) = k8_relset_1(A_4,'#skF_3','#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_1536])).

tff(c_1554,plain,(
    ! [A_4] : k8_relset_1(A_4,'#skF_3','#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1165,c_1548])).

tff(c_962,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1000,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_994])).

tff(c_1004,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_1000])).

tff(c_1078,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1002,c_963,c_962,c_44])).

tff(c_1155,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1150,c_1150,c_1150,c_1078])).

tff(c_1578,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_1155])).

tff(c_1005,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_50])).

tff(c_1018,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1005])).

tff(c_1161,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1150,c_1018])).

tff(c_1404,plain,(
    ! [A_217,B_218] :
      ( k1_relset_1(A_217,A_217,B_218) = A_217
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ v1_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1417,plain,(
    ! [A_217] :
      ( k1_relset_1(A_217,A_217,k2_zfmisc_1(A_217,A_217)) = A_217
      | ~ v1_funct_2(k2_zfmisc_1(A_217,A_217),A_217,A_217)
      | ~ v1_funct_1(k2_zfmisc_1(A_217,A_217)) ) ),
    inference(resolution,[status(thm)],[c_57,c_1404])).

tff(c_2145,plain,(
    ! [A_290] :
      ( k1_relat_1(k2_zfmisc_1(A_290,A_290)) = A_290
      | ~ v1_funct_2(k2_zfmisc_1(A_290,A_290),A_290,A_290)
      | ~ v1_funct_1(k2_zfmisc_1(A_290,A_290)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1417])).

tff(c_2161,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_3','#skF_3')
    | ~ v1_funct_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_2145])).

tff(c_2167,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1165,c_1161,c_1165,c_2161])).

tff(c_2169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1578,c_2167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:31:59 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.68  
% 3.60/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.60/1.68  
% 3.60/1.68  %Foreground sorts:
% 3.60/1.68  
% 3.60/1.68  
% 3.60/1.68  %Background operators:
% 3.60/1.68  
% 3.60/1.68  
% 3.60/1.68  %Foreground operators:
% 3.60/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.60/1.68  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.60/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.60/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.60/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.60/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.60/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.60/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.60/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.60/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.60/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.60/1.68  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.60/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.60/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.68  
% 3.94/1.70  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.94/1.70  tff(f_128, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.94/1.70  tff(f_109, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.94/1.70  tff(f_65, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.94/1.70  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.94/1.70  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.94/1.70  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.94/1.70  tff(f_89, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.94/1.70  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.94/1.70  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.94/1.70  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.94/1.70  tff(f_38, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.94/1.70  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 3.94/1.70  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.94/1.70  tff(f_48, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.94/1.70  tff(f_105, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 3.94/1.70  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.70  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.94/1.70  tff(c_110, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.94/1.70  tff(c_118, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_110])).
% 3.94/1.70  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.94/1.70  tff(c_117, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_110])).
% 3.94/1.70  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.94/1.70  tff(c_129, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_117, c_48])).
% 3.94/1.70  tff(c_239, plain, (![C_70, B_71, A_72]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(B_71, A_72))) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.94/1.70  tff(c_253, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_129, c_239])).
% 3.94/1.70  tff(c_257, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_253])).
% 3.94/1.70  tff(c_130, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.94/1.70  tff(c_142, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_130])).
% 3.94/1.70  tff(c_168, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.70  tff(c_182, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_129, c_168])).
% 3.94/1.70  tff(c_265, plain, (![B_74, A_75]: (k1_relat_1(B_74)=A_75 | ~v1_partfun1(B_74, A_75) | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.94/1.70  tff(c_274, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_182, c_265])).
% 3.94/1.70  tff(c_283, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_274])).
% 3.94/1.70  tff(c_342, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_283])).
% 3.94/1.70  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.94/1.70  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.94/1.70  tff(c_119, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_50])).
% 3.94/1.70  tff(c_128, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_119])).
% 3.94/1.70  tff(c_572, plain, (![C_121, A_122, B_123]: (v1_partfun1(C_121, A_122) | ~v1_funct_2(C_121, A_122, B_123) | ~v1_funct_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | v1_xboole_0(B_123))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.94/1.70  tff(c_578, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_129, c_572])).
% 3.94/1.70  tff(c_591, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_128, c_578])).
% 3.94/1.70  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_342, c_591])).
% 3.94/1.70  tff(c_594, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_283])).
% 3.94/1.70  tff(c_44, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.94/1.70  tff(c_184, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_117, c_44])).
% 3.94/1.70  tff(c_598, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_594, c_184])).
% 3.94/1.70  tff(c_322, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.94/1.70  tff(c_336, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_322])).
% 3.94/1.70  tff(c_596, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_336])).
% 3.94/1.70  tff(c_599, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_129])).
% 3.94/1.70  tff(c_807, plain, (![A_144, B_145, C_146]: (k8_relset_1(A_144, B_145, C_146, B_145)=k1_relset_1(A_144, B_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.94/1.70  tff(c_811, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_599, c_807])).
% 3.94/1.70  tff(c_820, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_811])).
% 3.94/1.70  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_598, c_820])).
% 3.94/1.70  tff(c_823, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_253])).
% 3.94/1.70  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.94/1.70  tff(c_831, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_823, c_4])).
% 3.94/1.70  tff(c_46, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.94/1.70  tff(c_83, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.94/1.70  tff(c_842, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_831, c_83])).
% 3.94/1.70  tff(c_824, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_253])).
% 3.94/1.70  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.94/1.70  tff(c_951, plain, (![A_153]: (A_153='#skF_3' | ~v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_823, c_6])).
% 3.94/1.70  tff(c_954, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_824, c_951])).
% 3.94/1.70  tff(c_961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_842, c_954])).
% 3.94/1.70  tff(c_963, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.94/1.70  tff(c_994, plain, (![A_156]: (u1_struct_0(A_156)=k2_struct_0(A_156) | ~l1_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.94/1.70  tff(c_997, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_994])).
% 3.94/1.70  tff(c_1002, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_963, c_997])).
% 3.94/1.70  tff(c_1034, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1002, c_48])).
% 3.94/1.70  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.94/1.70  tff(c_68, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.94/1.70  tff(c_72, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_68])).
% 3.94/1.70  tff(c_73, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2])).
% 3.94/1.70  tff(c_1119, plain, (![C_183, B_184, A_185]: (v1_xboole_0(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(B_184, A_185))) | ~v1_xboole_0(A_185))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.94/1.70  tff(c_1125, plain, (![C_183]: (v1_xboole_0(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1119])).
% 3.94/1.70  tff(c_1133, plain, (![C_186]: (v1_xboole_0(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_1125])).
% 3.94/1.70  tff(c_1141, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1034, c_1133])).
% 3.94/1.70  tff(c_1150, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1141, c_4])).
% 3.94/1.70  tff(c_1165, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1150, c_10])).
% 3.94/1.70  tff(c_14, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.94/1.70  tff(c_16, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.94/1.70  tff(c_57, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.94/1.70  tff(c_1255, plain, (![A_192, B_193, C_194]: (k1_relset_1(A_192, B_193, C_194)=k1_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.94/1.70  tff(c_1263, plain, (![A_192, B_193]: (k1_relset_1(A_192, B_193, k2_zfmisc_1(A_192, B_193))=k1_relat_1(k2_zfmisc_1(A_192, B_193)))), inference(resolution, [status(thm)], [c_57, c_1255])).
% 3.94/1.70  tff(c_1347, plain, (![A_203, B_204, C_205]: (k8_relset_1(A_203, B_204, C_205, B_204)=k1_relset_1(A_203, B_204, C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.94/1.70  tff(c_1355, plain, (![A_203, B_204]: (k8_relset_1(A_203, B_204, k2_zfmisc_1(A_203, B_204), B_204)=k1_relset_1(A_203, B_204, k2_zfmisc_1(A_203, B_204)))), inference(resolution, [status(thm)], [c_57, c_1347])).
% 3.94/1.70  tff(c_1536, plain, (![A_229, B_230]: (k8_relset_1(A_229, B_230, k2_zfmisc_1(A_229, B_230), B_230)=k1_relat_1(k2_zfmisc_1(A_229, B_230)))), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1355])).
% 3.94/1.70  tff(c_1548, plain, (![A_4]: (k1_relat_1(k2_zfmisc_1(A_4, '#skF_3'))=k8_relset_1(A_4, '#skF_3', '#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_1536])).
% 3.94/1.70  tff(c_1554, plain, (![A_4]: (k8_relset_1(A_4, '#skF_3', '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1165, c_1548])).
% 3.94/1.70  tff(c_962, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.94/1.70  tff(c_1000, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_994])).
% 3.94/1.70  tff(c_1004, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_962, c_1000])).
% 3.94/1.70  tff(c_1078, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1002, c_963, c_962, c_44])).
% 3.94/1.70  tff(c_1155, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1150, c_1150, c_1150, c_1078])).
% 3.94/1.70  tff(c_1578, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_1155])).
% 3.94/1.70  tff(c_1005, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_50])).
% 3.94/1.70  tff(c_1018, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1005])).
% 3.94/1.70  tff(c_1161, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1150, c_1018])).
% 3.94/1.70  tff(c_1404, plain, (![A_217, B_218]: (k1_relset_1(A_217, A_217, B_218)=A_217 | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~v1_funct_2(B_218, A_217, A_217) | ~v1_funct_1(B_218))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.94/1.70  tff(c_1417, plain, (![A_217]: (k1_relset_1(A_217, A_217, k2_zfmisc_1(A_217, A_217))=A_217 | ~v1_funct_2(k2_zfmisc_1(A_217, A_217), A_217, A_217) | ~v1_funct_1(k2_zfmisc_1(A_217, A_217)))), inference(resolution, [status(thm)], [c_57, c_1404])).
% 3.94/1.70  tff(c_2145, plain, (![A_290]: (k1_relat_1(k2_zfmisc_1(A_290, A_290))=A_290 | ~v1_funct_2(k2_zfmisc_1(A_290, A_290), A_290, A_290) | ~v1_funct_1(k2_zfmisc_1(A_290, A_290)))), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1417])).
% 3.94/1.70  tff(c_2161, plain, (k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))='#skF_3' | ~v1_funct_2('#skF_3', '#skF_3', '#skF_3') | ~v1_funct_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_2145])).
% 3.94/1.70  tff(c_2167, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1165, c_1161, c_1165, c_2161])).
% 3.94/1.70  tff(c_2169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1578, c_2167])).
% 3.94/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.70  
% 3.94/1.70  Inference rules
% 3.94/1.70  ----------------------
% 3.94/1.70  #Ref     : 0
% 3.94/1.70  #Sup     : 530
% 3.94/1.70  #Fact    : 0
% 3.94/1.70  #Define  : 0
% 3.94/1.70  #Split   : 4
% 3.94/1.70  #Chain   : 0
% 3.94/1.70  #Close   : 0
% 3.94/1.70  
% 3.94/1.70  Ordering : KBO
% 3.94/1.70  
% 3.94/1.70  Simplification rules
% 3.94/1.70  ----------------------
% 3.94/1.70  #Subsume      : 109
% 3.94/1.70  #Demod        : 281
% 3.94/1.70  #Tautology    : 240
% 3.94/1.70  #SimpNegUnit  : 14
% 3.94/1.70  #BackRed      : 50
% 3.94/1.70  
% 3.94/1.70  #Partial instantiations: 0
% 3.94/1.70  #Strategies tried      : 1
% 3.94/1.70  
% 3.94/1.70  Timing (in seconds)
% 3.94/1.70  ----------------------
% 3.94/1.71  Preprocessing        : 0.34
% 3.94/1.71  Parsing              : 0.19
% 3.94/1.71  CNF conversion       : 0.02
% 3.94/1.71  Main loop            : 0.54
% 3.94/1.71  Inferencing          : 0.19
% 3.94/1.71  Reduction            : 0.17
% 3.94/1.71  Demodulation         : 0.12
% 3.94/1.71  BG Simplification    : 0.03
% 3.94/1.71  Subsumption          : 0.10
% 3.94/1.71  Abstraction          : 0.03
% 3.94/1.71  MUC search           : 0.00
% 3.94/1.71  Cooper               : 0.00
% 3.94/1.71  Total                : 0.92
% 3.94/1.71  Index Insertion      : 0.00
% 3.94/1.71  Index Deletion       : 0.00
% 3.94/1.71  Index Matching       : 0.00
% 3.94/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
