%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:12 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 655 expanded)
%              Number of leaves         :   46 ( 244 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 (1460 expanded)
%              Number of equality atoms :   69 ( 654 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_69,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_133,negated_conjecture,(
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

tff(f_114,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(c_26,plain,(
    ! [A_19] : k10_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_892,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k8_relset_1(A_182,B_183,C_184,D_185) = k10_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_895,plain,(
    ! [A_182,B_183,D_185] : k8_relset_1(A_182,B_183,k1_xboole_0,D_185) = k10_relat_1(k1_xboole_0,D_185) ),
    inference(resolution,[status(thm)],[c_10,c_892])).

tff(c_902,plain,(
    ! [A_186,B_187,D_188] : k8_relset_1(A_186,B_187,k1_xboole_0,D_188) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_895])).

tff(c_633,plain,(
    ! [A_138] : k6_relat_1(A_138) = k6_partfun1(A_138) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_639,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_28])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_125,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_133,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_125])).

tff(c_60,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_132,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_125])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_143,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_132,c_54])).

tff(c_146,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_143,c_146])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_24,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_201,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_215,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_143,c_201])).

tff(c_195,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k2_relat_1(B_55),A_56)
      | ~ v5_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_516,plain,(
    ! [B_114,A_115] :
      ( k3_xboole_0(k2_relat_1(B_114),A_115) = k2_relat_1(B_114)
      | ~ v5_relat_1(B_114,A_115)
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k3_xboole_0(k2_relat_1(B_17),A_16)) = k10_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_598,plain,(
    ! [B_135,A_136] :
      ( k10_relat_1(B_135,k2_relat_1(B_135)) = k10_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135)
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_22])).

tff(c_600,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k10_relat_1('#skF_3',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_598])).

tff(c_605,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k10_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_600])).

tff(c_231,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_245,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_143,c_231])).

tff(c_310,plain,(
    ! [B_83,A_84] :
      ( k1_relat_1(B_83) = A_84
      | ~ v1_partfun1(B_83,A_84)
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_313,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_245,c_310])).

tff(c_319,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_313])).

tff(c_329,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_52,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_103,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_134,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_56])).

tff(c_144,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_134])).

tff(c_423,plain,(
    ! [B_108,C_109,A_110] :
      ( k1_xboole_0 = B_108
      | v1_partfun1(C_109,A_110)
      | ~ v1_funct_2(C_109,A_110,B_108)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_108)))
      | ~ v1_funct_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_426,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_143,c_423])).

tff(c_439,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_144,c_426])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_103,c_439])).

tff(c_442,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_448,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_143])).

tff(c_529,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k8_relset_1(A_118,B_119,C_120,D_121) = k10_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_539,plain,(
    ! [D_121] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_121) = k10_relat_1('#skF_3',D_121) ),
    inference(resolution,[status(thm)],[c_448,c_529])).

tff(c_50,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_200,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_132,c_50])).

tff(c_446,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_442,c_200])).

tff(c_555,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_446])).

tff(c_610,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_555])).

tff(c_617,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_610])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_617])).

tff(c_623,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_653,plain,(
    ! [A_139] :
      ( u1_struct_0(A_139) = k2_struct_0(A_139)
      | ~ l1_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_656,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_653])).

tff(c_661,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_656])).

tff(c_692,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_661,c_54])).

tff(c_845,plain,(
    ! [A_175,B_176] :
      ( k8_relset_1(A_175,A_175,k6_partfun1(A_175),B_176) = B_176
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_847,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_692,c_845])).

tff(c_851,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_847])).

tff(c_906,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_851])).

tff(c_622,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_659,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_653])).

tff(c_663,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_659])).

tff(c_720,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_661,c_623,c_622,c_50])).

tff(c_925,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_906,c_906,c_906,c_720])).

tff(c_882,plain,(
    ! [A_181] : k8_relset_1(A_181,A_181,k6_partfun1(A_181),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_845])).

tff(c_889,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_882])).

tff(c_1151,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_906,c_906,c_906,c_906,c_889])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_925,c_1151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.46  
% 3.26/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.47  
% 3.26/1.47  %Foreground sorts:
% 3.26/1.47  
% 3.26/1.47  
% 3.26/1.47  %Background operators:
% 3.26/1.47  
% 3.26/1.47  
% 3.26/1.47  %Foreground operators:
% 3.26/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.47  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.26/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.26/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.26/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.26/1.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.26/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.26/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.26/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.26/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.47  
% 3.26/1.49  tff(f_68, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 3.26/1.49  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.26/1.49  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.26/1.49  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.26/1.49  tff(f_69, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.26/1.49  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.26/1.49  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.26/1.49  tff(f_133, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.26/1.49  tff(f_114, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.26/1.49  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.49  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.26/1.49  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.26/1.49  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.26/1.49  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.26/1.49  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.26/1.49  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.26/1.49  tff(f_106, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 3.26/1.49  tff(f_110, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 3.26/1.49  tff(c_26, plain, (![A_19]: (k10_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.49  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.49  tff(c_892, plain, (![A_182, B_183, C_184, D_185]: (k8_relset_1(A_182, B_183, C_184, D_185)=k10_relat_1(C_184, D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.49  tff(c_895, plain, (![A_182, B_183, D_185]: (k8_relset_1(A_182, B_183, k1_xboole_0, D_185)=k10_relat_1(k1_xboole_0, D_185))), inference(resolution, [status(thm)], [c_10, c_892])).
% 3.26/1.49  tff(c_902, plain, (![A_186, B_187, D_188]: (k8_relset_1(A_186, B_187, k1_xboole_0, D_188)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_895])).
% 3.26/1.49  tff(c_633, plain, (![A_138]: (k6_relat_1(A_138)=k6_partfun1(A_138))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.26/1.49  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.49  tff(c_639, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_633, c_28])).
% 3.26/1.49  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.49  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.26/1.49  tff(c_62, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.26/1.49  tff(c_125, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.26/1.49  tff(c_133, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_125])).
% 3.26/1.49  tff(c_60, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.26/1.49  tff(c_132, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_125])).
% 3.26/1.49  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.26/1.49  tff(c_143, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_132, c_54])).
% 3.26/1.49  tff(c_146, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.49  tff(c_149, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_143, c_146])).
% 3.26/1.49  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 3.26/1.49  tff(c_24, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.49  tff(c_201, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.49  tff(c_215, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_143, c_201])).
% 3.26/1.49  tff(c_195, plain, (![B_55, A_56]: (r1_tarski(k2_relat_1(B_55), A_56) | ~v5_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.49  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.49  tff(c_516, plain, (![B_114, A_115]: (k3_xboole_0(k2_relat_1(B_114), A_115)=k2_relat_1(B_114) | ~v5_relat_1(B_114, A_115) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_195, c_2])).
% 3.26/1.49  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k3_xboole_0(k2_relat_1(B_17), A_16))=k10_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.26/1.49  tff(c_598, plain, (![B_135, A_136]: (k10_relat_1(B_135, k2_relat_1(B_135))=k10_relat_1(B_135, A_136) | ~v1_relat_1(B_135) | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_516, c_22])).
% 3.26/1.49  tff(c_600, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k10_relat_1('#skF_3', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_215, c_598])).
% 3.26/1.49  tff(c_605, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k10_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_600])).
% 3.26/1.49  tff(c_231, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.49  tff(c_245, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_143, c_231])).
% 3.26/1.49  tff(c_310, plain, (![B_83, A_84]: (k1_relat_1(B_83)=A_84 | ~v1_partfun1(B_83, A_84) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.26/1.49  tff(c_313, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_245, c_310])).
% 3.26/1.49  tff(c_319, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_313])).
% 3.26/1.49  tff(c_329, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_319])).
% 3.26/1.49  tff(c_52, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.26/1.49  tff(c_103, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.26/1.49  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.26/1.49  tff(c_56, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.26/1.49  tff(c_134, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_56])).
% 3.26/1.49  tff(c_144, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_134])).
% 3.26/1.49  tff(c_423, plain, (![B_108, C_109, A_110]: (k1_xboole_0=B_108 | v1_partfun1(C_109, A_110) | ~v1_funct_2(C_109, A_110, B_108) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_108))) | ~v1_funct_1(C_109))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.26/1.49  tff(c_426, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_143, c_423])).
% 3.26/1.49  tff(c_439, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_144, c_426])).
% 3.26/1.49  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_329, c_103, c_439])).
% 3.26/1.49  tff(c_442, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_319])).
% 3.26/1.49  tff(c_448, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_143])).
% 3.26/1.49  tff(c_529, plain, (![A_118, B_119, C_120, D_121]: (k8_relset_1(A_118, B_119, C_120, D_121)=k10_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.49  tff(c_539, plain, (![D_121]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_121)=k10_relat_1('#skF_3', D_121))), inference(resolution, [status(thm)], [c_448, c_529])).
% 3.26/1.49  tff(c_50, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.26/1.49  tff(c_200, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_132, c_50])).
% 3.26/1.49  tff(c_446, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_442, c_200])).
% 3.26/1.49  tff(c_555, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_446])).
% 3.26/1.49  tff(c_610, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_555])).
% 3.26/1.49  tff(c_617, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_610])).
% 3.26/1.49  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_617])).
% 3.26/1.49  tff(c_623, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.49  tff(c_653, plain, (![A_139]: (u1_struct_0(A_139)=k2_struct_0(A_139) | ~l1_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.26/1.49  tff(c_656, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_653])).
% 3.26/1.49  tff(c_661, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_623, c_656])).
% 3.26/1.49  tff(c_692, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_661, c_54])).
% 3.26/1.49  tff(c_845, plain, (![A_175, B_176]: (k8_relset_1(A_175, A_175, k6_partfun1(A_175), B_176)=B_176 | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.26/1.49  tff(c_847, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_692, c_845])).
% 3.26/1.49  tff(c_851, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_639, c_847])).
% 3.26/1.49  tff(c_906, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_902, c_851])).
% 3.26/1.49  tff(c_622, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.49  tff(c_659, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_653])).
% 3.26/1.49  tff(c_663, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_622, c_659])).
% 3.26/1.49  tff(c_720, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_663, c_661, c_623, c_622, c_50])).
% 3.26/1.49  tff(c_925, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_906, c_906, c_906, c_906, c_720])).
% 3.26/1.49  tff(c_882, plain, (![A_181]: (k8_relset_1(A_181, A_181, k6_partfun1(A_181), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_845])).
% 3.26/1.49  tff(c_889, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_639, c_882])).
% 3.26/1.49  tff(c_1151, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_906, c_906, c_906, c_906, c_906, c_889])).
% 3.26/1.49  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_925, c_1151])).
% 3.26/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.49  
% 3.26/1.49  Inference rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Ref     : 0
% 3.26/1.49  #Sup     : 249
% 3.26/1.49  #Fact    : 0
% 3.26/1.49  #Define  : 0
% 3.26/1.49  #Split   : 3
% 3.26/1.49  #Chain   : 0
% 3.26/1.49  #Close   : 0
% 3.26/1.49  
% 3.26/1.49  Ordering : KBO
% 3.26/1.49  
% 3.26/1.49  Simplification rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Subsume      : 8
% 3.26/1.49  #Demod        : 209
% 3.26/1.49  #Tautology    : 172
% 3.26/1.49  #SimpNegUnit  : 3
% 3.26/1.49  #BackRed      : 41
% 3.26/1.49  
% 3.26/1.49  #Partial instantiations: 0
% 3.26/1.49  #Strategies tried      : 1
% 3.26/1.49  
% 3.26/1.49  Timing (in seconds)
% 3.26/1.49  ----------------------
% 3.26/1.49  Preprocessing        : 0.34
% 3.26/1.49  Parsing              : 0.19
% 3.26/1.49  CNF conversion       : 0.02
% 3.26/1.49  Main loop            : 0.39
% 3.26/1.49  Inferencing          : 0.14
% 3.26/1.49  Reduction            : 0.13
% 3.26/1.49  Demodulation         : 0.10
% 3.26/1.49  BG Simplification    : 0.02
% 3.26/1.49  Subsumption          : 0.05
% 3.26/1.49  Abstraction          : 0.02
% 3.26/1.49  MUC search           : 0.00
% 3.26/1.49  Cooper               : 0.00
% 3.26/1.49  Total                : 0.77
% 3.26/1.49  Index Insertion      : 0.00
% 3.26/1.49  Index Deletion       : 0.00
% 3.26/1.49  Index Matching       : 0.00
% 3.26/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
