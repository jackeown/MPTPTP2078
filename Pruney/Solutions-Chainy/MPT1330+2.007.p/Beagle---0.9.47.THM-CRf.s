%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:09 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 463 expanded)
%              Number of leaves         :   44 ( 172 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 (1165 expanded)
%              Number of equality atoms :   60 ( 457 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_78,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(c_52,plain,
    ( k2_struct_0('#skF_4') = k1_xboole_0
    | k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_73,plain,(
    k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_62,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_74,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_82,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_74])).

tff(c_60,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_81,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_74])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54])).

tff(c_142,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_83])).

tff(c_22,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_146,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_142,c_22])).

tff(c_153,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_157,plain,(
    v4_relat_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_142,c_153])).

tff(c_177,plain,(
    ! [B_68,A_69] :
      ( k1_relat_1(B_68) = A_69
      | ~ v1_partfun1(B_68,A_69)
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_180,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_157,c_177])).

tff(c_183,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_180])).

tff(c_184,plain,(
    ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_84,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_56])).

tff(c_108,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84])).

tff(c_286,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_partfun1(C_97,A_98)
      | ~ v1_funct_2(C_97,A_98,B_99)
      | ~ v1_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | v1_xboole_0(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_289,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_142,c_286])).

tff(c_292,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_108,c_289])).

tff(c_293,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_292])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_296,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_293,c_2])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_296])).

tff(c_301,plain,(
    k2_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_50,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_123,plain,(
    k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_50])).

tff(c_306,plain,(
    k8_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_301,c_123])).

tff(c_305,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_142])).

tff(c_354,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_358,plain,(
    k1_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_305,c_354])).

tff(c_404,plain,(
    ! [A_113,B_114,C_115] :
      ( k8_relset_1(A_113,B_114,C_115,B_114) = k1_relset_1(A_113,B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_406,plain,(
    k8_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) = k1_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_305,c_404])).

tff(c_408,plain,(
    k8_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_406])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_408])).

tff(c_411,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_436,plain,(
    ! [A_117] :
      ( u1_struct_0(A_117) = k2_struct_0(A_117)
      | ~ l1_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_442,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_436])).

tff(c_446,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_442])).

tff(c_412,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_439,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_436])).

tff(c_444,plain,(
    u1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_439])).

tff(c_474,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_444,c_412,c_411,c_50])).

tff(c_452,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_54])).

tff(c_453,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_452])).

tff(c_491,plain,(
    ! [C_129,A_130,B_131] :
      ( v1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_495,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_453,c_491])).

tff(c_496,plain,(
    ! [C_132,A_133,B_134] :
      ( v4_relat_1(C_132,A_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_500,plain,(
    v4_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_453,c_496])).

tff(c_506,plain,(
    ! [B_138,A_139] :
      ( r1_tarski(k1_relat_1(B_138),A_139)
      | ~ v4_relat_1(B_138,A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_475,plain,(
    ! [A_125,B_126] :
      ( k3_tarski(A_125) != k1_xboole_0
      | ~ r2_hidden(B_126,A_125)
      | k1_xboole_0 = B_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_478,plain,(
    ! [A_2,C_6] :
      ( k3_tarski(k1_zfmisc_1(A_2)) != k1_xboole_0
      | k1_xboole_0 = C_6
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_475])).

tff(c_483,plain,(
    ! [A_2,C_6] :
      ( k1_xboole_0 != A_2
      | k1_xboole_0 = C_6
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_478])).

tff(c_518,plain,(
    ! [A_143,B_144] :
      ( k1_xboole_0 != A_143
      | k1_relat_1(B_144) = k1_xboole_0
      | ~ v4_relat_1(B_144,A_143)
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_506,c_483])).

tff(c_521,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_500,c_518])).

tff(c_524,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_521])).

tff(c_593,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_relset_1(A_150,B_151,C_152) = k1_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_596,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_453,c_593])).

tff(c_598,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_596])).

tff(c_652,plain,(
    ! [A_166,B_167,C_168] :
      ( k8_relset_1(A_166,B_167,C_168,B_167) = k1_relset_1(A_166,B_167,C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_654,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_453,c_652])).

tff(c_656,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_654])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.48  
% 2.90/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.90/1.48  
% 2.90/1.48  %Foreground sorts:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Background operators:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Foreground operators:
% 2.90/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.90/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.90/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.90/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.90/1.48  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.90/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.90/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.90/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.90/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.48  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.90/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.90/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.48  
% 2.90/1.50  tff(f_129, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 2.90/1.50  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.90/1.50  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.90/1.50  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.50  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.90/1.50  tff(f_78, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.90/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.90/1.50  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.90/1.50  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.90/1.50  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.90/1.50  tff(f_38, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.90/1.50  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.90/1.50  tff(f_110, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.90/1.50  tff(c_52, plain, (k2_struct_0('#skF_4')=k1_xboole_0 | k2_struct_0('#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.90/1.50  tff(c_73, plain, (k2_struct_0('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 2.90/1.50  tff(c_62, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.90/1.50  tff(c_74, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.50  tff(c_82, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_74])).
% 2.90/1.50  tff(c_60, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.90/1.50  tff(c_81, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_74])).
% 2.90/1.50  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.90/1.50  tff(c_83, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_54])).
% 2.90/1.50  tff(c_142, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_83])).
% 2.90/1.50  tff(c_22, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.50  tff(c_146, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_142, c_22])).
% 2.90/1.50  tff(c_153, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.90/1.50  tff(c_157, plain, (v4_relat_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_142, c_153])).
% 2.90/1.50  tff(c_177, plain, (![B_68, A_69]: (k1_relat_1(B_68)=A_69 | ~v1_partfun1(B_68, A_69) | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.90/1.50  tff(c_180, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_157, c_177])).
% 2.90/1.50  tff(c_183, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_180])).
% 2.90/1.50  tff(c_184, plain, (~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_183])).
% 2.90/1.50  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.90/1.50  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.90/1.50  tff(c_84, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_56])).
% 2.90/1.50  tff(c_108, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84])).
% 2.90/1.50  tff(c_286, plain, (![C_97, A_98, B_99]: (v1_partfun1(C_97, A_98) | ~v1_funct_2(C_97, A_98, B_99) | ~v1_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | v1_xboole_0(B_99))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.50  tff(c_289, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_142, c_286])).
% 2.90/1.50  tff(c_292, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_108, c_289])).
% 2.90/1.50  tff(c_293, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_184, c_292])).
% 2.90/1.50  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.90/1.50  tff(c_296, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_293, c_2])).
% 2.90/1.50  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_296])).
% 2.90/1.50  tff(c_301, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_183])).
% 2.90/1.50  tff(c_50, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.90/1.50  tff(c_123, plain, (k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_50])).
% 2.90/1.50  tff(c_306, plain, (k8_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_301, c_123])).
% 2.90/1.50  tff(c_305, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_142])).
% 2.90/1.50  tff(c_354, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.50  tff(c_358, plain, (k1_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_305, c_354])).
% 2.90/1.50  tff(c_404, plain, (![A_113, B_114, C_115]: (k8_relset_1(A_113, B_114, C_115, B_114)=k1_relset_1(A_113, B_114, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.90/1.50  tff(c_406, plain, (k8_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))=k1_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_305, c_404])).
% 2.90/1.50  tff(c_408, plain, (k8_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_406])).
% 2.90/1.50  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_408])).
% 2.90/1.50  tff(c_411, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.90/1.50  tff(c_436, plain, (![A_117]: (u1_struct_0(A_117)=k2_struct_0(A_117) | ~l1_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.50  tff(c_442, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_436])).
% 2.90/1.50  tff(c_446, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_411, c_442])).
% 2.90/1.50  tff(c_412, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.90/1.50  tff(c_439, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_436])).
% 2.90/1.50  tff(c_444, plain, (u1_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_412, c_439])).
% 2.90/1.50  tff(c_474, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_446, c_444, c_412, c_411, c_50])).
% 2.90/1.50  tff(c_452, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_54])).
% 2.90/1.50  tff(c_453, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_446, c_452])).
% 2.90/1.50  tff(c_491, plain, (![C_129, A_130, B_131]: (v1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.50  tff(c_495, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_453, c_491])).
% 2.90/1.50  tff(c_496, plain, (![C_132, A_133, B_134]: (v4_relat_1(C_132, A_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.90/1.50  tff(c_500, plain, (v4_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_453, c_496])).
% 2.90/1.50  tff(c_506, plain, (![B_138, A_139]: (r1_tarski(k1_relat_1(B_138), A_139) | ~v4_relat_1(B_138, A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.90/1.50  tff(c_16, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.50  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.90/1.50  tff(c_475, plain, (![A_125, B_126]: (k3_tarski(A_125)!=k1_xboole_0 | ~r2_hidden(B_126, A_125) | k1_xboole_0=B_126)), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.90/1.50  tff(c_478, plain, (![A_2, C_6]: (k3_tarski(k1_zfmisc_1(A_2))!=k1_xboole_0 | k1_xboole_0=C_6 | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_475])).
% 2.90/1.50  tff(c_483, plain, (![A_2, C_6]: (k1_xboole_0!=A_2 | k1_xboole_0=C_6 | ~r1_tarski(C_6, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_478])).
% 2.90/1.50  tff(c_518, plain, (![A_143, B_144]: (k1_xboole_0!=A_143 | k1_relat_1(B_144)=k1_xboole_0 | ~v4_relat_1(B_144, A_143) | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_506, c_483])).
% 2.90/1.50  tff(c_521, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_500, c_518])).
% 2.90/1.50  tff(c_524, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_495, c_521])).
% 2.90/1.50  tff(c_593, plain, (![A_150, B_151, C_152]: (k1_relset_1(A_150, B_151, C_152)=k1_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.50  tff(c_596, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_453, c_593])).
% 2.90/1.50  tff(c_598, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_524, c_596])).
% 2.90/1.50  tff(c_652, plain, (![A_166, B_167, C_168]: (k8_relset_1(A_166, B_167, C_168, B_167)=k1_relset_1(A_166, B_167, C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.90/1.50  tff(c_654, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_453, c_652])).
% 2.90/1.50  tff(c_656, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_598, c_654])).
% 2.90/1.50  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_656])).
% 2.90/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.50  
% 2.90/1.50  Inference rules
% 2.90/1.50  ----------------------
% 2.90/1.50  #Ref     : 0
% 2.90/1.50  #Sup     : 124
% 2.90/1.50  #Fact    : 0
% 2.90/1.50  #Define  : 0
% 2.90/1.50  #Split   : 3
% 2.90/1.50  #Chain   : 0
% 2.90/1.50  #Close   : 0
% 2.90/1.50  
% 2.90/1.50  Ordering : KBO
% 2.90/1.50  
% 2.90/1.50  Simplification rules
% 2.90/1.50  ----------------------
% 2.90/1.50  #Subsume      : 3
% 2.90/1.50  #Demod        : 63
% 2.90/1.50  #Tautology    : 58
% 2.90/1.50  #SimpNegUnit  : 5
% 2.90/1.50  #BackRed      : 11
% 2.90/1.50  
% 2.90/1.50  #Partial instantiations: 0
% 2.90/1.50  #Strategies tried      : 1
% 2.90/1.50  
% 2.90/1.50  Timing (in seconds)
% 2.90/1.50  ----------------------
% 2.90/1.50  Preprocessing        : 0.35
% 2.90/1.50  Parsing              : 0.19
% 2.90/1.50  CNF conversion       : 0.03
% 2.90/1.50  Main loop            : 0.33
% 2.90/1.50  Inferencing          : 0.13
% 2.90/1.50  Reduction            : 0.10
% 2.90/1.50  Demodulation         : 0.06
% 2.90/1.50  BG Simplification    : 0.02
% 2.90/1.50  Subsumption          : 0.05
% 2.90/1.50  Abstraction          : 0.02
% 2.90/1.50  MUC search           : 0.00
% 2.90/1.50  Cooper               : 0.00
% 2.90/1.50  Total                : 0.72
% 2.90/1.50  Index Insertion      : 0.00
% 2.90/1.50  Index Deletion       : 0.00
% 2.90/1.50  Index Matching       : 0.00
% 2.90/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
