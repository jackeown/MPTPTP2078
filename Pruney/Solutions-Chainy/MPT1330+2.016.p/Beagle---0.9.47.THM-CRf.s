%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:11 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 775 expanded)
%              Number of leaves         :   39 ( 270 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 (2050 expanded)
%              Number of equality atoms :   54 ( 797 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_85,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_40,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_53,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_54,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_54])).

tff(c_48,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_61,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_54])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_63,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_42])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_63])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( v1_relat_1(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_93,c_10])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_128,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_93,c_128])).

tff(c_176,plain,(
    ! [B_67,A_68] :
      ( k1_relat_1(B_67) = A_68
      | ~ v1_partfun1(B_67,A_68)
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_179,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_176])).

tff(c_182,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_179])).

tff(c_183,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44])).

tff(c_73,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64])).

tff(c_264,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_partfun1(C_97,A_98)
      | ~ v1_funct_2(C_97,A_98,B_99)
      | ~ v1_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | v1_xboole_0(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_267,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_93,c_264])).

tff(c_274,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_267])).

tff(c_275,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_274])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_279,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_279])).

tff(c_284,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_38,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_92,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_61,c_38])).

tff(c_290,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_284,c_92])).

tff(c_289,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_93])).

tff(c_360,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_368,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_360])).

tff(c_399,plain,(
    ! [A_116,B_117,C_118] :
      ( k8_relset_1(A_116,B_117,C_118,B_117) = k1_relset_1(A_116,B_117,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_401,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_399])).

tff(c_406,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_401])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_406])).

tff(c_409,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_419,plain,(
    ! [A_119] :
      ( u1_struct_0(A_119) = k2_struct_0(A_119)
      | ~ l1_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_425,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_419])).

tff(c_429,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_425])).

tff(c_410,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_422,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_419])).

tff(c_427,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_422])).

tff(c_472,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_427,c_410,c_409,c_38])).

tff(c_439,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_427,c_42])).

tff(c_460,plain,(
    ! [B_126,A_127] :
      ( v1_relat_1(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_127))
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_466,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_439,c_460])).

tff(c_470,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_466])).

tff(c_520,plain,(
    ! [C_142,A_143,B_144] :
      ( v4_relat_1(C_142,A_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_529,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_439,c_520])).

tff(c_485,plain,(
    ! [B_132,A_133] :
      ( r1_tarski(k1_relat_1(B_132),A_133)
      | ~ v4_relat_1(B_132,A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_451,plain,(
    ! [B_124,A_125] :
      ( v1_xboole_0(B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_125))
      | ~ v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_458,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(A_5)
      | ~ v1_xboole_0(B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_451])).

tff(c_542,plain,(
    ! [B_149,A_150] :
      ( v1_xboole_0(k1_relat_1(B_149))
      | ~ v1_xboole_0(A_150)
      | ~ v4_relat_1(B_149,A_150)
      | ~ v1_relat_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_485,c_458])).

tff(c_544,plain,
    ( v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_529,c_542])).

tff(c_547,plain,
    ( v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_544])).

tff(c_548,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_555,plain,(
    ! [B_153,A_154] :
      ( k1_relat_1(B_153) = A_154
      | ~ v1_partfun1(B_153,A_154)
      | ~ v4_relat_1(B_153,A_154)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_558,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_529,c_555])).

tff(c_561,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_558])).

tff(c_563,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_430,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_44])).

tff(c_440,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_430])).

tff(c_636,plain,(
    ! [C_182,A_183,B_184] :
      ( v1_partfun1(C_182,A_183)
      | ~ v1_funct_2(C_182,A_183,B_184)
      | ~ v1_funct_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | v1_xboole_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_643,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_439,c_636])).

tff(c_647,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_440,c_643])).

tff(c_649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_563,c_647])).

tff(c_650,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_671,plain,(
    ! [A_185,B_186,C_187] :
      ( k1_relset_1(A_185,B_186,C_187) = k1_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_678,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_439,c_671])).

tff(c_681,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_678])).

tff(c_750,plain,(
    ! [A_193,B_194,C_195] :
      ( k8_relset_1(A_193,B_194,C_195,B_194) = k1_relset_1(A_193,B_194,C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_755,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_439,c_750])).

tff(c_758,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_755])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_758])).

tff(c_761,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_771,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_761,c_2])).

tff(c_849,plain,(
    ! [A_202,B_203,C_204] :
      ( k1_relset_1(A_202,B_203,C_204) = k1_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_856,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_439,c_849])).

tff(c_859,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_856])).

tff(c_918,plain,(
    ! [A_221,B_222,C_223] :
      ( k8_relset_1(A_221,B_222,C_223,B_222) = k1_relset_1(A_221,B_222,C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_923,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_439,c_918])).

tff(c_926,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_923])).

tff(c_928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.83/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.83/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.83/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.44  
% 3.19/1.46  tff(f_116, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.19/1.46  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.19/1.46  tff(f_97, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.19/1.46  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.19/1.46  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.19/1.46  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.19/1.46  tff(f_85, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.19/1.46  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.19/1.46  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.19/1.46  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.19/1.46  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.19/1.46  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.19/1.46  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.19/1.46  tff(c_40, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.19/1.46  tff(c_53, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.19/1.46  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.46  tff(c_50, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.19/1.46  tff(c_54, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.19/1.46  tff(c_62, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_54])).
% 3.19/1.46  tff(c_48, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.19/1.46  tff(c_61, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_54])).
% 3.19/1.46  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.19/1.46  tff(c_63, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_42])).
% 3.19/1.46  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_63])).
% 3.19/1.46  tff(c_10, plain, (![B_9, A_7]: (v1_relat_1(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.46  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_93, c_10])).
% 3.19/1.46  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_99])).
% 3.19/1.46  tff(c_128, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.46  tff(c_136, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_93, c_128])).
% 3.19/1.46  tff(c_176, plain, (![B_67, A_68]: (k1_relat_1(B_67)=A_68 | ~v1_partfun1(B_67, A_68) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.46  tff(c_179, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_176])).
% 3.19/1.46  tff(c_182, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_179])).
% 3.19/1.46  tff(c_183, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_182])).
% 3.19/1.46  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.19/1.46  tff(c_44, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.19/1.46  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_44])).
% 3.19/1.46  tff(c_73, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64])).
% 3.19/1.46  tff(c_264, plain, (![C_97, A_98, B_99]: (v1_partfun1(C_97, A_98) | ~v1_funct_2(C_97, A_98, B_99) | ~v1_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | v1_xboole_0(B_99))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.19/1.46  tff(c_267, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_93, c_264])).
% 3.19/1.46  tff(c_274, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_267])).
% 3.19/1.46  tff(c_275, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_183, c_274])).
% 3.19/1.46  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.46  tff(c_279, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_275, c_2])).
% 3.19/1.46  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_279])).
% 3.19/1.46  tff(c_284, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_182])).
% 3.19/1.46  tff(c_38, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.19/1.46  tff(c_92, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_61, c_38])).
% 3.19/1.46  tff(c_290, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_284, c_92])).
% 3.19/1.46  tff(c_289, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_93])).
% 3.19/1.46  tff(c_360, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.46  tff(c_368, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_360])).
% 3.19/1.46  tff(c_399, plain, (![A_116, B_117, C_118]: (k8_relset_1(A_116, B_117, C_118, B_117)=k1_relset_1(A_116, B_117, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.46  tff(c_401, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_289, c_399])).
% 3.19/1.46  tff(c_406, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_401])).
% 3.19/1.46  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_406])).
% 3.19/1.46  tff(c_409, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.19/1.46  tff(c_419, plain, (![A_119]: (u1_struct_0(A_119)=k2_struct_0(A_119) | ~l1_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.19/1.46  tff(c_425, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_419])).
% 3.19/1.46  tff(c_429, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_409, c_425])).
% 3.19/1.46  tff(c_410, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.19/1.46  tff(c_422, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_419])).
% 3.19/1.46  tff(c_427, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_410, c_422])).
% 3.19/1.46  tff(c_472, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_429, c_427, c_410, c_409, c_38])).
% 3.19/1.46  tff(c_439, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_427, c_42])).
% 3.19/1.46  tff(c_460, plain, (![B_126, A_127]: (v1_relat_1(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_127)) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.46  tff(c_466, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_439, c_460])).
% 3.19/1.46  tff(c_470, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_466])).
% 3.19/1.46  tff(c_520, plain, (![C_142, A_143, B_144]: (v4_relat_1(C_142, A_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.46  tff(c_529, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_439, c_520])).
% 3.19/1.46  tff(c_485, plain, (![B_132, A_133]: (r1_tarski(k1_relat_1(B_132), A_133) | ~v4_relat_1(B_132, A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.19/1.46  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.19/1.46  tff(c_451, plain, (![B_124, A_125]: (v1_xboole_0(B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_125)) | ~v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.19/1.46  tff(c_458, plain, (![A_5, B_6]: (v1_xboole_0(A_5) | ~v1_xboole_0(B_6) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_451])).
% 3.19/1.46  tff(c_542, plain, (![B_149, A_150]: (v1_xboole_0(k1_relat_1(B_149)) | ~v1_xboole_0(A_150) | ~v4_relat_1(B_149, A_150) | ~v1_relat_1(B_149))), inference(resolution, [status(thm)], [c_485, c_458])).
% 3.19/1.46  tff(c_544, plain, (v1_xboole_0(k1_relat_1('#skF_3')) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_529, c_542])).
% 3.19/1.46  tff(c_547, plain, (v1_xboole_0(k1_relat_1('#skF_3')) | ~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_470, c_544])).
% 3.19/1.46  tff(c_548, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_547])).
% 3.19/1.46  tff(c_555, plain, (![B_153, A_154]: (k1_relat_1(B_153)=A_154 | ~v1_partfun1(B_153, A_154) | ~v4_relat_1(B_153, A_154) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.46  tff(c_558, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_529, c_555])).
% 3.19/1.46  tff(c_561, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_470, c_558])).
% 3.19/1.46  tff(c_563, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_561])).
% 3.19/1.46  tff(c_430, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_427, c_44])).
% 3.19/1.46  tff(c_440, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_429, c_430])).
% 3.19/1.46  tff(c_636, plain, (![C_182, A_183, B_184]: (v1_partfun1(C_182, A_183) | ~v1_funct_2(C_182, A_183, B_184) | ~v1_funct_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | v1_xboole_0(B_184))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.19/1.46  tff(c_643, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_439, c_636])).
% 3.19/1.46  tff(c_647, plain, (v1_partfun1('#skF_3', k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_440, c_643])).
% 3.19/1.46  tff(c_649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_548, c_563, c_647])).
% 3.19/1.46  tff(c_650, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_561])).
% 3.19/1.46  tff(c_671, plain, (![A_185, B_186, C_187]: (k1_relset_1(A_185, B_186, C_187)=k1_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.46  tff(c_678, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_439, c_671])).
% 3.19/1.46  tff(c_681, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_650, c_678])).
% 3.19/1.46  tff(c_750, plain, (![A_193, B_194, C_195]: (k8_relset_1(A_193, B_194, C_195, B_194)=k1_relset_1(A_193, B_194, C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.46  tff(c_755, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_439, c_750])).
% 3.19/1.46  tff(c_758, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_681, c_755])).
% 3.19/1.46  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_758])).
% 3.19/1.46  tff(c_761, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_547])).
% 3.19/1.46  tff(c_771, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_761, c_2])).
% 3.19/1.46  tff(c_849, plain, (![A_202, B_203, C_204]: (k1_relset_1(A_202, B_203, C_204)=k1_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.46  tff(c_856, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_439, c_849])).
% 3.19/1.46  tff(c_859, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_771, c_856])).
% 3.19/1.46  tff(c_918, plain, (![A_221, B_222, C_223]: (k8_relset_1(A_221, B_222, C_223, B_222)=k1_relset_1(A_221, B_222, C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.46  tff(c_923, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_439, c_918])).
% 3.19/1.46  tff(c_926, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_859, c_923])).
% 3.19/1.46  tff(c_928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_926])).
% 3.19/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.46  
% 3.19/1.46  Inference rules
% 3.19/1.46  ----------------------
% 3.19/1.46  #Ref     : 0
% 3.19/1.46  #Sup     : 180
% 3.19/1.46  #Fact    : 0
% 3.19/1.46  #Define  : 0
% 3.19/1.46  #Split   : 9
% 3.19/1.46  #Chain   : 0
% 3.19/1.46  #Close   : 0
% 3.19/1.46  
% 3.19/1.46  Ordering : KBO
% 3.19/1.46  
% 3.19/1.46  Simplification rules
% 3.19/1.46  ----------------------
% 3.19/1.46  #Subsume      : 11
% 3.19/1.46  #Demod        : 128
% 3.19/1.46  #Tautology    : 82
% 3.19/1.46  #SimpNegUnit  : 10
% 3.19/1.46  #BackRed      : 13
% 3.19/1.46  
% 3.19/1.46  #Partial instantiations: 0
% 3.19/1.46  #Strategies tried      : 1
% 3.19/1.46  
% 3.19/1.46  Timing (in seconds)
% 3.19/1.46  ----------------------
% 3.19/1.46  Preprocessing        : 0.33
% 3.19/1.46  Parsing              : 0.17
% 3.19/1.46  CNF conversion       : 0.02
% 3.19/1.46  Main loop            : 0.37
% 3.19/1.46  Inferencing          : 0.14
% 3.19/1.46  Reduction            : 0.12
% 3.19/1.47  Demodulation         : 0.08
% 3.19/1.47  BG Simplification    : 0.02
% 3.19/1.47  Subsumption          : 0.05
% 3.19/1.47  Abstraction          : 0.02
% 3.19/1.47  MUC search           : 0.00
% 3.19/1.47  Cooper               : 0.00
% 3.19/1.47  Total                : 0.74
% 3.19/1.47  Index Insertion      : 0.00
% 3.19/1.47  Index Deletion       : 0.00
% 3.19/1.47  Index Matching       : 0.00
% 3.19/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
