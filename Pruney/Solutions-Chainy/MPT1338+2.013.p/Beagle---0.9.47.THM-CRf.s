%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:15 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  307 (16995 expanded)
%              Number of leaves         :   41 (5913 expanded)
%              Depth                    :   21
%              Number of atoms          :  544 (51278 expanded)
%              Number of equality atoms :  189 (17652 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(f_155,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_87,axiom,(
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

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_67,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_67])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_74,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_67])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_85,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_56])).

tff(c_101,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_101])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_587,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_591,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_587])).

tff(c_54,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_111,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_54])).

tff(c_593,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_111])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_87,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(u1_struct_0(A_34))
      | ~ l1_struct_0(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_93,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_87])).

tff(c_97,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_93])).

tff(c_98,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_97])).

tff(c_601,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_98])).

tff(c_123,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_85,c_123])).

tff(c_578,plain,(
    ! [B_103,A_104] :
      ( k1_relat_1(B_103) = A_104
      | ~ v1_partfun1(B_103,A_104)
      | ~ v4_relat_1(B_103,A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_581,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_578])).

tff(c_584,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_581])).

tff(c_585,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_584])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_58])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_76])).

tff(c_602,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_86])).

tff(c_603,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_85])).

tff(c_677,plain,(
    ! [C_124,A_125,B_126] :
      ( v1_partfun1(C_124,A_125)
      | ~ v1_funct_2(C_124,A_125,B_126)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | v1_xboole_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_680,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_603,c_677])).

tff(c_683,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_602,c_680])).

tff(c_685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_601,c_585,c_683])).

tff(c_686,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_584])).

tff(c_693,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_85])).

tff(c_743,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_747,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_693,c_743])).

tff(c_690,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_111])).

tff(c_749,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_690])).

tff(c_692,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_86])).

tff(c_755,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_692])).

tff(c_756,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_693])).

tff(c_754,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_747])).

tff(c_902,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_tops_2(A_156,B_157,C_158) = k2_funct_1(C_158)
      | ~ v2_funct_1(C_158)
      | k2_relset_1(A_156,B_157,C_158) != B_157
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_2(C_158,A_156,B_157)
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_908,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_756,c_902])).

tff(c_912,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_755,c_754,c_52,c_908])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28] :
      ( m1_subset_1(k2_tops_2(A_26,B_27,C_28),k1_zfmisc_1(k2_zfmisc_1(B_27,A_26)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_920,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_44])).

tff(c_924,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_755,c_756,c_920])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1017,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_924,c_16])).

tff(c_165,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_relset_1(A_51,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_165])).

tff(c_171,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_111])).

tff(c_178,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_98])).

tff(c_157,plain,(
    ! [B_49,A_50] :
      ( k1_relat_1(B_49) = A_50
      | ~ v1_partfun1(B_49,A_50)
      | ~ v4_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_160,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_157])).

tff(c_163,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_160])).

tff(c_164,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_179,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_86])).

tff(c_180,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_85])).

tff(c_224,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_partfun1(C_61,A_62)
      | ~ v1_funct_2(C_61,A_62,B_63)
      | ~ v1_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | v1_xboole_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_227,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_180,c_224])).

tff(c_230,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_179,c_227])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_164,c_230])).

tff(c_233,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_240,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_85])).

tff(c_286,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_16])).

tff(c_237,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_111])).

tff(c_293,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_237])).

tff(c_239,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_86])).

tff(c_300,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_239])).

tff(c_298,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_286])).

tff(c_299,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_240])).

tff(c_462,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_tops_2(A_96,B_97,C_98) = k2_funct_1(C_98)
      | ~ v2_funct_1(C_98)
      | k2_relset_1(A_96,B_97,C_98) != B_97
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_468,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_462])).

tff(c_472,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_300,c_298,c_52,c_468])).

tff(c_50,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_146,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_74,c_74,c_75,c_75,c_74,c_74,c_50])).

tff(c_147,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_235,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_233,c_147])).

tff(c_343,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_293,c_293,c_235])).

tff(c_476,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_343])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) = k1_xboole_0
      | k2_relat_1(A_1) != k1_xboole_0
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_110,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_116,plain,(
    ! [A_39] :
      ( k2_relat_1(A_39) = k1_xboole_0
      | k1_relat_1(A_39) != k1_xboole_0
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_116])).

tff(c_122,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_119])).

tff(c_381,plain,(
    ! [A_86,B_87,C_88] :
      ( v1_funct_2(k2_tops_2(A_86,B_87,C_88),B_87,A_86)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(C_88,A_86,B_87)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_383,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_381])).

tff(c_386,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_300,c_383])).

tff(c_474,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_386])).

tff(c_480,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_44])).

tff(c_484,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_300,c_299,c_480])).

tff(c_32,plain,(
    ! [B_17,A_16,C_18] :
      ( k1_xboole_0 = B_17
      | k1_relset_1(A_16,B_17,C_18) = A_16
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_528,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_484,c_32])).

tff(c_564,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_528])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_122,c_564])).

tff(c_567,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_688,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_686,c_686,c_567])).

tff(c_804,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_749,c_688])).

tff(c_915,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_804])).

tff(c_1050,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_915])).

tff(c_1057,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1050])).

tff(c_1061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_60,c_52,c_1057])).

tff(c_1063,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_1062,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_1094,plain,(
    ! [B_172] :
      ( v1_partfun1(B_172,k1_relat_1(B_172))
      | ~ v4_relat_1(B_172,k1_relat_1(B_172))
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1097,plain,
    ( v1_partfun1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_1094])).

tff(c_1099,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1062,c_1097])).

tff(c_1100,plain,(
    ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_1133,plain,(
    ! [A_178,B_179,C_180] :
      ( k2_relset_1(A_178,B_179,C_180) = k2_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1136,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_1133])).

tff(c_1138,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1136])).

tff(c_1064,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_75,c_54])).

tff(c_1139,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_1064])).

tff(c_1147,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_86])).

tff(c_1148,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_85])).

tff(c_24,plain,(
    ! [C_18,A_16] :
      ( k1_xboole_0 = C_18
      | ~ v1_funct_2(C_18,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1171,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1148,c_24])).

tff(c_1186,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1171])).

tff(c_1195,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1186])).

tff(c_1089,plain,(
    ! [C_169,A_170,B_171] :
      ( v4_relat_1(C_169,A_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1093,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_85,c_1089])).

tff(c_1200,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1093])).

tff(c_1204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1100,c_1200])).

tff(c_1205,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1186])).

tff(c_1146,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_98])).

tff(c_1215,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1146])).

tff(c_1115,plain,(
    ! [B_174,A_175] :
      ( k1_relat_1(B_174) = A_175
      | ~ v1_partfun1(B_174,A_175)
      | ~ v4_relat_1(B_174,A_175)
      | ~ v1_relat_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1118,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1093,c_1115])).

tff(c_1121,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1062,c_1118])).

tff(c_1122,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1121])).

tff(c_1212,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1147])).

tff(c_1209,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1148])).

tff(c_1338,plain,(
    ! [C_201,A_202,B_203] :
      ( v1_partfun1(C_201,A_202)
      | ~ v1_funct_2(C_201,A_202,B_203)
      | ~ v1_funct_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | v1_xboole_0(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1341,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1209,c_1338])).

tff(c_1344,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1212,c_1341])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1215,c_1122,c_1344])).

tff(c_1347,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1121])).

tff(c_1349,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_1093])).

tff(c_1356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1100,c_1349])).

tff(c_1357,plain,(
    v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_2118,plain,(
    ! [A_284,B_285,C_286] :
      ( k2_relset_1(A_284,B_285,C_286) = k2_relat_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2121,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_2118])).

tff(c_2123,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_2121])).

tff(c_2124,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_1064])).

tff(c_2133,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_86])).

tff(c_2134,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_85])).

tff(c_2153,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2134,c_24])).

tff(c_2168,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2133,c_2153])).

tff(c_2177,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2168])).

tff(c_2094,plain,(
    ! [B_280,A_281] :
      ( k1_relat_1(B_280) = A_281
      | ~ v1_partfun1(B_280,A_281)
      | ~ v4_relat_1(B_280,A_281)
      | ~ v1_relat_1(B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2100,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1093,c_2094])).

tff(c_2106,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1062,c_2100])).

tff(c_2107,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2106])).

tff(c_2180,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2177,c_2107])).

tff(c_2186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_2180])).

tff(c_2187,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2168])).

tff(c_2132,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_98])).

tff(c_2194,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2187,c_2132])).

tff(c_2190,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2187,c_2133])).

tff(c_2189,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2187,c_2134])).

tff(c_2304,plain,(
    ! [C_296,A_297,B_298] :
      ( v1_partfun1(C_296,A_297)
      | ~ v1_funct_2(C_296,A_297,B_298)
      | ~ v1_funct_1(C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | v1_xboole_0(B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2307,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2189,c_2304])).

tff(c_2310,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2190,c_2307])).

tff(c_2312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2194,c_2107,c_2310])).

tff(c_2313,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2106])).

tff(c_2319,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_85])).

tff(c_2364,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2367,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2319,c_2364])).

tff(c_2369,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_2367])).

tff(c_2316,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_1064])).

tff(c_2371,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2369,c_2316])).

tff(c_2318,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_86])).

tff(c_2378,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2318])).

tff(c_2376,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2369])).

tff(c_2377,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2319])).

tff(c_2640,plain,(
    ! [A_340,B_341,C_342] :
      ( k2_tops_2(A_340,B_341,C_342) = k2_funct_1(C_342)
      | ~ v2_funct_1(C_342)
      | k2_relset_1(A_340,B_341,C_342) != B_341
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341)))
      | ~ v1_funct_2(C_342,A_340,B_341)
      | ~ v1_funct_1(C_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2646,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2377,c_2640])).

tff(c_2650,plain,(
    k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2378,c_2376,c_52,c_2646])).

tff(c_1396,plain,(
    ! [A_208,B_209,C_210] :
      ( k2_relset_1(A_208,B_209,C_210) = k2_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1399,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_1396])).

tff(c_1401,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1399])).

tff(c_1402,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1064])).

tff(c_1410,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_86])).

tff(c_1411,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_85])).

tff(c_1452,plain,(
    ! [C_212,A_213] :
      ( k1_xboole_0 = C_212
      | ~ v1_funct_2(C_212,A_213,k1_xboole_0)
      | k1_xboole_0 = A_213
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_213,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1455,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1411,c_1452])).

tff(c_1458,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1455])).

tff(c_1459,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1458])).

tff(c_1373,plain,(
    ! [B_205,A_206] :
      ( k1_relat_1(B_205) = A_206
      | ~ v1_partfun1(B_205,A_206)
      | ~ v4_relat_1(B_205,A_206)
      | ~ v1_relat_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1379,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1093,c_1373])).

tff(c_1385,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1062,c_1379])).

tff(c_1386,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_1463,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1386])).

tff(c_1469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1463])).

tff(c_1470,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1458])).

tff(c_1409,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_98])).

tff(c_1479,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_1409])).

tff(c_1476,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_1410])).

tff(c_1474,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_1411])).

tff(c_1611,plain,(
    ! [C_232,A_233,B_234] :
      ( v1_partfun1(C_232,A_233)
      | ~ v1_funct_2(C_232,A_233,B_234)
      | ~ v1_funct_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | v1_xboole_0(B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1614,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1474,c_1611])).

tff(c_1617,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1476,c_1614])).

tff(c_1619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1479,c_1386,c_1617])).

tff(c_1620,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_1626,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_85])).

tff(c_1672,plain,(
    ! [A_237,B_238,C_239] :
      ( k2_relset_1(A_237,B_238,C_239) = k2_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1675,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1626,c_1672])).

tff(c_1677,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1675])).

tff(c_1623,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1064])).

tff(c_1678,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1677,c_1623])).

tff(c_1625,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_86])).

tff(c_1685,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1625])).

tff(c_1683,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1677])).

tff(c_1684,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1626])).

tff(c_1942,plain,(
    ! [A_276,B_277,C_278] :
      ( k2_tops_2(A_276,B_277,C_278) = k2_funct_1(C_278)
      | ~ v2_funct_1(C_278)
      | k2_relset_1(A_276,B_277,C_278) != B_277
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ v1_funct_2(C_278,A_276,B_277)
      | ~ v1_funct_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1948,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1684,c_1942])).

tff(c_1952,plain,(
    k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1685,c_1683,c_52,c_1948])).

tff(c_1359,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_75,c_75,c_74,c_74,c_75,c_75,c_50])).

tff(c_1360,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1359])).

tff(c_1727,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1678,c_1678,c_1620,c_1620,c_1360])).

tff(c_1957,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1727])).

tff(c_1785,plain,(
    ! [A_258,B_259,C_260] :
      ( v1_funct_2(k2_tops_2(A_258,B_259,C_260),B_259,A_258)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_260,A_258,B_259)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1787,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3'),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1684,c_1785])).

tff(c_1790,plain,(
    v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1685,c_1787])).

tff(c_1955,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1790])).

tff(c_1961,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1952,c_44])).

tff(c_1965,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1685,c_1684,c_1961])).

tff(c_30,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2034,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1965,c_30])).

tff(c_2077,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1955,c_2034])).

tff(c_2079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1957,c_2077])).

tff(c_2080,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1359])).

tff(c_2425,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2371,c_2313,c_2313,c_2313,c_2080])).

tff(c_2655,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_2425])).

tff(c_2578,plain,(
    ! [A_337,B_338,C_339] :
      ( k2_tops_2(A_337,B_338,C_339) = k2_funct_1(C_339)
      | ~ v2_funct_1(C_339)
      | k2_relset_1(A_337,B_338,C_339) != B_338
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338)))
      | ~ v1_funct_2(C_339,A_337,B_338)
      | ~ v1_funct_1(C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2584,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2377,c_2578])).

tff(c_2588,plain,(
    k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2378,c_2376,c_52,c_2584])).

tff(c_2488,plain,(
    ! [A_325,B_326,C_327] :
      ( m1_subset_1(k2_tops_2(A_325,B_326,C_327),k1_zfmisc_1(k2_zfmisc_1(B_326,A_325)))
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326)))
      | ~ v1_funct_2(C_327,A_325,B_326)
      | ~ v1_funct_1(C_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2539,plain,(
    ! [A_328,B_329,C_330] :
      ( v1_relat_1(k2_tops_2(A_328,B_329,C_330))
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329)))
      | ~ v1_funct_2(C_330,A_328,B_329)
      | ~ v1_funct_1(C_330) ) ),
    inference(resolution,[status(thm)],[c_2488,c_10])).

tff(c_2545,plain,
    ( v1_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2377,c_2539])).

tff(c_2549,plain,(
    v1_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2378,c_2545])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) = k1_xboole_0
      | k1_relat_1(A_1) != k1_xboole_0
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2556,plain,
    ( k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) = k1_xboole_0
    | k1_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2549,c_4])).

tff(c_2558,plain,(
    k1_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2556])).

tff(c_2557,plain,
    ( k1_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) = k1_xboole_0
    | k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2549,c_2])).

tff(c_2559,plain,(
    k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2558,c_2557])).

tff(c_2598,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2588,c_2559])).

tff(c_2630,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2598])).

tff(c_2633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_60,c_52,c_1062,c_2630])).

tff(c_2634,plain,(
    k2_relat_1(k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2556])).

tff(c_2651,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_2634])).

tff(c_2660,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2650,c_44])).

tff(c_2664,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2378,c_2377,c_2660])).

tff(c_2743,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2664,c_16])).

tff(c_2788,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2651,c_2743])).

tff(c_2790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2655,c_2788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.96  
% 4.94/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.94/1.96  
% 4.94/1.96  %Foreground sorts:
% 4.94/1.96  
% 4.94/1.96  
% 4.94/1.96  %Background operators:
% 4.94/1.96  
% 4.94/1.96  
% 4.94/1.96  %Foreground operators:
% 4.94/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.94/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.94/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.94/1.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.94/1.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.94/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.94/1.96  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.94/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.94/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.94/1.96  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.94/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.94/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.94/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.94/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.94/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.94/1.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.94/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.94/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.94/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.94/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.94/1.96  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.94/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.94/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.94/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.94/1.96  
% 5.14/2.00  tff(f_155, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 5.14/2.00  tff(f_99, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.14/2.00  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.14/2.00  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.14/2.00  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.14/2.00  tff(f_107, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.14/2.00  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.14/2.00  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.14/2.00  tff(f_69, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.14/2.00  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.14/2.00  tff(f_131, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 5.14/2.00  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 5.14/2.00  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.14/2.00  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_67, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.14/2.00  tff(c_75, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_67])).
% 5.14/2.00  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_74, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_67])).
% 5.14/2.00  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_85, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_56])).
% 5.14/2.00  tff(c_101, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.14/2.00  tff(c_105, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_101])).
% 5.14/2.00  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_6, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/2.00  tff(c_587, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_591, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_587])).
% 5.14/2.00  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_111, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_54])).
% 5.14/2.00  tff(c_593, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_111])).
% 5.14/2.00  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_87, plain, (![A_34]: (~v1_xboole_0(u1_struct_0(A_34)) | ~l1_struct_0(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.14/2.00  tff(c_93, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_74, c_87])).
% 5.14/2.00  tff(c_97, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_93])).
% 5.14/2.00  tff(c_98, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_97])).
% 5.14/2.00  tff(c_601, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_98])).
% 5.14/2.00  tff(c_123, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.14/2.00  tff(c_127, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_85, c_123])).
% 5.14/2.00  tff(c_578, plain, (![B_103, A_104]: (k1_relat_1(B_103)=A_104 | ~v1_partfun1(B_103, A_104) | ~v4_relat_1(B_103, A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/2.00  tff(c_581, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_127, c_578])).
% 5.14/2.00  tff(c_584, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_581])).
% 5.14/2.00  tff(c_585, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_584])).
% 5.14/2.00  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_76, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_58])).
% 5.14/2.00  tff(c_86, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_76])).
% 5.14/2.00  tff(c_602, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_86])).
% 5.14/2.00  tff(c_603, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_85])).
% 5.14/2.00  tff(c_677, plain, (![C_124, A_125, B_126]: (v1_partfun1(C_124, A_125) | ~v1_funct_2(C_124, A_125, B_126) | ~v1_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | v1_xboole_0(B_126))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.14/2.00  tff(c_680, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_603, c_677])).
% 5.14/2.00  tff(c_683, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_602, c_680])).
% 5.14/2.00  tff(c_685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_601, c_585, c_683])).
% 5.14/2.00  tff(c_686, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_584])).
% 5.14/2.00  tff(c_693, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_85])).
% 5.14/2.00  tff(c_743, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_747, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_693, c_743])).
% 5.14/2.00  tff(c_690, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_111])).
% 5.14/2.00  tff(c_749, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_747, c_690])).
% 5.14/2.00  tff(c_692, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_86])).
% 5.14/2.00  tff(c_755, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_749, c_692])).
% 5.14/2.00  tff(c_756, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_749, c_693])).
% 5.14/2.00  tff(c_754, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_747])).
% 5.14/2.00  tff(c_902, plain, (![A_156, B_157, C_158]: (k2_tops_2(A_156, B_157, C_158)=k2_funct_1(C_158) | ~v2_funct_1(C_158) | k2_relset_1(A_156, B_157, C_158)!=B_157 | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_2(C_158, A_156, B_157) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.14/2.00  tff(c_908, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_756, c_902])).
% 5.14/2.00  tff(c_912, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_755, c_754, c_52, c_908])).
% 5.14/2.00  tff(c_44, plain, (![A_26, B_27, C_28]: (m1_subset_1(k2_tops_2(A_26, B_27, C_28), k1_zfmisc_1(k2_zfmisc_1(B_27, A_26))) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.14/2.00  tff(c_920, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_912, c_44])).
% 5.14/2.00  tff(c_924, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_755, c_756, c_920])).
% 5.14/2.00  tff(c_16, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_1017, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_924, c_16])).
% 5.14/2.00  tff(c_165, plain, (![A_51, B_52, C_53]: (k2_relset_1(A_51, B_52, C_53)=k2_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_169, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_165])).
% 5.14/2.00  tff(c_171, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_111])).
% 5.14/2.00  tff(c_178, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_98])).
% 5.14/2.00  tff(c_157, plain, (![B_49, A_50]: (k1_relat_1(B_49)=A_50 | ~v1_partfun1(B_49, A_50) | ~v4_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/2.00  tff(c_160, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_127, c_157])).
% 5.14/2.00  tff(c_163, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_160])).
% 5.14/2.00  tff(c_164, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_163])).
% 5.14/2.00  tff(c_179, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_86])).
% 5.14/2.00  tff(c_180, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_85])).
% 5.14/2.00  tff(c_224, plain, (![C_61, A_62, B_63]: (v1_partfun1(C_61, A_62) | ~v1_funct_2(C_61, A_62, B_63) | ~v1_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | v1_xboole_0(B_63))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.14/2.00  tff(c_227, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_180, c_224])).
% 5.14/2.00  tff(c_230, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_179, c_227])).
% 5.14/2.00  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_164, c_230])).
% 5.14/2.00  tff(c_233, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_163])).
% 5.14/2.00  tff(c_240, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_85])).
% 5.14/2.00  tff(c_286, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_240, c_16])).
% 5.14/2.00  tff(c_237, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_111])).
% 5.14/2.00  tff(c_293, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_237])).
% 5.14/2.00  tff(c_239, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_86])).
% 5.14/2.00  tff(c_300, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_239])).
% 5.14/2.00  tff(c_298, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_286])).
% 5.14/2.00  tff(c_299, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_240])).
% 5.14/2.00  tff(c_462, plain, (![A_96, B_97, C_98]: (k2_tops_2(A_96, B_97, C_98)=k2_funct_1(C_98) | ~v2_funct_1(C_98) | k2_relset_1(A_96, B_97, C_98)!=B_97 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.14/2.00  tff(c_468, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_299, c_462])).
% 5.14/2.00  tff(c_472, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_300, c_298, c_52, c_468])).
% 5.14/2.00  tff(c_50, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.14/2.00  tff(c_146, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_74, c_74, c_75, c_75, c_74, c_74, c_50])).
% 5.14/2.00  tff(c_147, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_146])).
% 5.14/2.00  tff(c_235, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_233, c_147])).
% 5.14/2.00  tff(c_343, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_293, c_293, c_235])).
% 5.14/2.00  tff(c_476, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_472, c_343])).
% 5.14/2.00  tff(c_2, plain, (![A_1]: (k1_relat_1(A_1)=k1_xboole_0 | k2_relat_1(A_1)!=k1_xboole_0 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/2.00  tff(c_109, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_2])).
% 5.14/2.00  tff(c_110, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_109])).
% 5.14/2.00  tff(c_116, plain, (![A_39]: (k2_relat_1(A_39)=k1_xboole_0 | k1_relat_1(A_39)!=k1_xboole_0 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/2.00  tff(c_119, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_116])).
% 5.14/2.00  tff(c_122, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_110, c_119])).
% 5.14/2.00  tff(c_381, plain, (![A_86, B_87, C_88]: (v1_funct_2(k2_tops_2(A_86, B_87, C_88), B_87, A_86) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(C_88, A_86, B_87) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.14/2.00  tff(c_383, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_299, c_381])).
% 5.14/2.00  tff(c_386, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_300, c_383])).
% 5.14/2.00  tff(c_474, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_386])).
% 5.14/2.00  tff(c_480, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_472, c_44])).
% 5.14/2.00  tff(c_484, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_300, c_299, c_480])).
% 5.14/2.00  tff(c_32, plain, (![B_17, A_16, C_18]: (k1_xboole_0=B_17 | k1_relset_1(A_16, B_17, C_18)=A_16 | ~v1_funct_2(C_18, A_16, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.14/2.00  tff(c_528, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_484, c_32])).
% 5.14/2.00  tff(c_564, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_528])).
% 5.14/2.00  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_122, c_564])).
% 5.14/2.00  tff(c_567, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_146])).
% 5.14/2.00  tff(c_688, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_686, c_686, c_567])).
% 5.14/2.00  tff(c_804, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_749, c_688])).
% 5.14/2.00  tff(c_915, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_912, c_804])).
% 5.14/2.00  tff(c_1050, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_915])).
% 5.14/2.00  tff(c_1057, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_1050])).
% 5.14/2.00  tff(c_1061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_60, c_52, c_1057])).
% 5.14/2.00  tff(c_1063, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_109])).
% 5.14/2.00  tff(c_1062, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_109])).
% 5.14/2.00  tff(c_1094, plain, (![B_172]: (v1_partfun1(B_172, k1_relat_1(B_172)) | ~v4_relat_1(B_172, k1_relat_1(B_172)) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/2.00  tff(c_1097, plain, (v1_partfun1('#skF_3', k1_relat_1('#skF_3')) | ~v4_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_1094])).
% 5.14/2.00  tff(c_1099, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1062, c_1097])).
% 5.14/2.00  tff(c_1100, plain, (~v4_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1099])).
% 5.14/2.00  tff(c_1133, plain, (![A_178, B_179, C_180]: (k2_relset_1(A_178, B_179, C_180)=k2_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_1136, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_1133])).
% 5.14/2.00  tff(c_1138, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1136])).
% 5.14/2.00  tff(c_1064, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_75, c_54])).
% 5.14/2.00  tff(c_1139, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_1064])).
% 5.14/2.00  tff(c_1147, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_86])).
% 5.14/2.00  tff(c_1148, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_85])).
% 5.14/2.00  tff(c_24, plain, (![C_18, A_16]: (k1_xboole_0=C_18 | ~v1_funct_2(C_18, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.14/2.00  tff(c_1171, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1148, c_24])).
% 5.14/2.00  tff(c_1186, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1171])).
% 5.14/2.00  tff(c_1195, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1186])).
% 5.14/2.00  tff(c_1089, plain, (![C_169, A_170, B_171]: (v4_relat_1(C_169, A_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.14/2.00  tff(c_1093, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_85, c_1089])).
% 5.14/2.00  tff(c_1200, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1093])).
% 5.14/2.00  tff(c_1204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1100, c_1200])).
% 5.14/2.00  tff(c_1205, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1186])).
% 5.14/2.00  tff(c_1146, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_98])).
% 5.14/2.00  tff(c_1215, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1146])).
% 5.14/2.00  tff(c_1115, plain, (![B_174, A_175]: (k1_relat_1(B_174)=A_175 | ~v1_partfun1(B_174, A_175) | ~v4_relat_1(B_174, A_175) | ~v1_relat_1(B_174))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/2.00  tff(c_1118, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1093, c_1115])).
% 5.14/2.00  tff(c_1121, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1062, c_1118])).
% 5.14/2.00  tff(c_1122, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1121])).
% 5.14/2.00  tff(c_1212, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1147])).
% 5.14/2.00  tff(c_1209, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1148])).
% 5.14/2.00  tff(c_1338, plain, (![C_201, A_202, B_203]: (v1_partfun1(C_201, A_202) | ~v1_funct_2(C_201, A_202, B_203) | ~v1_funct_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | v1_xboole_0(B_203))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.14/2.00  tff(c_1341, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1209, c_1338])).
% 5.14/2.00  tff(c_1344, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1212, c_1341])).
% 5.14/2.00  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1215, c_1122, c_1344])).
% 5.14/2.00  tff(c_1347, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1121])).
% 5.14/2.00  tff(c_1349, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_1093])).
% 5.14/2.00  tff(c_1356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1100, c_1349])).
% 5.14/2.00  tff(c_1357, plain, (v1_partfun1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1099])).
% 5.14/2.00  tff(c_2118, plain, (![A_284, B_285, C_286]: (k2_relset_1(A_284, B_285, C_286)=k2_relat_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_2121, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_2118])).
% 5.14/2.00  tff(c_2123, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_2121])).
% 5.14/2.00  tff(c_2124, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2123, c_1064])).
% 5.14/2.00  tff(c_2133, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_86])).
% 5.14/2.00  tff(c_2134, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_85])).
% 5.14/2.00  tff(c_2153, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_2134, c_24])).
% 5.14/2.00  tff(c_2168, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2133, c_2153])).
% 5.14/2.00  tff(c_2177, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2168])).
% 5.14/2.00  tff(c_2094, plain, (![B_280, A_281]: (k1_relat_1(B_280)=A_281 | ~v1_partfun1(B_280, A_281) | ~v4_relat_1(B_280, A_281) | ~v1_relat_1(B_280))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/2.00  tff(c_2100, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1093, c_2094])).
% 5.14/2.00  tff(c_2106, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1062, c_2100])).
% 5.14/2.00  tff(c_2107, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2106])).
% 5.14/2.00  tff(c_2180, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2177, c_2107])).
% 5.14/2.00  tff(c_2186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1357, c_2180])).
% 5.14/2.00  tff(c_2187, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2168])).
% 5.14/2.00  tff(c_2132, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_98])).
% 5.14/2.00  tff(c_2194, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2187, c_2132])).
% 5.14/2.00  tff(c_2190, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2187, c_2133])).
% 5.14/2.00  tff(c_2189, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2187, c_2134])).
% 5.14/2.00  tff(c_2304, plain, (![C_296, A_297, B_298]: (v1_partfun1(C_296, A_297) | ~v1_funct_2(C_296, A_297, B_298) | ~v1_funct_1(C_296) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | v1_xboole_0(B_298))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.14/2.00  tff(c_2307, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_2189, c_2304])).
% 5.14/2.00  tff(c_2310, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2190, c_2307])).
% 5.14/2.00  tff(c_2312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2194, c_2107, c_2310])).
% 5.14/2.00  tff(c_2313, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2106])).
% 5.14/2.00  tff(c_2319, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_85])).
% 5.14/2.00  tff(c_2364, plain, (![A_300, B_301, C_302]: (k2_relset_1(A_300, B_301, C_302)=k2_relat_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_2367, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2319, c_2364])).
% 5.14/2.00  tff(c_2369, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_2367])).
% 5.14/2.00  tff(c_2316, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_1064])).
% 5.14/2.00  tff(c_2371, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2369, c_2316])).
% 5.14/2.00  tff(c_2318, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_86])).
% 5.14/2.00  tff(c_2378, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2371, c_2318])).
% 5.14/2.00  tff(c_2376, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2371, c_2369])).
% 5.14/2.00  tff(c_2377, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2371, c_2319])).
% 5.14/2.00  tff(c_2640, plain, (![A_340, B_341, C_342]: (k2_tops_2(A_340, B_341, C_342)=k2_funct_1(C_342) | ~v2_funct_1(C_342) | k2_relset_1(A_340, B_341, C_342)!=B_341 | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))) | ~v1_funct_2(C_342, A_340, B_341) | ~v1_funct_1(C_342))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.14/2.00  tff(c_2646, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2377, c_2640])).
% 5.14/2.00  tff(c_2650, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2378, c_2376, c_52, c_2646])).
% 5.14/2.00  tff(c_1396, plain, (![A_208, B_209, C_210]: (k2_relset_1(A_208, B_209, C_210)=k2_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_1399, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_1396])).
% 5.14/2.00  tff(c_1401, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1399])).
% 5.14/2.00  tff(c_1402, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1064])).
% 5.14/2.00  tff(c_1410, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_86])).
% 5.14/2.00  tff(c_1411, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_85])).
% 5.14/2.00  tff(c_1452, plain, (![C_212, A_213]: (k1_xboole_0=C_212 | ~v1_funct_2(C_212, A_213, k1_xboole_0) | k1_xboole_0=A_213 | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_213, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.14/2.00  tff(c_1455, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1411, c_1452])).
% 5.14/2.00  tff(c_1458, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1455])).
% 5.14/2.00  tff(c_1459, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1458])).
% 5.14/2.00  tff(c_1373, plain, (![B_205, A_206]: (k1_relat_1(B_205)=A_206 | ~v1_partfun1(B_205, A_206) | ~v4_relat_1(B_205, A_206) | ~v1_relat_1(B_205))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/2.00  tff(c_1379, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1093, c_1373])).
% 5.14/2.00  tff(c_1385, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1062, c_1379])).
% 5.14/2.00  tff(c_1386, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1385])).
% 5.14/2.00  tff(c_1463, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1386])).
% 5.14/2.00  tff(c_1469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1463])).
% 5.14/2.00  tff(c_1470, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1458])).
% 5.14/2.00  tff(c_1409, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_98])).
% 5.14/2.00  tff(c_1479, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_1409])).
% 5.14/2.00  tff(c_1476, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_1410])).
% 5.14/2.00  tff(c_1474, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_1411])).
% 5.14/2.00  tff(c_1611, plain, (![C_232, A_233, B_234]: (v1_partfun1(C_232, A_233) | ~v1_funct_2(C_232, A_233, B_234) | ~v1_funct_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | v1_xboole_0(B_234))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.14/2.00  tff(c_1614, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1474, c_1611])).
% 5.14/2.00  tff(c_1617, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1476, c_1614])).
% 5.14/2.00  tff(c_1619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1479, c_1386, c_1617])).
% 5.14/2.00  tff(c_1620, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1385])).
% 5.14/2.00  tff(c_1626, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_85])).
% 5.14/2.00  tff(c_1672, plain, (![A_237, B_238, C_239]: (k2_relset_1(A_237, B_238, C_239)=k2_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/2.00  tff(c_1675, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1626, c_1672])).
% 5.14/2.00  tff(c_1677, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1675])).
% 5.14/2.00  tff(c_1623, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1064])).
% 5.14/2.00  tff(c_1678, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1677, c_1623])).
% 5.14/2.00  tff(c_1625, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_86])).
% 5.14/2.00  tff(c_1685, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1625])).
% 5.14/2.00  tff(c_1683, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1677])).
% 5.14/2.00  tff(c_1684, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1626])).
% 5.14/2.00  tff(c_1942, plain, (![A_276, B_277, C_278]: (k2_tops_2(A_276, B_277, C_278)=k2_funct_1(C_278) | ~v2_funct_1(C_278) | k2_relset_1(A_276, B_277, C_278)!=B_277 | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~v1_funct_2(C_278, A_276, B_277) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.14/2.00  tff(c_1948, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1684, c_1942])).
% 5.14/2.00  tff(c_1952, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1685, c_1683, c_52, c_1948])).
% 5.14/2.00  tff(c_1359, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_75, c_75, c_74, c_74, c_75, c_75, c_50])).
% 5.14/2.00  tff(c_1360, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1359])).
% 5.14/2.00  tff(c_1727, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1678, c_1678, c_1620, c_1620, c_1360])).
% 5.14/2.00  tff(c_1957, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1727])).
% 5.14/2.00  tff(c_1785, plain, (![A_258, B_259, C_260]: (v1_funct_2(k2_tops_2(A_258, B_259, C_260), B_259, A_258) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(C_260, A_258, B_259) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.14/2.00  tff(c_1787, plain, (v1_funct_2(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'), k1_xboole_0, k1_xboole_0) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1684, c_1785])).
% 5.14/2.00  tff(c_1790, plain, (v1_funct_2(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1685, c_1787])).
% 5.14/2.00  tff(c_1955, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1790])).
% 5.14/2.00  tff(c_1961, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1952, c_44])).
% 5.14/2.00  tff(c_1965, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1685, c_1684, c_1961])).
% 5.14/2.00  tff(c_30, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.14/2.00  tff(c_2034, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1965, c_30])).
% 5.14/2.00  tff(c_2077, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1955, c_2034])).
% 5.14/2.00  tff(c_2079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1957, c_2077])).
% 5.14/2.00  tff(c_2080, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1359])).
% 5.14/2.00  tff(c_2425, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2371, c_2371, c_2313, c_2313, c_2313, c_2080])).
% 5.14/2.00  tff(c_2655, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_2425])).
% 5.14/2.00  tff(c_2578, plain, (![A_337, B_338, C_339]: (k2_tops_2(A_337, B_338, C_339)=k2_funct_1(C_339) | ~v2_funct_1(C_339) | k2_relset_1(A_337, B_338, C_339)!=B_338 | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))) | ~v1_funct_2(C_339, A_337, B_338) | ~v1_funct_1(C_339))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.14/2.00  tff(c_2584, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2377, c_2578])).
% 5.14/2.00  tff(c_2588, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2378, c_2376, c_52, c_2584])).
% 5.14/2.00  tff(c_2488, plain, (![A_325, B_326, C_327]: (m1_subset_1(k2_tops_2(A_325, B_326, C_327), k1_zfmisc_1(k2_zfmisc_1(B_326, A_325))) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))) | ~v1_funct_2(C_327, A_325, B_326) | ~v1_funct_1(C_327))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.14/2.00  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.14/2.00  tff(c_2539, plain, (![A_328, B_329, C_330]: (v1_relat_1(k2_tops_2(A_328, B_329, C_330)) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))) | ~v1_funct_2(C_330, A_328, B_329) | ~v1_funct_1(C_330))), inference(resolution, [status(thm)], [c_2488, c_10])).
% 5.14/2.00  tff(c_2545, plain, (v1_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2377, c_2539])).
% 5.14/2.00  tff(c_2549, plain, (v1_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2378, c_2545])).
% 5.14/2.00  tff(c_4, plain, (![A_1]: (k2_relat_1(A_1)=k1_xboole_0 | k1_relat_1(A_1)!=k1_xboole_0 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/2.00  tff(c_2556, plain, (k2_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))=k1_xboole_0 | k1_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2549, c_4])).
% 5.14/2.00  tff(c_2558, plain, (k1_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2556])).
% 5.14/2.00  tff(c_2557, plain, (k1_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))=k1_xboole_0 | k2_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2549, c_2])).
% 5.14/2.00  tff(c_2559, plain, (k2_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2558, c_2557])).
% 5.14/2.00  tff(c_2598, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2588, c_2559])).
% 5.14/2.00  tff(c_2630, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_2598])).
% 5.14/2.00  tff(c_2633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_60, c_52, c_1062, c_2630])).
% 5.14/2.00  tff(c_2634, plain, (k2_relat_1(k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2556])).
% 5.14/2.00  tff(c_2651, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_2634])).
% 5.14/2.00  tff(c_2660, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2650, c_44])).
% 5.14/2.00  tff(c_2664, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2378, c_2377, c_2660])).
% 5.14/2.00  tff(c_2743, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2664, c_16])).
% 5.14/2.00  tff(c_2788, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2651, c_2743])).
% 5.14/2.00  tff(c_2790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2655, c_2788])).
% 5.14/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.00  
% 5.14/2.00  Inference rules
% 5.14/2.00  ----------------------
% 5.14/2.00  #Ref     : 0
% 5.14/2.00  #Sup     : 568
% 5.14/2.00  #Fact    : 0
% 5.14/2.00  #Define  : 0
% 5.14/2.00  #Split   : 19
% 5.14/2.00  #Chain   : 0
% 5.14/2.00  #Close   : 0
% 5.14/2.00  
% 5.14/2.00  Ordering : KBO
% 5.14/2.00  
% 5.14/2.00  Simplification rules
% 5.14/2.00  ----------------------
% 5.14/2.00  #Subsume      : 36
% 5.14/2.00  #Demod        : 769
% 5.14/2.00  #Tautology    : 338
% 5.14/2.00  #SimpNegUnit  : 51
% 5.14/2.00  #BackRed      : 201
% 5.14/2.00  
% 5.14/2.00  #Partial instantiations: 0
% 5.14/2.00  #Strategies tried      : 1
% 5.14/2.00  
% 5.14/2.00  Timing (in seconds)
% 5.14/2.00  ----------------------
% 5.14/2.00  Preprocessing        : 0.38
% 5.14/2.00  Parsing              : 0.21
% 5.14/2.00  CNF conversion       : 0.02
% 5.14/2.00  Main loop            : 0.71
% 5.14/2.00  Inferencing          : 0.26
% 5.14/2.00  Reduction            : 0.24
% 5.14/2.00  Demodulation         : 0.17
% 5.14/2.01  BG Simplification    : 0.03
% 5.14/2.01  Subsumption          : 0.11
% 5.14/2.01  Abstraction          : 0.03
% 5.14/2.01  MUC search           : 0.00
% 5.14/2.01  Cooper               : 0.00
% 5.14/2.01  Total                : 1.18
% 5.14/2.01  Index Insertion      : 0.00
% 5.14/2.01  Index Deletion       : 0.00
% 5.14/2.01  Index Matching       : 0.00
% 5.14/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
