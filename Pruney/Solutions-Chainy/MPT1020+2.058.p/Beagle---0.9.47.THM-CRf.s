%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:59 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  174 (1072 expanded)
%              Number of leaves         :   41 ( 372 expanded)
%              Depth                    :   13
%              Number of atoms          :  304 (3070 expanded)
%              Number of equality atoms :   87 ( 495 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_161,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_95,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_45,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_116,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_116])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_122,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_128,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_122])).

tff(c_377,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_relset_1(A_94,B_95,D_96,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_382,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_377])).

tff(c_147,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_147])).

tff(c_170,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(B_56) = A_57
      | ~ v2_funct_2(B_56,A_57)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_173,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_170])).

tff(c_179,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_173])).

tff(c_183,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_62,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_285,plain,(
    ! [C_79,B_80,A_81] :
      ( v2_funct_2(C_79,B_80)
      | ~ v3_funct_2(C_79,A_81,B_80)
      | ~ v1_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_291,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_285])).

tff(c_297,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_291])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_297])).

tff(c_300,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_144,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_128,c_6])).

tff(c_157,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_302,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_157])).

tff(c_60,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_385,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_391,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_385])).

tff(c_395,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_391])).

tff(c_404,plain,(
    ! [C_100,A_101,B_102] :
      ( v2_funct_1(C_100)
      | ~ v3_funct_2(C_100,A_101,B_102)
      | ~ v1_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_410,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_404])).

tff(c_416,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_410])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_491,plain,(
    ! [C_126,D_127,B_128,A_129] :
      ( k2_funct_1(C_126) = D_127
      | k1_xboole_0 = B_128
      | k1_xboole_0 = A_129
      | ~ v2_funct_1(C_126)
      | ~ r2_relset_1(A_129,A_129,k1_partfun1(A_129,B_128,B_128,A_129,C_126,D_127),k6_partfun1(A_129))
      | k2_relset_1(A_129,B_128,C_126) != B_128
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(B_128,A_129)))
      | ~ v1_funct_2(D_127,B_128,A_129)
      | ~ v1_funct_1(D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128)))
      | ~ v1_funct_2(C_126,A_129,B_128)
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_494,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_491])).

tff(c_500,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_48,c_395,c_416,c_494])).

tff(c_501,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_500])).

tff(c_446,plain,(
    ! [A_110,B_111] :
      ( k2_funct_2(A_110,B_111) = k2_funct_1(B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v3_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_452,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_446])).

tff(c_458,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_452])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_464,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_44])).

tff(c_503,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_464])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_503])).

tff(c_508,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_509,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_522,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_509])).

tff(c_808,plain,(
    ! [B_169,A_170] :
      ( k2_relat_1(B_169) = A_170
      | ~ v2_funct_2(B_169,A_170)
      | ~ v5_relat_1(B_169,A_170)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_814,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_808])).

tff(c_823,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_522,c_814])).

tff(c_827,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_917,plain,(
    ! [C_186,B_187,A_188] :
      ( v2_funct_2(C_186,B_187)
      | ~ v3_funct_2(C_186,A_188,B_187)
      | ~ v1_funct_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_188,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_923,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_917])).

tff(c_929,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_923])).

tff(c_931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_827,c_929])).

tff(c_932,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_136,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_125,c_6])).

tff(c_146,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_511,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_146])).

tff(c_944,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_511])).

tff(c_50,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1020,plain,(
    ! [C_195,B_196,A_197] :
      ( v2_funct_2(C_195,B_196)
      | ~ v3_funct_2(C_195,A_197,B_196)
      | ~ v1_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1023,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1020])).

tff(c_1026,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1023])).

tff(c_154,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_147])).

tff(c_817,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_808])).

tff(c_826,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_817])).

tff(c_1075,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_826])).

tff(c_1076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_944,c_1075])).

tff(c_1077,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1078,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1612,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1078])).

tff(c_1079,plain,(
    ! [C_198,B_199,A_200] :
      ( v5_relat_1(C_198,B_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_200,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1086,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1079])).

tff(c_1805,plain,(
    ! [B_298,A_299] :
      ( k2_relat_1(B_298) = A_299
      | ~ v2_funct_2(B_298,A_299)
      | ~ v5_relat_1(B_298,A_299)
      | ~ v1_relat_1(B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1811,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_1805])).

tff(c_1817,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_1612,c_1811])).

tff(c_1818,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1817])).

tff(c_1836,plain,(
    ! [C_306,B_307,A_308] :
      ( v2_funct_2(C_306,B_307)
      | ~ v3_funct_2(C_306,A_308,B_307)
      | ~ v1_funct_1(C_306)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_308,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1839,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1836])).

tff(c_1842,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1839])).

tff(c_1844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1818,c_1842])).

tff(c_1845,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_1801,plain,(
    ! [A_295,B_296,D_297] :
      ( r2_relset_1(A_295,B_296,D_297,D_297)
      | ~ m1_subset_1(D_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1804,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1801])).

tff(c_1847,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1845,c_1804])).

tff(c_1869,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_54])).

tff(c_1867,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_52])).

tff(c_1868,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_50])).

tff(c_69,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_36,plain,(
    ! [A_25] : k6_relat_1(A_25) = k6_partfun1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_7] : k2_funct_1(k6_relat_1(A_7)) = k6_relat_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    ! [A_40] : k2_funct_1(k6_partfun1(A_40)) = k6_partfun1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_12])).

tff(c_98,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_89])).

tff(c_101,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_98])).

tff(c_1091,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1077,c_101])).

tff(c_1857,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1845,c_1091])).

tff(c_1866,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_48])).

tff(c_2006,plain,(
    ! [A_328,B_329] :
      ( k2_funct_2(A_328,B_329) = k2_funct_1(B_329)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(k2_zfmisc_1(A_328,A_328)))
      | ~ v3_funct_2(B_329,A_328,A_328)
      | ~ v1_funct_2(B_329,A_328,A_328)
      | ~ v1_funct_1(B_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2009,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1866,c_2006])).

tff(c_2012,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1869,c_1867,c_1868,c_1857,c_2009])).

tff(c_1100,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1078])).

tff(c_1325,plain,(
    ! [B_228,A_229] :
      ( k2_relat_1(B_228) = A_229
      | ~ v2_funct_2(B_228,A_229)
      | ~ v5_relat_1(B_228,A_229)
      | ~ v1_relat_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1331,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_1325])).

tff(c_1337,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_1100,c_1331])).

tff(c_1344,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1337])).

tff(c_1401,plain,(
    ! [C_244,B_245,A_246] :
      ( v2_funct_2(C_244,B_245)
      | ~ v3_funct_2(C_244,A_246,B_245)
      | ~ v1_funct_1(C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_246,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1404,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1401])).

tff(c_1410,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1404])).

tff(c_1412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1344,c_1410])).

tff(c_1413,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1337])).

tff(c_1098,plain,
    ( k2_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1077,c_144])).

tff(c_1099,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1098])).

tff(c_1419,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1413,c_1099])).

tff(c_1087,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1079])).

tff(c_1328,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1087,c_1325])).

tff(c_1334,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1328])).

tff(c_1527,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1419,c_1334])).

tff(c_1577,plain,(
    ! [C_262,B_263,A_264] :
      ( v2_funct_2(C_262,B_263)
      | ~ v3_funct_2(C_262,A_264,B_263)
      | ~ v1_funct_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_264,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1583,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1577])).

tff(c_1589,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1583])).

tff(c_1591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1527,c_1589])).

tff(c_1592,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1098])).

tff(c_1597,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_44])).

tff(c_1859,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1845,c_1597])).

tff(c_2013,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_1859])).

tff(c_2016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_2013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:31:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.82  
% 4.76/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.82  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.76/1.82  
% 4.76/1.82  %Foreground sorts:
% 4.76/1.82  
% 4.76/1.82  
% 4.76/1.82  %Background operators:
% 4.76/1.82  
% 4.76/1.82  
% 4.76/1.82  %Foreground operators:
% 4.76/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.76/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.76/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.76/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.76/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.76/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.82  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.76/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.76/1.82  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.76/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.76/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.76/1.82  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.76/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.76/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.82  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.76/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.76/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.76/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.76/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.76/1.82  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.76/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.76/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.82  
% 4.81/1.84  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.81/1.84  tff(f_161, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 4.81/1.84  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.81/1.84  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.81/1.84  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.81/1.84  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.81/1.84  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.81/1.84  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.81/1.84  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.81/1.84  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.81/1.84  tff(f_93, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.81/1.84  tff(f_95, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.81/1.84  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.81/1.84  tff(f_45, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 4.81/1.84  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.81/1.84  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_116, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.84  tff(c_119, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_116])).
% 4.81/1.84  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_119])).
% 4.81/1.84  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_122, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_116])).
% 4.81/1.84  tff(c_128, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_122])).
% 4.81/1.84  tff(c_377, plain, (![A_94, B_95, D_96]: (r2_relset_1(A_94, B_95, D_96, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.81/1.84  tff(c_382, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_377])).
% 4.81/1.84  tff(c_147, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.81/1.84  tff(c_155, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_147])).
% 4.81/1.84  tff(c_170, plain, (![B_56, A_57]: (k2_relat_1(B_56)=A_57 | ~v2_funct_2(B_56, A_57) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.81/1.84  tff(c_173, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_155, c_170])).
% 4.81/1.84  tff(c_179, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_173])).
% 4.81/1.84  tff(c_183, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_179])).
% 4.81/1.84  tff(c_62, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_58, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_285, plain, (![C_79, B_80, A_81]: (v2_funct_2(C_79, B_80) | ~v3_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.84  tff(c_291, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_285])).
% 4.81/1.84  tff(c_297, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_291])).
% 4.81/1.84  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_297])).
% 4.81/1.84  tff(c_300, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_179])).
% 4.81/1.84  tff(c_6, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.81/1.84  tff(c_144, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_128, c_6])).
% 4.81/1.84  tff(c_157, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_144])).
% 4.81/1.84  tff(c_302, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_300, c_157])).
% 4.81/1.84  tff(c_60, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_385, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.81/1.84  tff(c_391, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_385])).
% 4.81/1.84  tff(c_395, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_300, c_391])).
% 4.81/1.84  tff(c_404, plain, (![C_100, A_101, B_102]: (v2_funct_1(C_100) | ~v3_funct_2(C_100, A_101, B_102) | ~v1_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.84  tff(c_410, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_404])).
% 4.81/1.84  tff(c_416, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_410])).
% 4.81/1.84  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_491, plain, (![C_126, D_127, B_128, A_129]: (k2_funct_1(C_126)=D_127 | k1_xboole_0=B_128 | k1_xboole_0=A_129 | ~v2_funct_1(C_126) | ~r2_relset_1(A_129, A_129, k1_partfun1(A_129, B_128, B_128, A_129, C_126, D_127), k6_partfun1(A_129)) | k2_relset_1(A_129, B_128, C_126)!=B_128 | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(B_128, A_129))) | ~v1_funct_2(D_127, B_128, A_129) | ~v1_funct_1(D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))) | ~v1_funct_2(C_126, A_129, B_128) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.81/1.84  tff(c_494, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_491])).
% 4.81/1.84  tff(c_500, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_48, c_395, c_416, c_494])).
% 4.81/1.84  tff(c_501, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_302, c_500])).
% 4.81/1.84  tff(c_446, plain, (![A_110, B_111]: (k2_funct_2(A_110, B_111)=k2_funct_1(B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v3_funct_2(B_111, A_110, A_110) | ~v1_funct_2(B_111, A_110, A_110) | ~v1_funct_1(B_111))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.81/1.84  tff(c_452, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_446])).
% 4.81/1.84  tff(c_458, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_452])).
% 4.81/1.84  tff(c_44, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_464, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_44])).
% 4.81/1.84  tff(c_503, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_501, c_464])).
% 4.81/1.84  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_382, c_503])).
% 4.81/1.84  tff(c_508, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_144])).
% 4.81/1.84  tff(c_509, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_144])).
% 4.81/1.84  tff(c_522, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_508, c_509])).
% 4.81/1.84  tff(c_808, plain, (![B_169, A_170]: (k2_relat_1(B_169)=A_170 | ~v2_funct_2(B_169, A_170) | ~v5_relat_1(B_169, A_170) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.81/1.84  tff(c_814, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_155, c_808])).
% 4.81/1.84  tff(c_823, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_522, c_814])).
% 4.81/1.84  tff(c_827, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_823])).
% 4.81/1.84  tff(c_917, plain, (![C_186, B_187, A_188]: (v2_funct_2(C_186, B_187) | ~v3_funct_2(C_186, A_188, B_187) | ~v1_funct_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_188, B_187))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.84  tff(c_923, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_917])).
% 4.81/1.84  tff(c_929, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_923])).
% 4.81/1.84  tff(c_931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_827, c_929])).
% 4.81/1.84  tff(c_932, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_823])).
% 4.81/1.84  tff(c_136, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_125, c_6])).
% 4.81/1.84  tff(c_146, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_136])).
% 4.81/1.84  tff(c_511, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_508, c_146])).
% 4.81/1.84  tff(c_944, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_932, c_511])).
% 4.81/1.84  tff(c_50, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.81/1.84  tff(c_1020, plain, (![C_195, B_196, A_197]: (v2_funct_2(C_195, B_196) | ~v3_funct_2(C_195, A_197, B_196) | ~v1_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.84  tff(c_1023, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1020])).
% 4.81/1.84  tff(c_1026, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1023])).
% 4.81/1.84  tff(c_154, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_147])).
% 4.81/1.84  tff(c_817, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_154, c_808])).
% 4.81/1.84  tff(c_826, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_817])).
% 4.81/1.84  tff(c_1075, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_826])).
% 4.81/1.84  tff(c_1076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_944, c_1075])).
% 4.81/1.84  tff(c_1077, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_136])).
% 4.81/1.84  tff(c_1078, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_136])).
% 4.81/1.84  tff(c_1612, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1078])).
% 4.81/1.84  tff(c_1079, plain, (![C_198, B_199, A_200]: (v5_relat_1(C_198, B_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_200, B_199))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.81/1.84  tff(c_1086, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1079])).
% 4.81/1.84  tff(c_1805, plain, (![B_298, A_299]: (k2_relat_1(B_298)=A_299 | ~v2_funct_2(B_298, A_299) | ~v5_relat_1(B_298, A_299) | ~v1_relat_1(B_298))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.81/1.84  tff(c_1811, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1086, c_1805])).
% 4.81/1.84  tff(c_1817, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_1612, c_1811])).
% 4.81/1.84  tff(c_1818, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1817])).
% 4.81/1.84  tff(c_1836, plain, (![C_306, B_307, A_308]: (v2_funct_2(C_306, B_307) | ~v3_funct_2(C_306, A_308, B_307) | ~v1_funct_1(C_306) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_308, B_307))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.84  tff(c_1839, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1836])).
% 4.81/1.84  tff(c_1842, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1839])).
% 4.81/1.84  tff(c_1844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1818, c_1842])).
% 4.81/1.84  tff(c_1845, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1817])).
% 4.81/1.84  tff(c_1801, plain, (![A_295, B_296, D_297]: (r2_relset_1(A_295, B_296, D_297, D_297) | ~m1_subset_1(D_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.81/1.84  tff(c_1804, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_1801])).
% 4.81/1.84  tff(c_1847, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1845, c_1804])).
% 4.81/1.84  tff(c_1869, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_54])).
% 4.81/1.84  tff(c_1867, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_52])).
% 4.81/1.84  tff(c_1868, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_50])).
% 4.81/1.84  tff(c_69, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.81/1.84  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.81/1.84  tff(c_75, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_69, c_10])).
% 4.81/1.84  tff(c_36, plain, (![A_25]: (k6_relat_1(A_25)=k6_partfun1(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.81/1.84  tff(c_12, plain, (![A_7]: (k2_funct_1(k6_relat_1(A_7))=k6_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.81/1.84  tff(c_89, plain, (![A_40]: (k2_funct_1(k6_partfun1(A_40))=k6_partfun1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_12])).
% 4.81/1.84  tff(c_98, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_89])).
% 4.81/1.84  tff(c_101, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_75, c_98])).
% 4.81/1.84  tff(c_1091, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1077, c_101])).
% 4.81/1.84  tff(c_1857, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1845, c_1091])).
% 4.81/1.84  tff(c_1866, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_48])).
% 4.81/1.84  tff(c_2006, plain, (![A_328, B_329]: (k2_funct_2(A_328, B_329)=k2_funct_1(B_329) | ~m1_subset_1(B_329, k1_zfmisc_1(k2_zfmisc_1(A_328, A_328))) | ~v3_funct_2(B_329, A_328, A_328) | ~v1_funct_2(B_329, A_328, A_328) | ~v1_funct_1(B_329))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.81/1.84  tff(c_2009, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1866, c_2006])).
% 4.81/1.84  tff(c_2012, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1869, c_1867, c_1868, c_1857, c_2009])).
% 4.81/1.84  tff(c_1100, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1078])).
% 4.81/1.84  tff(c_1325, plain, (![B_228, A_229]: (k2_relat_1(B_228)=A_229 | ~v2_funct_2(B_228, A_229) | ~v5_relat_1(B_228, A_229) | ~v1_relat_1(B_228))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.81/1.84  tff(c_1331, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1086, c_1325])).
% 4.81/1.84  tff(c_1337, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_1100, c_1331])).
% 4.81/1.84  tff(c_1344, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1337])).
% 4.81/1.84  tff(c_1401, plain, (![C_244, B_245, A_246]: (v2_funct_2(C_244, B_245) | ~v3_funct_2(C_244, A_246, B_245) | ~v1_funct_1(C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_246, B_245))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.84  tff(c_1404, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1401])).
% 4.81/1.84  tff(c_1410, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1404])).
% 4.81/1.84  tff(c_1412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1344, c_1410])).
% 4.81/1.84  tff(c_1413, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1337])).
% 4.81/1.84  tff(c_1098, plain, (k2_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1077, c_144])).
% 4.81/1.84  tff(c_1099, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1098])).
% 4.81/1.84  tff(c_1419, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1413, c_1099])).
% 4.81/1.84  tff(c_1087, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_1079])).
% 4.81/1.84  tff(c_1328, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1087, c_1325])).
% 4.81/1.84  tff(c_1334, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1328])).
% 4.81/1.84  tff(c_1527, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1419, c_1334])).
% 4.81/1.84  tff(c_1577, plain, (![C_262, B_263, A_264]: (v2_funct_2(C_262, B_263) | ~v3_funct_2(C_262, A_264, B_263) | ~v1_funct_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_264, B_263))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.84  tff(c_1583, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1577])).
% 4.81/1.84  tff(c_1589, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1583])).
% 4.81/1.84  tff(c_1591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1527, c_1589])).
% 4.81/1.84  tff(c_1592, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1098])).
% 4.81/1.84  tff(c_1597, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_44])).
% 4.81/1.84  tff(c_1859, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1845, c_1597])).
% 4.81/1.84  tff(c_2013, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_1859])).
% 4.81/1.84  tff(c_2016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1847, c_2013])).
% 4.81/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.84  
% 4.81/1.84  Inference rules
% 4.81/1.84  ----------------------
% 4.81/1.84  #Ref     : 0
% 4.81/1.84  #Sup     : 422
% 4.81/1.84  #Fact    : 0
% 4.81/1.84  #Define  : 0
% 4.81/1.84  #Split   : 23
% 4.81/1.84  #Chain   : 0
% 4.81/1.84  #Close   : 0
% 4.81/1.84  
% 4.81/1.84  Ordering : KBO
% 4.81/1.84  
% 4.81/1.84  Simplification rules
% 4.81/1.84  ----------------------
% 4.81/1.84  #Subsume      : 32
% 4.81/1.84  #Demod        : 611
% 4.81/1.84  #Tautology    : 272
% 4.81/1.84  #SimpNegUnit  : 15
% 4.81/1.84  #BackRed      : 164
% 4.81/1.84  
% 4.81/1.85  #Partial instantiations: 0
% 4.81/1.85  #Strategies tried      : 1
% 4.81/1.85  
% 4.81/1.85  Timing (in seconds)
% 4.81/1.85  ----------------------
% 4.81/1.85  Preprocessing        : 0.37
% 4.81/1.85  Parsing              : 0.19
% 4.81/1.85  CNF conversion       : 0.03
% 4.81/1.85  Main loop            : 0.70
% 4.81/1.85  Inferencing          : 0.25
% 4.81/1.85  Reduction            : 0.24
% 4.81/1.85  Demodulation         : 0.17
% 4.81/1.85  BG Simplification    : 0.03
% 4.81/1.85  Subsumption          : 0.09
% 4.81/1.85  Abstraction          : 0.03
% 4.81/1.85  MUC search           : 0.00
% 4.81/1.85  Cooper               : 0.00
% 4.81/1.85  Total                : 1.12
% 4.81/1.85  Index Insertion      : 0.00
% 4.81/1.85  Index Deletion       : 0.00
% 4.81/1.85  Index Matching       : 0.00
% 4.81/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
