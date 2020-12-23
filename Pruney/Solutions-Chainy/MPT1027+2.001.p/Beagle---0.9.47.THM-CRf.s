%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:42 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 299 expanded)
%              Number of leaves         :   33 ( 114 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 662 expanded)
%              Number of equality atoms :   33 ( 142 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_52,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_130,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_398,plain,(
    ! [C_87,B_88,A_89] :
      ( v1_xboole_0(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(B_88,A_89)))
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_416,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_398])).

tff(c_421,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_70,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62])).

tff(c_64,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_811,plain,(
    ! [B_131,C_132,A_133] :
      ( k1_xboole_0 = B_131
      | v1_funct_2(C_132,A_133,B_131)
      | k1_relset_1(A_133,B_131,C_132) != A_133
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_817,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_811])).

tff(c_832,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_817])).

tff(c_833,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_832])).

tff(c_14,plain,(
    ! [A_5] : v1_xboole_0('#skF_1'(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_5] : '#skF_1'(A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_91,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_14])).

tff(c_878,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_91])).

tff(c_883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_878])).

tff(c_884,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_889,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_884,c_2])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_144,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_16])).

tff(c_910,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_144])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_75,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_946,plain,(
    ! [A_34] :
      ( v1_funct_2('#skF_4',A_34,'#skF_4')
      | A_34 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_889,c_889,c_889,c_889,c_75])).

tff(c_947,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_946])).

tff(c_1092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_947])).

tff(c_1382,plain,(
    ! [A_174] :
      ( v1_funct_2('#skF_4',A_174,'#skF_4')
      | A_174 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_885,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_893,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_885,c_2])).

tff(c_925,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_893])).

tff(c_931,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_70])).

tff(c_1392,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1382,c_931])).

tff(c_1393,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_931])).

tff(c_58,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1249,plain,(
    ! [A_159] :
      ( v1_xboole_0(k6_partfun1(A_159))
      | ~ v1_xboole_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_58,c_398])).

tff(c_917,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_2])).

tff(c_1276,plain,(
    ! [A_164] :
      ( k6_partfun1(A_164) = '#skF_4'
      | ~ v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_1249,c_917])).

tff(c_1284,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_884,c_1276])).

tff(c_56,plain,(
    ! [A_37] : v1_partfun1(k6_partfun1(A_37),A_37) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1362,plain,(
    ! [C_171,A_172,B_173] :
      ( v1_funct_2(C_171,A_172,B_173)
      | ~ v1_partfun1(C_171,A_172)
      | ~ v1_funct_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1375,plain,(
    ! [A_37] :
      ( v1_funct_2(k6_partfun1(A_37),A_37,A_37)
      | ~ v1_partfun1(k6_partfun1(A_37),A_37)
      | ~ v1_funct_1(k6_partfun1(A_37)) ) ),
    inference(resolution,[status(thm)],[c_58,c_1362])).

tff(c_1574,plain,(
    ! [A_196] :
      ( v1_funct_2(k6_partfun1(A_196),A_196,A_196)
      | ~ v1_funct_1(k6_partfun1(A_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1375])).

tff(c_1586,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_1574])).

tff(c_1595,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1284,c_1586])).

tff(c_1597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1393,c_1595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:32:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.56  
% 3.62/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.62/1.56  
% 3.62/1.56  %Foreground sorts:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Background operators:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Foreground operators:
% 3.62/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.62/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.62/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.62/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.62/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.62/1.56  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.62/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.62/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.62/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.56  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.62/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.56  
% 3.62/1.58  tff(f_145, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 3.62/1.58  tff(f_87, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.62/1.58  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.62/1.58  tff(f_52, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 3.62/1.58  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.62/1.58  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.62/1.58  tff(f_130, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.62/1.58  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.62/1.58  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.62/1.58  tff(c_398, plain, (![C_87, B_88, A_89]: (v1_xboole_0(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(B_88, A_89))) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.62/1.58  tff(c_416, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_398])).
% 3.62/1.58  tff(c_421, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_416])).
% 3.62/1.58  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.62/1.58  tff(c_62, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.62/1.58  tff(c_70, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62])).
% 3.62/1.58  tff(c_64, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.62/1.58  tff(c_811, plain, (![B_131, C_132, A_133]: (k1_xboole_0=B_131 | v1_funct_2(C_132, A_133, B_131) | k1_relset_1(A_133, B_131, C_132)!=A_133 | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_131))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.62/1.58  tff(c_817, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_66, c_811])).
% 3.62/1.58  tff(c_832, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_817])).
% 3.62/1.58  tff(c_833, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_70, c_832])).
% 3.62/1.58  tff(c_14, plain, (![A_5]: (v1_xboole_0('#skF_1'(A_5)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.58  tff(c_77, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.58  tff(c_81, plain, (![A_5]: ('#skF_1'(A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_77])).
% 3.62/1.58  tff(c_91, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_14])).
% 3.62/1.58  tff(c_878, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_91])).
% 3.62/1.58  tff(c_883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_878])).
% 3.62/1.58  tff(c_884, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_416])).
% 3.62/1.58  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.58  tff(c_889, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_884, c_2])).
% 3.62/1.58  tff(c_16, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.58  tff(c_144, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_16])).
% 3.62/1.58  tff(c_910, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_144])).
% 3.62/1.58  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.62/1.58  tff(c_44, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.62/1.58  tff(c_75, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_44])).
% 3.62/1.58  tff(c_946, plain, (![A_34]: (v1_funct_2('#skF_4', A_34, '#skF_4') | A_34='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_889, c_889, c_889, c_889, c_75])).
% 3.62/1.58  tff(c_947, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_946])).
% 3.62/1.58  tff(c_1092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_910, c_947])).
% 3.62/1.58  tff(c_1382, plain, (![A_174]: (v1_funct_2('#skF_4', A_174, '#skF_4') | A_174='#skF_4')), inference(splitRight, [status(thm)], [c_946])).
% 3.62/1.58  tff(c_885, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_416])).
% 3.62/1.58  tff(c_893, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_885, c_2])).
% 3.62/1.58  tff(c_925, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_889, c_893])).
% 3.62/1.58  tff(c_931, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_925, c_70])).
% 3.62/1.58  tff(c_1392, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_1382, c_931])).
% 3.62/1.58  tff(c_1393, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1392, c_931])).
% 3.62/1.58  tff(c_58, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.58  tff(c_1249, plain, (![A_159]: (v1_xboole_0(k6_partfun1(A_159)) | ~v1_xboole_0(A_159))), inference(resolution, [status(thm)], [c_58, c_398])).
% 3.62/1.58  tff(c_917, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_2])).
% 3.62/1.58  tff(c_1276, plain, (![A_164]: (k6_partfun1(A_164)='#skF_4' | ~v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_1249, c_917])).
% 3.62/1.58  tff(c_1284, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_884, c_1276])).
% 3.62/1.58  tff(c_56, plain, (![A_37]: (v1_partfun1(k6_partfun1(A_37), A_37))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.58  tff(c_1362, plain, (![C_171, A_172, B_173]: (v1_funct_2(C_171, A_172, B_173) | ~v1_partfun1(C_171, A_172) | ~v1_funct_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.62/1.58  tff(c_1375, plain, (![A_37]: (v1_funct_2(k6_partfun1(A_37), A_37, A_37) | ~v1_partfun1(k6_partfun1(A_37), A_37) | ~v1_funct_1(k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_58, c_1362])).
% 3.62/1.58  tff(c_1574, plain, (![A_196]: (v1_funct_2(k6_partfun1(A_196), A_196, A_196) | ~v1_funct_1(k6_partfun1(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1375])).
% 3.62/1.58  tff(c_1586, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1284, c_1574])).
% 3.62/1.58  tff(c_1595, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1284, c_1586])).
% 3.62/1.58  tff(c_1597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1393, c_1595])).
% 3.62/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.58  
% 3.62/1.58  Inference rules
% 3.62/1.58  ----------------------
% 3.62/1.58  #Ref     : 0
% 3.62/1.58  #Sup     : 320
% 3.62/1.58  #Fact    : 0
% 3.62/1.58  #Define  : 0
% 3.62/1.58  #Split   : 6
% 3.62/1.58  #Chain   : 0
% 3.62/1.58  #Close   : 0
% 3.62/1.58  
% 3.62/1.58  Ordering : KBO
% 3.62/1.58  
% 3.62/1.58  Simplification rules
% 3.62/1.58  ----------------------
% 3.62/1.58  #Subsume      : 21
% 3.62/1.58  #Demod        : 351
% 3.62/1.58  #Tautology    : 210
% 3.62/1.58  #SimpNegUnit  : 4
% 3.62/1.58  #BackRed      : 88
% 3.62/1.58  
% 3.62/1.58  #Partial instantiations: 0
% 3.62/1.58  #Strategies tried      : 1
% 3.62/1.58  
% 3.62/1.58  Timing (in seconds)
% 3.62/1.58  ----------------------
% 3.62/1.58  Preprocessing        : 0.34
% 3.62/1.58  Parsing              : 0.17
% 3.62/1.58  CNF conversion       : 0.02
% 3.62/1.58  Main loop            : 0.47
% 3.62/1.58  Inferencing          : 0.16
% 3.62/1.58  Reduction            : 0.17
% 3.62/1.58  Demodulation         : 0.12
% 3.62/1.58  BG Simplification    : 0.02
% 3.62/1.58  Subsumption          : 0.07
% 3.62/1.58  Abstraction          : 0.02
% 3.62/1.58  MUC search           : 0.00
% 3.62/1.58  Cooper               : 0.00
% 3.62/1.58  Total                : 0.84
% 3.62/1.58  Index Insertion      : 0.00
% 3.62/1.58  Index Deletion       : 0.00
% 3.62/1.58  Index Matching       : 0.00
% 3.62/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
