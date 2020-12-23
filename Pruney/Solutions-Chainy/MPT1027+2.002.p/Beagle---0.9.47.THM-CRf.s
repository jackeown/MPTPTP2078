%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:42 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 252 expanded)
%              Number of leaves         :   35 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 533 expanded)
%              Number of equality atoms :   34 ( 110 expanded)
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

tff(f_143,negated_conjecture,(
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

tff(f_128,axiom,(
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

tff(f_130,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_93,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_289,plain,(
    ! [C_73,B_74,A_75] :
      ( v1_xboole_0(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(B_74,A_75)))
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_307,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_289])).

tff(c_312,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60])).

tff(c_62,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_791,plain,(
    ! [B_126,C_127,A_128] :
      ( k1_xboole_0 = B_126
      | v1_funct_2(C_127,A_128,B_126)
      | k1_relset_1(A_128,B_126,C_127) != A_128
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_797,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_791])).

tff(c_812,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_797])).

tff(c_813,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_812])).

tff(c_14,plain,(
    ! [A_5] : v1_xboole_0('#skF_1'(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [A_5] : '#skF_1'(A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_859,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_90])).

tff(c_863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_859])).

tff(c_864,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_58,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_38])).

tff(c_1044,plain,(
    ! [A_143] :
      ( v1_xboole_0(k6_partfun1(A_143))
      | ~ v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_69,c_289])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_869,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_864,c_2])).

tff(c_890,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_2])).

tff(c_1087,plain,(
    ! [A_146] :
      ( k6_partfun1(A_146) = '#skF_4'
      | ~ v1_xboole_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_1044,c_890])).

tff(c_1095,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_864,c_1087])).

tff(c_1160,plain,(
    ! [C_152,A_153,B_154] :
      ( v1_partfun1(C_152,A_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_xboole_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1179,plain,(
    ! [A_156] :
      ( v1_partfun1(k6_partfun1(A_156),A_156)
      | ~ v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_69,c_1160])).

tff(c_1182,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_1179])).

tff(c_1184,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_1182])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_142,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_16])).

tff(c_883,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_142])).

tff(c_1334,plain,(
    ! [C_175,A_176,B_177] :
      ( v1_funct_2(C_175,A_176,B_177)
      | ~ v1_partfun1(C_175,A_176)
      | ~ v1_funct_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1338,plain,(
    ! [A_176,B_177] :
      ( v1_funct_2('#skF_4',A_176,B_177)
      | ~ v1_partfun1('#skF_4',A_176)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_883,c_1334])).

tff(c_1353,plain,(
    ! [A_178,B_179] :
      ( v1_funct_2('#skF_4',A_178,B_179)
      | ~ v1_partfun1('#skF_4',A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1338])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_35,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_74,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_1062,plain,(
    ! [A_145] :
      ( v1_funct_2('#skF_4',A_145,'#skF_4')
      | A_145 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_869,c_869,c_869,c_869,c_869,c_74])).

tff(c_865,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_873,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_865,c_2])).

tff(c_898,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_873])).

tff(c_903,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_68])).

tff(c_1066,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1062,c_903])).

tff(c_1067,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_903])).

tff(c_1362,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1353,c_1067])).

tff(c_1373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.53  
% 3.20/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.20/1.53  
% 3.20/1.53  %Foreground sorts:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Background operators:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Foreground operators:
% 3.20/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.20/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.20/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.53  
% 3.39/1.55  tff(f_143, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 3.39/1.55  tff(f_87, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.39/1.55  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.39/1.55  tff(f_52, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 3.39/1.55  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.39/1.55  tff(f_130, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.39/1.55  tff(f_93, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.39/1.55  tff(f_110, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.39/1.55  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.39/1.55  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.39/1.55  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.39/1.55  tff(c_289, plain, (![C_73, B_74, A_75]: (v1_xboole_0(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(B_74, A_75))) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.55  tff(c_307, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_289])).
% 3.39/1.55  tff(c_312, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_307])).
% 3.39/1.55  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.39/1.55  tff(c_60, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.39/1.55  tff(c_68, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60])).
% 3.39/1.55  tff(c_62, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.39/1.55  tff(c_791, plain, (![B_126, C_127, A_128]: (k1_xboole_0=B_126 | v1_funct_2(C_127, A_128, B_126) | k1_relset_1(A_128, B_126, C_127)!=A_128 | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_126))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.39/1.55  tff(c_797, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_64, c_791])).
% 3.39/1.55  tff(c_812, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_797])).
% 3.39/1.55  tff(c_813, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_68, c_812])).
% 3.39/1.55  tff(c_14, plain, (![A_5]: (v1_xboole_0('#skF_1'(A_5)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.55  tff(c_76, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.55  tff(c_80, plain, (![A_5]: ('#skF_1'(A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_76])).
% 3.39/1.55  tff(c_90, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_14])).
% 3.39/1.55  tff(c_859, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_813, c_90])).
% 3.39/1.55  tff(c_863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_859])).
% 3.39/1.55  tff(c_864, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_307])).
% 3.39/1.55  tff(c_58, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.39/1.55  tff(c_38, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.39/1.55  tff(c_69, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_38])).
% 3.39/1.55  tff(c_1044, plain, (![A_143]: (v1_xboole_0(k6_partfun1(A_143)) | ~v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_69, c_289])).
% 3.39/1.55  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.55  tff(c_869, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_864, c_2])).
% 3.39/1.55  tff(c_890, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_869, c_2])).
% 3.39/1.55  tff(c_1087, plain, (![A_146]: (k6_partfun1(A_146)='#skF_4' | ~v1_xboole_0(A_146))), inference(resolution, [status(thm)], [c_1044, c_890])).
% 3.39/1.55  tff(c_1095, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_864, c_1087])).
% 3.39/1.55  tff(c_1160, plain, (![C_152, A_153, B_154]: (v1_partfun1(C_152, A_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_xboole_0(A_153))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.39/1.55  tff(c_1179, plain, (![A_156]: (v1_partfun1(k6_partfun1(A_156), A_156) | ~v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_69, c_1160])).
% 3.39/1.55  tff(c_1182, plain, (v1_partfun1('#skF_4', '#skF_4') | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1095, c_1179])).
% 3.39/1.55  tff(c_1184, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_864, c_1182])).
% 3.39/1.55  tff(c_16, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.55  tff(c_142, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_16])).
% 3.39/1.55  tff(c_883, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_869, c_142])).
% 3.39/1.55  tff(c_1334, plain, (![C_175, A_176, B_177]: (v1_funct_2(C_175, A_176, B_177) | ~v1_partfun1(C_175, A_176) | ~v1_funct_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.39/1.55  tff(c_1338, plain, (![A_176, B_177]: (v1_funct_2('#skF_4', A_176, B_177) | ~v1_partfun1('#skF_4', A_176) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_883, c_1334])).
% 3.39/1.55  tff(c_1353, plain, (![A_178, B_179]: (v1_funct_2('#skF_4', A_178, B_179) | ~v1_partfun1('#skF_4', A_178))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1338])).
% 3.39/1.55  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.55  tff(c_46, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_35, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.39/1.55  tff(c_74, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_46])).
% 3.39/1.55  tff(c_1062, plain, (![A_145]: (v1_funct_2('#skF_4', A_145, '#skF_4') | A_145='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_869, c_869, c_869, c_869, c_869, c_74])).
% 3.39/1.55  tff(c_865, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_307])).
% 3.39/1.55  tff(c_873, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_865, c_2])).
% 3.39/1.55  tff(c_898, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_869, c_873])).
% 3.39/1.55  tff(c_903, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_898, c_68])).
% 3.39/1.55  tff(c_1066, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_1062, c_903])).
% 3.39/1.55  tff(c_1067, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_903])).
% 3.39/1.55  tff(c_1362, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1353, c_1067])).
% 3.39/1.55  tff(c_1373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1362])).
% 3.39/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.55  
% 3.39/1.55  Inference rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Ref     : 0
% 3.39/1.55  #Sup     : 271
% 3.39/1.55  #Fact    : 0
% 3.39/1.55  #Define  : 0
% 3.39/1.55  #Split   : 4
% 3.39/1.55  #Chain   : 0
% 3.39/1.55  #Close   : 0
% 3.39/1.55  
% 3.39/1.55  Ordering : KBO
% 3.39/1.55  
% 3.39/1.55  Simplification rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Subsume      : 24
% 3.39/1.55  #Demod        : 314
% 3.39/1.55  #Tautology    : 182
% 3.39/1.55  #SimpNegUnit  : 3
% 3.39/1.55  #BackRed      : 76
% 3.39/1.55  
% 3.39/1.55  #Partial instantiations: 0
% 3.39/1.55  #Strategies tried      : 1
% 3.39/1.55  
% 3.39/1.55  Timing (in seconds)
% 3.39/1.55  ----------------------
% 3.39/1.55  Preprocessing        : 0.33
% 3.39/1.55  Parsing              : 0.17
% 3.39/1.55  CNF conversion       : 0.02
% 3.39/1.55  Main loop            : 0.43
% 3.39/1.55  Inferencing          : 0.15
% 3.39/1.55  Reduction            : 0.15
% 3.39/1.55  Demodulation         : 0.11
% 3.39/1.55  BG Simplification    : 0.02
% 3.39/1.55  Subsumption          : 0.07
% 3.39/1.55  Abstraction          : 0.02
% 3.39/1.55  MUC search           : 0.00
% 3.39/1.55  Cooper               : 0.00
% 3.39/1.55  Total                : 0.79
% 3.39/1.55  Index Insertion      : 0.00
% 3.39/1.55  Index Deletion       : 0.00
% 3.39/1.55  Index Matching       : 0.00
% 3.39/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
