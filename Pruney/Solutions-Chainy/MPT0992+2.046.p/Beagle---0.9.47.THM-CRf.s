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
% DateTime   : Thu Dec  3 10:13:38 EST 2020

% Result     : Theorem 13.66s
% Output     : CNFRefutation 13.93s
% Verified   : 
% Statistics : Number of formulae       :  191 (2127 expanded)
%              Number of leaves         :   35 ( 675 expanded)
%              Depth                    :   15
%              Number of atoms          :  345 (7021 expanded)
%              Number of equality atoms :   90 (2711 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_92,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_92])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_24986,plain,(
    ! [A_1082,B_1083,C_1084] :
      ( k1_relset_1(A_1082,B_1083,C_1084) = k1_relat_1(C_1084)
      | ~ m1_subset_1(C_1084,k1_zfmisc_1(k2_zfmisc_1(A_1082,B_1083))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_25000,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_24986])).

tff(c_25232,plain,(
    ! [B_1123,A_1124,C_1125] :
      ( k1_xboole_0 = B_1123
      | k1_relset_1(A_1124,B_1123,C_1125) = A_1124
      | ~ v1_funct_2(C_1125,A_1124,B_1123)
      | ~ m1_subset_1(C_1125,k1_zfmisc_1(k2_zfmisc_1(A_1124,B_1123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_25241,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_25232])).

tff(c_25254,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_25000,c_25241])).

tff(c_25255,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_25254])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( k1_relat_1(k7_relat_1(B_11,A_10)) = A_10
      | ~ r1_tarski(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25271,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25255,c_18])).

tff(c_25293,plain,(
    ! [A_1127] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1127)) = A_1127
      | ~ r1_tarski(A_1127,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_25271])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_25086,plain,(
    ! [A_1113,B_1114,C_1115,D_1116] :
      ( k2_partfun1(A_1113,B_1114,C_1115,D_1116) = k7_relat_1(C_1115,D_1116)
      | ~ m1_subset_1(C_1115,k1_zfmisc_1(k2_zfmisc_1(A_1113,B_1114)))
      | ~ v1_funct_1(C_1115) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_25092,plain,(
    ! [D_1116] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1116) = k7_relat_1('#skF_4',D_1116)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_25086])).

tff(c_25103,plain,(
    ! [D_1116] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1116) = k7_relat_1('#skF_4',D_1116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25092])).

tff(c_324,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k2_partfun1(A_123,B_124,C_125,D_126) = k7_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_funct_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_328,plain,(
    ! [D_126] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_126) = k7_relat_1('#skF_4',D_126)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_324])).

tff(c_336,plain,(
    ! [D_126] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_126) = k7_relat_1('#skF_4',D_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_328])).

tff(c_490,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( m1_subset_1(k2_partfun1(A_142,B_143,C_144,D_145),k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_515,plain,(
    ! [D_126] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_126),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_490])).

tff(c_534,plain,(
    ! [D_146] : m1_subset_1(k7_relat_1('#skF_4',D_146),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_515])).

tff(c_20,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_574,plain,(
    ! [D_146] : v1_relat_1(k7_relat_1('#skF_4',D_146)) ),
    inference(resolution,[status(thm)],[c_534,c_20])).

tff(c_22,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_573,plain,(
    ! [D_146] : v5_relat_1(k7_relat_1('#skF_4',D_146),'#skF_2') ),
    inference(resolution,[status(thm)],[c_534,c_22])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_286,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( v1_funct_1(k2_partfun1(A_110,B_111,C_112,D_113))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_288,plain,(
    ! [D_113] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_113))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_286])).

tff(c_295,plain,(
    ! [D_113] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_288])).

tff(c_337,plain,(
    ! [D_113] : v1_funct_1(k7_relat_1('#skF_4',D_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_295])).

tff(c_262,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_272,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_262])).

tff(c_408,plain,(
    ! [B_136,A_137,C_138] :
      ( k1_xboole_0 = B_136
      | k1_relset_1(A_137,B_136,C_138) = A_137
      | ~ v1_funct_2(C_138,A_137,B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_414,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_408])).

tff(c_424,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_272,c_414])).

tff(c_425,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_424])).

tff(c_437,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_18])).

tff(c_464,plain,(
    ! [A_141] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_141)) = A_141
      | ~ r1_tarski(A_141,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_437])).

tff(c_46,plain,(
    ! [B_33,A_32] :
      ( m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33),A_32)))
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_470,plain,(
    ! [A_141,A_32] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_141),k1_zfmisc_1(k2_zfmisc_1(A_141,A_32)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_141)),A_32)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_141))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_141))
      | ~ r1_tarski(A_141,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_46])).

tff(c_485,plain,(
    ! [A_141,A_32] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_141),k1_zfmisc_1(k2_zfmisc_1(A_141,A_32)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_141)),A_32)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_141))
      | ~ r1_tarski(A_141,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_470])).

tff(c_24850,plain,(
    ! [A_1074,A_1075] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_1074),k1_zfmisc_1(k2_zfmisc_1(A_1074,A_1075)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_1074)),A_1075)
      | ~ r1_tarski(A_1074,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_485])).

tff(c_198,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( v1_funct_1(k2_partfun1(A_77,B_78,C_79,D_80))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_200,plain,(
    ! [D_80] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_80))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_198])).

tff(c_207,plain,(
    ! [D_80] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_200])).

tff(c_52,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_126,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_126])).

tff(c_211,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_252,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_338,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_252])).

tff(c_24881,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24850,c_338])).

tff(c_24937,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_24881])).

tff(c_24952,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_24937])).

tff(c_24956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_573,c_24952])).

tff(c_24958,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_24999,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24958,c_24986])).

tff(c_25119,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25103,c_25103,c_24999])).

tff(c_24957,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_25127,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25103,c_24957])).

tff(c_25126,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25103,c_24958])).

tff(c_25184,plain,(
    ! [B_1119,C_1120,A_1121] :
      ( k1_xboole_0 = B_1119
      | v1_funct_2(C_1120,A_1121,B_1119)
      | k1_relset_1(A_1121,B_1119,C_1120) != A_1121
      | ~ m1_subset_1(C_1120,k1_zfmisc_1(k2_zfmisc_1(A_1121,B_1119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_25187,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_25126,c_25184])).

tff(c_25202,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_25127,c_67,c_25187])).

tff(c_25218,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25119,c_25202])).

tff(c_25302,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_25293,c_25218])).

tff(c_25324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_25302])).

tff(c_25325,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25337,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25325,c_25325,c_6])).

tff(c_25326,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_25331,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25325,c_25326])).

tff(c_25378,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25337,c_25331,c_58])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25345,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25325,c_25325,c_8])).

tff(c_25401,plain,(
    ! [C_1139,B_1140,A_1141] :
      ( v5_relat_1(C_1139,B_1140)
      | ~ m1_subset_1(C_1139,k1_zfmisc_1(k2_zfmisc_1(A_1141,B_1140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25408,plain,(
    ! [C_1142,B_1143] :
      ( v5_relat_1(C_1142,B_1143)
      | ~ m1_subset_1(C_1142,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25345,c_25401])).

tff(c_25411,plain,(
    ! [B_1143] : v5_relat_1('#skF_4',B_1143) ),
    inference(resolution,[status(thm)],[c_25378,c_25408])).

tff(c_25379,plain,(
    ! [C_1133,A_1134,B_1135] :
      ( v1_relat_1(C_1133)
      | ~ m1_subset_1(C_1133,k1_zfmisc_1(k2_zfmisc_1(A_1134,B_1135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_25384,plain,(
    ! [C_1136] :
      ( v1_relat_1(C_1136)
      | ~ m1_subset_1(C_1136,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25345,c_25379])).

tff(c_25388,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_25378,c_25384])).

tff(c_25679,plain,(
    ! [C_1193,A_1194,B_1195] :
      ( v4_relat_1(C_1193,A_1194)
      | ~ m1_subset_1(C_1193,k1_zfmisc_1(k2_zfmisc_1(A_1194,B_1195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25697,plain,(
    ! [C_1199,A_1200] :
      ( v4_relat_1(C_1199,A_1200)
      | ~ m1_subset_1(C_1199,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25337,c_25679])).

tff(c_25700,plain,(
    ! [A_1200] : v4_relat_1('#skF_4',A_1200) ),
    inference(resolution,[status(thm)],[c_25378,c_25697])).

tff(c_25728,plain,(
    ! [B_1204,A_1205] :
      ( k7_relat_1(B_1204,A_1205) = B_1204
      | ~ v4_relat_1(B_1204,A_1205)
      | ~ v1_relat_1(B_1204) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_25731,plain,(
    ! [A_1200] :
      ( k7_relat_1('#skF_4',A_1200) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_25700,c_25728])).

tff(c_25734,plain,(
    ! [A_1200] : k7_relat_1('#skF_4',A_1200) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25388,c_25731])).

tff(c_26034,plain,(
    ! [A_1254,B_1255,C_1256,D_1257] :
      ( k2_partfun1(A_1254,B_1255,C_1256,D_1257) = k7_relat_1(C_1256,D_1257)
      | ~ m1_subset_1(C_1256,k1_zfmisc_1(k2_zfmisc_1(A_1254,B_1255)))
      | ~ v1_funct_1(C_1256) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26119,plain,(
    ! [B_1288,C_1289,D_1290] :
      ( k2_partfun1('#skF_1',B_1288,C_1289,D_1290) = k7_relat_1(C_1289,D_1290)
      | ~ m1_subset_1(C_1289,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1289) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25345,c_26034])).

tff(c_26123,plain,(
    ! [B_1288,D_1290] :
      ( k2_partfun1('#skF_1',B_1288,'#skF_4',D_1290) = k7_relat_1('#skF_4',D_1290)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_25378,c_26119])).

tff(c_26127,plain,(
    ! [B_1288,D_1290] : k2_partfun1('#skF_1',B_1288,'#skF_4',D_1290) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25734,c_26123])).

tff(c_26086,plain,(
    ! [A_1275,C_1276,D_1277] :
      ( k2_partfun1(A_1275,'#skF_1',C_1276,D_1277) = k7_relat_1(C_1276,D_1277)
      | ~ m1_subset_1(C_1276,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25337,c_26034])).

tff(c_26090,plain,(
    ! [A_1275,D_1277] :
      ( k2_partfun1(A_1275,'#skF_1','#skF_4',D_1277) = k7_relat_1('#skF_4',D_1277)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_25378,c_26086])).

tff(c_26094,plain,(
    ! [A_1275,D_1277] : k2_partfun1(A_1275,'#skF_1','#skF_4',D_1277) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25734,c_26090])).

tff(c_25916,plain,(
    ! [A_1232,B_1233,C_1234,D_1235] :
      ( v1_funct_1(k2_partfun1(A_1232,B_1233,C_1234,D_1235))
      | ~ m1_subset_1(C_1234,k1_zfmisc_1(k2_zfmisc_1(A_1232,B_1233)))
      | ~ v1_funct_1(C_1234) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_25957,plain,(
    ! [B_1238,C_1239,D_1240] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_1238,C_1239,D_1240))
      | ~ m1_subset_1(C_1239,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25345,c_25916])).

tff(c_25959,plain,(
    ! [B_1238,D_1240] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_1238,'#skF_4',D_1240))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_25378,c_25957])).

tff(c_25962,plain,(
    ! [B_1238,D_1240] : v1_funct_1(k2_partfun1('#skF_1',B_1238,'#skF_4',D_1240)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25959])).

tff(c_25921,plain,(
    ! [B_1236,A_1237] :
      ( m1_subset_1(B_1236,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1236),A_1237)))
      | ~ r1_tarski(k2_relat_1(B_1236),A_1237)
      | ~ v1_funct_1(B_1236)
      | ~ v1_relat_1(B_1236) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_25986,plain,(
    ! [B_1252] :
      ( m1_subset_1(B_1252,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(B_1252),'#skF_1')
      | ~ v1_funct_1(B_1252)
      | ~ v1_relat_1(B_1252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25337,c_25921])).

tff(c_25997,plain,(
    ! [B_1253] :
      ( m1_subset_1(B_1253,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(B_1253)
      | ~ v5_relat_1(B_1253,'#skF_1')
      | ~ v1_relat_1(B_1253) ) ),
    inference(resolution,[status(thm)],[c_12,c_25986])).

tff(c_25663,plain,(
    ! [A_1186,B_1187,C_1188,D_1189] :
      ( v1_funct_1(k2_partfun1(A_1186,B_1187,C_1188,D_1189))
      | ~ m1_subset_1(C_1188,k1_zfmisc_1(k2_zfmisc_1(A_1186,B_1187)))
      | ~ v1_funct_1(C_1188) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_25668,plain,(
    ! [B_1190,C_1191,D_1192] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_1190,C_1191,D_1192))
      | ~ m1_subset_1(C_1191,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25345,c_25663])).

tff(c_25670,plain,(
    ! [B_1190,D_1192] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_1190,'#skF_4',D_1192))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_25378,c_25668])).

tff(c_25673,plain,(
    ! [B_1190,D_1192] : v1_funct_1(k2_partfun1('#skF_1',B_1190,'#skF_4',D_1192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25670])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25362,plain,(
    ! [A_1130] :
      ( A_1130 = '#skF_1'
      | ~ r1_tarski(A_1130,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25325,c_25325,c_2])).

tff(c_25366,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_25362])).

tff(c_25413,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25366,c_25331,c_25366,c_25366,c_25331,c_25331,c_25366,c_25337,c_25331,c_25331,c_52])).

tff(c_25414,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_25413])).

tff(c_25676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25673,c_25414])).

tff(c_25677,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25413])).

tff(c_25770,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_25677])).

tff(c_26010,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_25997,c_25770])).

tff(c_26028,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25962,c_26010])).

tff(c_26056,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_26028])).

tff(c_26095,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26094,c_26056])).

tff(c_26100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25388,c_26095])).

tff(c_26101,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_26028])).

tff(c_26141,plain,(
    ~ v5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26127,c_26101])).

tff(c_26147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25411,c_26141])).

tff(c_26149,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25677])).

tff(c_25381,plain,(
    ! [C_1133] :
      ( v1_relat_1(C_1133)
      | ~ m1_subset_1(C_1133,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25345,c_25379])).

tff(c_26186,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26149,c_25381])).

tff(c_25678,plain,(
    v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25413])).

tff(c_25686,plain,(
    ! [B_1196,A_1197] :
      ( r1_tarski(k2_relat_1(B_1196),A_1197)
      | ~ v5_relat_1(B_1196,A_1197)
      | ~ v1_relat_1(B_1196) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25361,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25325,c_25325,c_2])).

tff(c_25703,plain,(
    ! [B_1202] :
      ( k2_relat_1(B_1202) = '#skF_1'
      | ~ v5_relat_1(B_1202,'#skF_1')
      | ~ v1_relat_1(B_1202) ) ),
    inference(resolution,[status(thm)],[c_25686,c_25361])).

tff(c_25707,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_25411,c_25703])).

tff(c_25710,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25388,c_25707])).

tff(c_25714,plain,(
    ! [A_4] :
      ( r1_tarski('#skF_1',A_4)
      | ~ v5_relat_1('#skF_4',A_4)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25710,c_12])).

tff(c_25718,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25388,c_25411,c_25714])).

tff(c_25404,plain,(
    ! [C_1139,B_3] :
      ( v5_relat_1(C_1139,B_3)
      | ~ m1_subset_1(C_1139,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25345,c_25401])).

tff(c_26194,plain,(
    ! [B_1296] : v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),B_1296) ),
    inference(resolution,[status(thm)],[c_26149,c_25404])).

tff(c_25691,plain,(
    ! [B_1196] :
      ( k2_relat_1(B_1196) = '#skF_1'
      | ~ v5_relat_1(B_1196,'#skF_1')
      | ~ v1_relat_1(B_1196) ) ),
    inference(resolution,[status(thm)],[c_25686,c_25361])).

tff(c_26198,plain,
    ( k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26194,c_25691])).

tff(c_26201,plain,(
    k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26186,c_26198])).

tff(c_25685,plain,(
    ! [C_1193,A_2] :
      ( v4_relat_1(C_1193,A_2)
      | ~ m1_subset_1(C_1193,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25337,c_25679])).

tff(c_26187,plain,(
    ! [A_1295] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1295) ),
    inference(resolution,[status(thm)],[c_26149,c_25685])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26190,plain,(
    ! [A_1295] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1295) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26187,c_16])).

tff(c_26269,plain,(
    ! [A_1308] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1308) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26186,c_26190])).

tff(c_25759,plain,(
    ! [B_1209,A_1210] :
      ( k1_relat_1(k7_relat_1(B_1209,A_1210)) = A_1210
      | ~ r1_tarski(A_1210,k1_relat_1(B_1209))
      | ~ v1_relat_1(B_1209) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25768,plain,(
    ! [B_1209] :
      ( k1_relat_1(k7_relat_1(B_1209,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1209) ) ),
    inference(resolution,[status(thm)],[c_25718,c_25759])).

tff(c_26275,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26269,c_25768])).

tff(c_26283,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26186,c_26275])).

tff(c_26315,plain,(
    ! [B_1312,A_1313] :
      ( v1_funct_2(B_1312,k1_relat_1(B_1312),A_1313)
      | ~ r1_tarski(k2_relat_1(B_1312),A_1313)
      | ~ v1_funct_1(B_1312)
      | ~ v1_relat_1(B_1312) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26321,plain,(
    ! [A_1313] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_1313)
      | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')),A_1313)
      | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26283,c_26315])).

tff(c_26330,plain,(
    ! [A_1313] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_1313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26186,c_25678,c_25718,c_26201,c_26321])).

tff(c_26148,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_25677])).

tff(c_26335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26330,c_26148])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.66/5.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.66/5.79  
% 13.66/5.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.66/5.79  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.66/5.79  
% 13.66/5.79  %Foreground sorts:
% 13.66/5.79  
% 13.66/5.79  
% 13.66/5.79  %Background operators:
% 13.66/5.79  
% 13.66/5.79  
% 13.66/5.79  %Foreground operators:
% 13.66/5.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.66/5.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.66/5.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.66/5.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.66/5.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.66/5.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.66/5.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.66/5.79  tff('#skF_2', type, '#skF_2': $i).
% 13.66/5.79  tff('#skF_3', type, '#skF_3': $i).
% 13.66/5.79  tff('#skF_1', type, '#skF_1': $i).
% 13.66/5.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.66/5.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.66/5.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.66/5.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.66/5.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.66/5.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.66/5.79  tff('#skF_4', type, '#skF_4': $i).
% 13.66/5.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.66/5.79  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.66/5.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.66/5.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.66/5.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.66/5.79  
% 13.93/5.82  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 13.93/5.82  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.93/5.82  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.93/5.82  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.93/5.82  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 13.93/5.82  tff(f_103, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 13.93/5.82  tff(f_97, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 13.93/5.82  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.93/5.82  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 13.93/5.82  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 13.93/5.82  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.93/5.82  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 13.93/5.82  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 13.93/5.82  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.93/5.82  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.93/5.82  tff(c_92, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.93/5.82  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_92])).
% 13.93/5.82  tff(c_54, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.93/5.82  tff(c_67, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 13.93/5.82  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.93/5.82  tff(c_24986, plain, (![A_1082, B_1083, C_1084]: (k1_relset_1(A_1082, B_1083, C_1084)=k1_relat_1(C_1084) | ~m1_subset_1(C_1084, k1_zfmisc_1(k2_zfmisc_1(A_1082, B_1083))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.93/5.82  tff(c_25000, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_24986])).
% 13.93/5.82  tff(c_25232, plain, (![B_1123, A_1124, C_1125]: (k1_xboole_0=B_1123 | k1_relset_1(A_1124, B_1123, C_1125)=A_1124 | ~v1_funct_2(C_1125, A_1124, B_1123) | ~m1_subset_1(C_1125, k1_zfmisc_1(k2_zfmisc_1(A_1124, B_1123))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.93/5.82  tff(c_25241, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_25232])).
% 13.93/5.82  tff(c_25254, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_25000, c_25241])).
% 13.93/5.82  tff(c_25255, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_67, c_25254])).
% 13.93/5.82  tff(c_18, plain, (![B_11, A_10]: (k1_relat_1(k7_relat_1(B_11, A_10))=A_10 | ~r1_tarski(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.93/5.82  tff(c_25271, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_25255, c_18])).
% 13.93/5.82  tff(c_25293, plain, (![A_1127]: (k1_relat_1(k7_relat_1('#skF_4', A_1127))=A_1127 | ~r1_tarski(A_1127, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_25271])).
% 13.93/5.82  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.93/5.82  tff(c_25086, plain, (![A_1113, B_1114, C_1115, D_1116]: (k2_partfun1(A_1113, B_1114, C_1115, D_1116)=k7_relat_1(C_1115, D_1116) | ~m1_subset_1(C_1115, k1_zfmisc_1(k2_zfmisc_1(A_1113, B_1114))) | ~v1_funct_1(C_1115))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.93/5.82  tff(c_25092, plain, (![D_1116]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1116)=k7_relat_1('#skF_4', D_1116) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_25086])).
% 13.93/5.82  tff(c_25103, plain, (![D_1116]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1116)=k7_relat_1('#skF_4', D_1116))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25092])).
% 13.93/5.82  tff(c_324, plain, (![A_123, B_124, C_125, D_126]: (k2_partfun1(A_123, B_124, C_125, D_126)=k7_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_funct_1(C_125))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.93/5.82  tff(c_328, plain, (![D_126]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_126)=k7_relat_1('#skF_4', D_126) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_324])).
% 13.93/5.82  tff(c_336, plain, (![D_126]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_126)=k7_relat_1('#skF_4', D_126))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_328])).
% 13.93/5.82  tff(c_490, plain, (![A_142, B_143, C_144, D_145]: (m1_subset_1(k2_partfun1(A_142, B_143, C_144, D_145), k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.93/5.82  tff(c_515, plain, (![D_126]: (m1_subset_1(k7_relat_1('#skF_4', D_126), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_490])).
% 13.93/5.82  tff(c_534, plain, (![D_146]: (m1_subset_1(k7_relat_1('#skF_4', D_146), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_515])).
% 13.93/5.82  tff(c_20, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.93/5.82  tff(c_574, plain, (![D_146]: (v1_relat_1(k7_relat_1('#skF_4', D_146)))), inference(resolution, [status(thm)], [c_534, c_20])).
% 13.93/5.82  tff(c_22, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.93/5.82  tff(c_573, plain, (![D_146]: (v5_relat_1(k7_relat_1('#skF_4', D_146), '#skF_2'))), inference(resolution, [status(thm)], [c_534, c_22])).
% 13.93/5.82  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.93/5.82  tff(c_286, plain, (![A_110, B_111, C_112, D_113]: (v1_funct_1(k2_partfun1(A_110, B_111, C_112, D_113)) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.93/5.82  tff(c_288, plain, (![D_113]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_113)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_286])).
% 13.93/5.82  tff(c_295, plain, (![D_113]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_113)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_288])).
% 13.93/5.82  tff(c_337, plain, (![D_113]: (v1_funct_1(k7_relat_1('#skF_4', D_113)))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_295])).
% 13.93/5.82  tff(c_262, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.93/5.82  tff(c_272, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_262])).
% 13.93/5.82  tff(c_408, plain, (![B_136, A_137, C_138]: (k1_xboole_0=B_136 | k1_relset_1(A_137, B_136, C_138)=A_137 | ~v1_funct_2(C_138, A_137, B_136) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.93/5.82  tff(c_414, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_408])).
% 13.93/5.82  tff(c_424, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_272, c_414])).
% 13.93/5.82  tff(c_425, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_67, c_424])).
% 13.93/5.82  tff(c_437, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_18])).
% 13.93/5.82  tff(c_464, plain, (![A_141]: (k1_relat_1(k7_relat_1('#skF_4', A_141))=A_141 | ~r1_tarski(A_141, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_437])).
% 13.93/5.82  tff(c_46, plain, (![B_33, A_32]: (m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33), A_32))) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.93/5.82  tff(c_470, plain, (![A_141, A_32]: (m1_subset_1(k7_relat_1('#skF_4', A_141), k1_zfmisc_1(k2_zfmisc_1(A_141, A_32))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_141)), A_32) | ~v1_funct_1(k7_relat_1('#skF_4', A_141)) | ~v1_relat_1(k7_relat_1('#skF_4', A_141)) | ~r1_tarski(A_141, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_464, c_46])).
% 13.93/5.82  tff(c_485, plain, (![A_141, A_32]: (m1_subset_1(k7_relat_1('#skF_4', A_141), k1_zfmisc_1(k2_zfmisc_1(A_141, A_32))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_141)), A_32) | ~v1_relat_1(k7_relat_1('#skF_4', A_141)) | ~r1_tarski(A_141, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_470])).
% 13.93/5.82  tff(c_24850, plain, (![A_1074, A_1075]: (m1_subset_1(k7_relat_1('#skF_4', A_1074), k1_zfmisc_1(k2_zfmisc_1(A_1074, A_1075))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_1074)), A_1075) | ~r1_tarski(A_1074, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_485])).
% 13.93/5.82  tff(c_198, plain, (![A_77, B_78, C_79, D_80]: (v1_funct_1(k2_partfun1(A_77, B_78, C_79, D_80)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.93/5.82  tff(c_200, plain, (![D_80]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_80)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_198])).
% 13.93/5.82  tff(c_207, plain, (![D_80]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_80)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_200])).
% 13.93/5.82  tff(c_52, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.93/5.82  tff(c_126, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 13.93/5.82  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_126])).
% 13.93/5.82  tff(c_211, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 13.93/5.82  tff(c_252, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_211])).
% 13.93/5.82  tff(c_338, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_252])).
% 13.93/5.82  tff(c_24881, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24850, c_338])).
% 13.93/5.82  tff(c_24937, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_24881])).
% 13.93/5.82  tff(c_24952, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_24937])).
% 13.93/5.82  tff(c_24956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_574, c_573, c_24952])).
% 13.93/5.82  tff(c_24958, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_211])).
% 13.93/5.82  tff(c_24999, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_24958, c_24986])).
% 13.93/5.82  tff(c_25119, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_25103, c_25103, c_24999])).
% 13.93/5.82  tff(c_24957, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_211])).
% 13.93/5.82  tff(c_25127, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25103, c_24957])).
% 13.93/5.82  tff(c_25126, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25103, c_24958])).
% 13.93/5.82  tff(c_25184, plain, (![B_1119, C_1120, A_1121]: (k1_xboole_0=B_1119 | v1_funct_2(C_1120, A_1121, B_1119) | k1_relset_1(A_1121, B_1119, C_1120)!=A_1121 | ~m1_subset_1(C_1120, k1_zfmisc_1(k2_zfmisc_1(A_1121, B_1119))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.93/5.82  tff(c_25187, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_25126, c_25184])).
% 13.93/5.82  tff(c_25202, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_25127, c_67, c_25187])).
% 13.93/5.82  tff(c_25218, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25119, c_25202])).
% 13.93/5.82  tff(c_25302, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_25293, c_25218])).
% 13.93/5.82  tff(c_25324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_25302])).
% 13.93/5.82  tff(c_25325, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_54])).
% 13.93/5.82  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.93/5.82  tff(c_25337, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25325, c_25325, c_6])).
% 13.93/5.82  tff(c_25326, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 13.93/5.82  tff(c_25331, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25325, c_25326])).
% 13.93/5.82  tff(c_25378, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25337, c_25331, c_58])).
% 13.93/5.82  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.93/5.82  tff(c_25345, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25325, c_25325, c_8])).
% 13.93/5.82  tff(c_25401, plain, (![C_1139, B_1140, A_1141]: (v5_relat_1(C_1139, B_1140) | ~m1_subset_1(C_1139, k1_zfmisc_1(k2_zfmisc_1(A_1141, B_1140))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.93/5.82  tff(c_25408, plain, (![C_1142, B_1143]: (v5_relat_1(C_1142, B_1143) | ~m1_subset_1(C_1142, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25345, c_25401])).
% 13.93/5.82  tff(c_25411, plain, (![B_1143]: (v5_relat_1('#skF_4', B_1143))), inference(resolution, [status(thm)], [c_25378, c_25408])).
% 13.93/5.82  tff(c_25379, plain, (![C_1133, A_1134, B_1135]: (v1_relat_1(C_1133) | ~m1_subset_1(C_1133, k1_zfmisc_1(k2_zfmisc_1(A_1134, B_1135))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.93/5.82  tff(c_25384, plain, (![C_1136]: (v1_relat_1(C_1136) | ~m1_subset_1(C_1136, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25345, c_25379])).
% 13.93/5.82  tff(c_25388, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_25378, c_25384])).
% 13.93/5.82  tff(c_25679, plain, (![C_1193, A_1194, B_1195]: (v4_relat_1(C_1193, A_1194) | ~m1_subset_1(C_1193, k1_zfmisc_1(k2_zfmisc_1(A_1194, B_1195))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.93/5.82  tff(c_25697, plain, (![C_1199, A_1200]: (v4_relat_1(C_1199, A_1200) | ~m1_subset_1(C_1199, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25337, c_25679])).
% 13.93/5.82  tff(c_25700, plain, (![A_1200]: (v4_relat_1('#skF_4', A_1200))), inference(resolution, [status(thm)], [c_25378, c_25697])).
% 13.93/5.82  tff(c_25728, plain, (![B_1204, A_1205]: (k7_relat_1(B_1204, A_1205)=B_1204 | ~v4_relat_1(B_1204, A_1205) | ~v1_relat_1(B_1204))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.93/5.82  tff(c_25731, plain, (![A_1200]: (k7_relat_1('#skF_4', A_1200)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_25700, c_25728])).
% 13.93/5.82  tff(c_25734, plain, (![A_1200]: (k7_relat_1('#skF_4', A_1200)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25388, c_25731])).
% 13.93/5.82  tff(c_26034, plain, (![A_1254, B_1255, C_1256, D_1257]: (k2_partfun1(A_1254, B_1255, C_1256, D_1257)=k7_relat_1(C_1256, D_1257) | ~m1_subset_1(C_1256, k1_zfmisc_1(k2_zfmisc_1(A_1254, B_1255))) | ~v1_funct_1(C_1256))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.93/5.82  tff(c_26119, plain, (![B_1288, C_1289, D_1290]: (k2_partfun1('#skF_1', B_1288, C_1289, D_1290)=k7_relat_1(C_1289, D_1290) | ~m1_subset_1(C_1289, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1289))), inference(superposition, [status(thm), theory('equality')], [c_25345, c_26034])).
% 13.93/5.82  tff(c_26123, plain, (![B_1288, D_1290]: (k2_partfun1('#skF_1', B_1288, '#skF_4', D_1290)=k7_relat_1('#skF_4', D_1290) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_25378, c_26119])).
% 13.93/5.82  tff(c_26127, plain, (![B_1288, D_1290]: (k2_partfun1('#skF_1', B_1288, '#skF_4', D_1290)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25734, c_26123])).
% 13.93/5.82  tff(c_26086, plain, (![A_1275, C_1276, D_1277]: (k2_partfun1(A_1275, '#skF_1', C_1276, D_1277)=k7_relat_1(C_1276, D_1277) | ~m1_subset_1(C_1276, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1276))), inference(superposition, [status(thm), theory('equality')], [c_25337, c_26034])).
% 13.93/5.82  tff(c_26090, plain, (![A_1275, D_1277]: (k2_partfun1(A_1275, '#skF_1', '#skF_4', D_1277)=k7_relat_1('#skF_4', D_1277) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_25378, c_26086])).
% 13.93/5.82  tff(c_26094, plain, (![A_1275, D_1277]: (k2_partfun1(A_1275, '#skF_1', '#skF_4', D_1277)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25734, c_26090])).
% 13.93/5.82  tff(c_25916, plain, (![A_1232, B_1233, C_1234, D_1235]: (v1_funct_1(k2_partfun1(A_1232, B_1233, C_1234, D_1235)) | ~m1_subset_1(C_1234, k1_zfmisc_1(k2_zfmisc_1(A_1232, B_1233))) | ~v1_funct_1(C_1234))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.93/5.82  tff(c_25957, plain, (![B_1238, C_1239, D_1240]: (v1_funct_1(k2_partfun1('#skF_1', B_1238, C_1239, D_1240)) | ~m1_subset_1(C_1239, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1239))), inference(superposition, [status(thm), theory('equality')], [c_25345, c_25916])).
% 13.93/5.82  tff(c_25959, plain, (![B_1238, D_1240]: (v1_funct_1(k2_partfun1('#skF_1', B_1238, '#skF_4', D_1240)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_25378, c_25957])).
% 13.93/5.82  tff(c_25962, plain, (![B_1238, D_1240]: (v1_funct_1(k2_partfun1('#skF_1', B_1238, '#skF_4', D_1240)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25959])).
% 13.93/5.82  tff(c_25921, plain, (![B_1236, A_1237]: (m1_subset_1(B_1236, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1236), A_1237))) | ~r1_tarski(k2_relat_1(B_1236), A_1237) | ~v1_funct_1(B_1236) | ~v1_relat_1(B_1236))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.93/5.82  tff(c_25986, plain, (![B_1252]: (m1_subset_1(B_1252, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(B_1252), '#skF_1') | ~v1_funct_1(B_1252) | ~v1_relat_1(B_1252))), inference(superposition, [status(thm), theory('equality')], [c_25337, c_25921])).
% 13.93/5.82  tff(c_25997, plain, (![B_1253]: (m1_subset_1(B_1253, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(B_1253) | ~v5_relat_1(B_1253, '#skF_1') | ~v1_relat_1(B_1253))), inference(resolution, [status(thm)], [c_12, c_25986])).
% 13.93/5.82  tff(c_25663, plain, (![A_1186, B_1187, C_1188, D_1189]: (v1_funct_1(k2_partfun1(A_1186, B_1187, C_1188, D_1189)) | ~m1_subset_1(C_1188, k1_zfmisc_1(k2_zfmisc_1(A_1186, B_1187))) | ~v1_funct_1(C_1188))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.93/5.82  tff(c_25668, plain, (![B_1190, C_1191, D_1192]: (v1_funct_1(k2_partfun1('#skF_1', B_1190, C_1191, D_1192)) | ~m1_subset_1(C_1191, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1191))), inference(superposition, [status(thm), theory('equality')], [c_25345, c_25663])).
% 13.93/5.82  tff(c_25670, plain, (![B_1190, D_1192]: (v1_funct_1(k2_partfun1('#skF_1', B_1190, '#skF_4', D_1192)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_25378, c_25668])).
% 13.93/5.82  tff(c_25673, plain, (![B_1190, D_1192]: (v1_funct_1(k2_partfun1('#skF_1', B_1190, '#skF_4', D_1192)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25670])).
% 13.93/5.82  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.93/5.82  tff(c_25362, plain, (![A_1130]: (A_1130='#skF_1' | ~r1_tarski(A_1130, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25325, c_25325, c_2])).
% 13.93/5.82  tff(c_25366, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_56, c_25362])).
% 13.93/5.82  tff(c_25413, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25366, c_25331, c_25366, c_25366, c_25331, c_25331, c_25366, c_25337, c_25331, c_25331, c_52])).
% 13.93/5.82  tff(c_25414, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_25413])).
% 13.93/5.82  tff(c_25676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25673, c_25414])).
% 13.93/5.82  tff(c_25677, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_25413])).
% 13.93/5.82  tff(c_25770, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_25677])).
% 13.93/5.82  tff(c_26010, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_25997, c_25770])).
% 13.93/5.82  tff(c_26028, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25962, c_26010])).
% 13.93/5.82  tff(c_26056, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_26028])).
% 13.93/5.82  tff(c_26095, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26094, c_26056])).
% 13.93/5.82  tff(c_26100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25388, c_26095])).
% 13.93/5.82  tff(c_26101, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_26028])).
% 13.93/5.82  tff(c_26141, plain, (~v5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26127, c_26101])).
% 13.93/5.82  tff(c_26147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25411, c_26141])).
% 13.93/5.82  tff(c_26149, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_25677])).
% 13.93/5.82  tff(c_25381, plain, (![C_1133]: (v1_relat_1(C_1133) | ~m1_subset_1(C_1133, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25345, c_25379])).
% 13.93/5.82  tff(c_26186, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_26149, c_25381])).
% 13.93/5.82  tff(c_25678, plain, (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitRight, [status(thm)], [c_25413])).
% 13.93/5.82  tff(c_25686, plain, (![B_1196, A_1197]: (r1_tarski(k2_relat_1(B_1196), A_1197) | ~v5_relat_1(B_1196, A_1197) | ~v1_relat_1(B_1196))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.93/5.82  tff(c_25361, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25325, c_25325, c_2])).
% 13.93/5.82  tff(c_25703, plain, (![B_1202]: (k2_relat_1(B_1202)='#skF_1' | ~v5_relat_1(B_1202, '#skF_1') | ~v1_relat_1(B_1202))), inference(resolution, [status(thm)], [c_25686, c_25361])).
% 13.93/5.82  tff(c_25707, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_25411, c_25703])).
% 13.93/5.82  tff(c_25710, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25388, c_25707])).
% 13.93/5.82  tff(c_25714, plain, (![A_4]: (r1_tarski('#skF_1', A_4) | ~v5_relat_1('#skF_4', A_4) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_25710, c_12])).
% 13.93/5.82  tff(c_25718, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_25388, c_25411, c_25714])).
% 13.93/5.82  tff(c_25404, plain, (![C_1139, B_3]: (v5_relat_1(C_1139, B_3) | ~m1_subset_1(C_1139, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25345, c_25401])).
% 13.93/5.82  tff(c_26194, plain, (![B_1296]: (v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), B_1296))), inference(resolution, [status(thm)], [c_26149, c_25404])).
% 13.93/5.82  tff(c_25691, plain, (![B_1196]: (k2_relat_1(B_1196)='#skF_1' | ~v5_relat_1(B_1196, '#skF_1') | ~v1_relat_1(B_1196))), inference(resolution, [status(thm)], [c_25686, c_25361])).
% 13.93/5.82  tff(c_26198, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_26194, c_25691])).
% 13.93/5.82  tff(c_26201, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26186, c_26198])).
% 13.93/5.82  tff(c_25685, plain, (![C_1193, A_2]: (v4_relat_1(C_1193, A_2) | ~m1_subset_1(C_1193, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25337, c_25679])).
% 13.93/5.82  tff(c_26187, plain, (![A_1295]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1295))), inference(resolution, [status(thm)], [c_26149, c_25685])).
% 13.93/5.82  tff(c_16, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.93/5.82  tff(c_26190, plain, (![A_1295]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1295)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_26187, c_16])).
% 13.93/5.82  tff(c_26269, plain, (![A_1308]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1308)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26186, c_26190])).
% 13.93/5.82  tff(c_25759, plain, (![B_1209, A_1210]: (k1_relat_1(k7_relat_1(B_1209, A_1210))=A_1210 | ~r1_tarski(A_1210, k1_relat_1(B_1209)) | ~v1_relat_1(B_1209))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.93/5.82  tff(c_25768, plain, (![B_1209]: (k1_relat_1(k7_relat_1(B_1209, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1209))), inference(resolution, [status(thm)], [c_25718, c_25759])).
% 13.93/5.82  tff(c_26275, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26269, c_25768])).
% 13.93/5.82  tff(c_26283, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26186, c_26275])).
% 13.93/5.82  tff(c_26315, plain, (![B_1312, A_1313]: (v1_funct_2(B_1312, k1_relat_1(B_1312), A_1313) | ~r1_tarski(k2_relat_1(B_1312), A_1313) | ~v1_funct_1(B_1312) | ~v1_relat_1(B_1312))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.93/5.82  tff(c_26321, plain, (![A_1313]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_1313) | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), A_1313) | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_26283, c_26315])).
% 13.93/5.82  tff(c_26330, plain, (![A_1313]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_1313))), inference(demodulation, [status(thm), theory('equality')], [c_26186, c_25678, c_25718, c_26201, c_26321])).
% 13.93/5.82  tff(c_26148, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_25677])).
% 13.93/5.82  tff(c_26335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26330, c_26148])).
% 13.93/5.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.93/5.82  
% 13.93/5.82  Inference rules
% 13.93/5.82  ----------------------
% 13.93/5.82  #Ref     : 0
% 13.93/5.82  #Sup     : 6216
% 13.93/5.82  #Fact    : 0
% 13.93/5.82  #Define  : 0
% 13.93/5.82  #Split   : 20
% 13.93/5.82  #Chain   : 0
% 13.93/5.82  #Close   : 0
% 13.93/5.82  
% 13.93/5.82  Ordering : KBO
% 13.93/5.82  
% 13.93/5.82  Simplification rules
% 13.93/5.82  ----------------------
% 13.93/5.82  #Subsume      : 1959
% 13.93/5.82  #Demod        : 7047
% 13.93/5.82  #Tautology    : 2010
% 13.93/5.82  #SimpNegUnit  : 31
% 13.93/5.82  #BackRed      : 55
% 13.93/5.82  
% 13.93/5.82  #Partial instantiations: 0
% 13.93/5.82  #Strategies tried      : 1
% 13.93/5.82  
% 13.93/5.82  Timing (in seconds)
% 13.93/5.82  ----------------------
% 13.93/5.82  Preprocessing        : 0.41
% 13.93/5.82  Parsing              : 0.20
% 13.93/5.82  CNF conversion       : 0.03
% 13.93/5.82  Main loop            : 4.62
% 13.93/5.82  Inferencing          : 1.16
% 13.93/5.82  Reduction            : 2.00
% 13.93/5.82  Demodulation         : 1.59
% 13.93/5.82  BG Simplification    : 0.12
% 13.93/5.82  Subsumption          : 1.08
% 13.93/5.82  Abstraction          : 0.19
% 13.93/5.82  MUC search           : 0.00
% 13.93/5.82  Cooper               : 0.00
% 13.93/5.82  Total                : 5.08
% 13.93/5.82  Index Insertion      : 0.00
% 13.93/5.82  Index Deletion       : 0.00
% 13.93/5.82  Index Matching       : 0.00
% 13.93/5.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
