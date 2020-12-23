%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:36 EST 2020

% Result     : Theorem 13.27s
% Output     : CNFRefutation 13.72s
% Verified   : 
% Statistics : Number of formulae       :  186 (1624 expanded)
%              Number of leaves         :   36 ( 520 expanded)
%              Depth                    :   15
%              Number of atoms          :  329 (5138 expanded)
%              Number of equality atoms :   90 (1881 expanded)
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

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_62,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_127,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_127])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_29380,plain,(
    ! [A_1071,B_1072,C_1073] :
      ( k1_relset_1(A_1071,B_1072,C_1073) = k1_relat_1(C_1073)
      | ~ m1_subset_1(C_1073,k1_zfmisc_1(k2_zfmisc_1(A_1071,B_1072))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_29394,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_29380])).

tff(c_29549,plain,(
    ! [B_1110,A_1111,C_1112] :
      ( k1_xboole_0 = B_1110
      | k1_relset_1(A_1111,B_1110,C_1112) = A_1111
      | ~ v1_funct_2(C_1112,A_1111,B_1110)
      | ~ m1_subset_1(C_1112,k1_zfmisc_1(k2_zfmisc_1(A_1111,B_1110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_29555,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_29549])).

tff(c_29565,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_29394,c_29555])).

tff(c_29566,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_29565])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_29581,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29566,c_24])).

tff(c_29591,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_29581])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_29503,plain,(
    ! [A_1104,B_1105,C_1106,D_1107] :
      ( k2_partfun1(A_1104,B_1105,C_1106,D_1107) = k7_relat_1(C_1106,D_1107)
      | ~ m1_subset_1(C_1106,k1_zfmisc_1(k2_zfmisc_1(A_1104,B_1105)))
      | ~ v1_funct_1(C_1106) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_29509,plain,(
    ! [D_1107] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1107) = k7_relat_1('#skF_4',D_1107)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_29503])).

tff(c_29520,plain,(
    ! [D_1107] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1107) = k7_relat_1('#skF_4',D_1107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_29509])).

tff(c_542,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k2_partfun1(A_151,B_152,C_153,D_154) = k7_relat_1(C_153,D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_546,plain,(
    ! [D_154] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_154) = k7_relat_1('#skF_4',D_154)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_542])).

tff(c_554,plain,(
    ! [D_154] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_154) = k7_relat_1('#skF_4',D_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_546])).

tff(c_716,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( m1_subset_1(k2_partfun1(A_170,B_171,C_172,D_173),k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_741,plain,(
    ! [D_154] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_154),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_716])).

tff(c_760,plain,(
    ! [D_174] : m1_subset_1(k7_relat_1('#skF_4',D_174),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_741])).

tff(c_26,plain,(
    ! [C_16,A_14,B_15] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_804,plain,(
    ! [D_174] : v1_relat_1(k7_relat_1('#skF_4',D_174)) ),
    inference(resolution,[status(thm)],[c_760,c_26])).

tff(c_28,plain,(
    ! [C_19,B_18,A_17] :
      ( v5_relat_1(C_19,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_802,plain,(
    ! [D_174] : v5_relat_1(k7_relat_1('#skF_4',D_174),'#skF_2') ),
    inference(resolution,[status(thm)],[c_760,c_28])).

tff(c_18,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_497,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( v1_funct_1(k2_partfun1(A_138,B_139,C_140,D_141))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_499,plain,(
    ! [D_141] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_141))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_497])).

tff(c_506,plain,(
    ! [D_141] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_141)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_499])).

tff(c_555,plain,(
    ! [D_141] : v1_funct_1(k7_relat_1('#skF_4',D_141)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_506])).

tff(c_449,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_459,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_449])).

tff(c_640,plain,(
    ! [B_165,A_166,C_167] :
      ( k1_xboole_0 = B_165
      | k1_relset_1(A_166,B_165,C_167) = A_166
      | ~ v1_funct_2(C_167,A_166,B_165)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_646,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_640])).

tff(c_656,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_459,c_646])).

tff(c_657,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_656])).

tff(c_678,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_24])).

tff(c_856,plain,(
    ! [A_179] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_179)) = A_179
      | ~ r1_tarski(A_179,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_678])).

tff(c_52,plain,(
    ! [B_35,A_34] :
      ( m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_35),A_34)))
      | ~ r1_tarski(k2_relat_1(B_35),A_34)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_868,plain,(
    ! [A_179,A_34] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_179),k1_zfmisc_1(k2_zfmisc_1(A_179,A_34)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_179)),A_34)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_179))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_179))
      | ~ r1_tarski(A_179,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_52])).

tff(c_29168,plain,(
    ! [A_1052,A_1053] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_1052),k1_zfmisc_1(k2_zfmisc_1(A_1052,A_1053)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_1052)),A_1053)
      | ~ r1_tarski(A_1052,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_555,c_868])).

tff(c_309,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( v1_funct_1(k2_partfun1(A_91,B_92,C_93,D_94))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_311,plain,(
    ! [D_94] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_94))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_309])).

tff(c_318,plain,(
    ! [D_94] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_311])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_137,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_137])).

tff(c_322,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_363,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_556,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_363])).

tff(c_29191,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_29168,c_556])).

tff(c_29246,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_29191])).

tff(c_29269,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_29246])).

tff(c_29275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_802,c_29269])).

tff(c_29277,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_29393,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_29277,c_29380])).

tff(c_29523,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29520,c_29520,c_29393])).

tff(c_29276,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_29529,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29520,c_29276])).

tff(c_29528,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29520,c_29277])).

tff(c_29671,plain,(
    ! [B_1116,C_1117,A_1118] :
      ( k1_xboole_0 = B_1116
      | v1_funct_2(C_1117,A_1118,B_1116)
      | k1_relset_1(A_1118,B_1116,C_1117) != A_1118
      | ~ m1_subset_1(C_1117,k1_zfmisc_1(k2_zfmisc_1(A_1118,B_1116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_29674,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_29528,c_29671])).

tff(c_29689,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_29529,c_76,c_29674])).

tff(c_29807,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29523,c_29689])).

tff(c_29814,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_29591,c_29807])).

tff(c_29818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_29814])).

tff(c_29819,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29833,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29819,c_29819,c_14])).

tff(c_29820,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_29826,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29819,c_29820])).

tff(c_29857,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29833,c_29826,c_64])).

tff(c_30247,plain,(
    ! [C_1193,B_1194,A_1195] :
      ( v5_relat_1(C_1193,B_1194)
      | ~ m1_subset_1(C_1193,k1_zfmisc_1(k2_zfmisc_1(A_1195,B_1194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30276,plain,(
    ! [C_1199,B_1200] :
      ( v5_relat_1(C_1199,B_1200)
      | ~ m1_subset_1(C_1199,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29833,c_30247])).

tff(c_30279,plain,(
    ! [B_1200] : v5_relat_1('#skF_4',B_1200) ),
    inference(resolution,[status(thm)],[c_29857,c_30276])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29841,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29819,c_29819,c_12])).

tff(c_29871,plain,(
    ! [C_1129,A_1130,B_1131] :
      ( v1_relat_1(C_1129)
      | ~ m1_subset_1(C_1129,k1_zfmisc_1(k2_zfmisc_1(A_1130,B_1131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_29876,plain,(
    ! [C_1132] :
      ( v1_relat_1(C_1132)
      | ~ m1_subset_1(C_1132,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29841,c_29871])).

tff(c_29880,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_29857,c_29876])).

tff(c_30310,plain,(
    ! [C_1205,A_1206,B_1207] :
      ( v4_relat_1(C_1205,A_1206)
      | ~ m1_subset_1(C_1205,k1_zfmisc_1(k2_zfmisc_1(A_1206,B_1207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30317,plain,(
    ! [C_1208,A_1209] :
      ( v4_relat_1(C_1208,A_1209)
      | ~ m1_subset_1(C_1208,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29841,c_30310])).

tff(c_30321,plain,(
    ! [A_1210] : v4_relat_1('#skF_4',A_1210) ),
    inference(resolution,[status(thm)],[c_29857,c_30317])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30324,plain,(
    ! [A_1210] :
      ( k7_relat_1('#skF_4',A_1210) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30321,c_22])).

tff(c_30327,plain,(
    ! [A_1210] : k7_relat_1('#skF_4',A_1210) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29880,c_30324])).

tff(c_30602,plain,(
    ! [A_1255,B_1256,C_1257,D_1258] :
      ( k2_partfun1(A_1255,B_1256,C_1257,D_1258) = k7_relat_1(C_1257,D_1258)
      | ~ m1_subset_1(C_1257,k1_zfmisc_1(k2_zfmisc_1(A_1255,B_1256)))
      | ~ v1_funct_1(C_1257) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30813,plain,(
    ! [B_1292,C_1293,D_1294] :
      ( k2_partfun1('#skF_1',B_1292,C_1293,D_1294) = k7_relat_1(C_1293,D_1294)
      | ~ m1_subset_1(C_1293,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29833,c_30602])).

tff(c_30817,plain,(
    ! [B_1292,D_1294] :
      ( k2_partfun1('#skF_1',B_1292,'#skF_4',D_1294) = k7_relat_1('#skF_4',D_1294)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29857,c_30813])).

tff(c_30821,plain,(
    ! [B_1292,D_1294] : k2_partfun1('#skF_1',B_1292,'#skF_4',D_1294) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30327,c_30817])).

tff(c_30756,plain,(
    ! [B_1282,C_1283,D_1284] :
      ( k2_partfun1('#skF_1',B_1282,C_1283,D_1284) = k7_relat_1(C_1283,D_1284)
      | ~ m1_subset_1(C_1283,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29833,c_30602])).

tff(c_30760,plain,(
    ! [B_1282,D_1284] :
      ( k2_partfun1('#skF_1',B_1282,'#skF_4',D_1284) = k7_relat_1('#skF_4',D_1284)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29857,c_30756])).

tff(c_30764,plain,(
    ! [B_1282,D_1284] : k2_partfun1('#skF_1',B_1282,'#skF_4',D_1284) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30327,c_30760])).

tff(c_30519,plain,(
    ! [A_1236,B_1237,C_1238,D_1239] :
      ( v1_funct_1(k2_partfun1(A_1236,B_1237,C_1238,D_1239))
      | ~ m1_subset_1(C_1238,k1_zfmisc_1(k2_zfmisc_1(A_1236,B_1237)))
      | ~ v1_funct_1(C_1238) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30524,plain,(
    ! [A_1240,C_1241,D_1242] :
      ( v1_funct_1(k2_partfun1(A_1240,'#skF_1',C_1241,D_1242))
      | ~ m1_subset_1(C_1241,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29841,c_30519])).

tff(c_30526,plain,(
    ! [A_1240,D_1242] :
      ( v1_funct_1(k2_partfun1(A_1240,'#skF_1','#skF_4',D_1242))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29857,c_30524])).

tff(c_30529,plain,(
    ! [A_1240,D_1242] : v1_funct_1(k2_partfun1(A_1240,'#skF_1','#skF_4',D_1242)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30526])).

tff(c_30539,plain,(
    ! [B_1250,A_1251] :
      ( m1_subset_1(B_1250,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1250),A_1251)))
      | ~ r1_tarski(k2_relat_1(B_1250),A_1251)
      | ~ v1_funct_1(B_1250)
      | ~ v1_relat_1(B_1250) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30651,plain,(
    ! [B_1260] :
      ( m1_subset_1(B_1260,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(B_1260),'#skF_1')
      | ~ v1_funct_1(B_1260)
      | ~ v1_relat_1(B_1260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29841,c_30539])).

tff(c_30675,plain,(
    ! [B_1264] :
      ( m1_subset_1(B_1264,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(B_1264)
      | ~ v5_relat_1(B_1264,'#skF_1')
      | ~ v1_relat_1(B_1264) ) ),
    inference(resolution,[status(thm)],[c_18,c_30651])).

tff(c_30221,plain,(
    ! [A_1183,B_1184,C_1185,D_1186] :
      ( v1_funct_1(k2_partfun1(A_1183,B_1184,C_1185,D_1186))
      | ~ m1_subset_1(C_1185,k1_zfmisc_1(k2_zfmisc_1(A_1183,B_1184)))
      | ~ v1_funct_1(C_1185) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30226,plain,(
    ! [A_1187,C_1188,D_1189] :
      ( v1_funct_1(k2_partfun1(A_1187,'#skF_1',C_1188,D_1189))
      | ~ m1_subset_1(C_1188,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29841,c_30221])).

tff(c_30228,plain,(
    ! [A_1187,D_1189] :
      ( v1_funct_1(k2_partfun1(A_1187,'#skF_1','#skF_4',D_1189))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29857,c_30226])).

tff(c_30231,plain,(
    ! [A_1187,D_1189] : v1_funct_1(k2_partfun1(A_1187,'#skF_1','#skF_4',D_1189)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30228])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29821,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29819,c_8])).

tff(c_29881,plain,(
    ! [B_1133,A_1134] :
      ( B_1133 = A_1134
      | ~ r1_tarski(B_1133,A_1134)
      | ~ r1_tarski(A_1134,B_1133) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29887,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_29881])).

tff(c_29895,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29821,c_29887])).

tff(c_29915,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29895,c_29826,c_29895,c_29895,c_29826,c_29826,c_29895,c_29841,c_29826,c_29826,c_58])).

tff(c_29916,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_29915])).

tff(c_30234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30231,c_29916])).

tff(c_30235,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_29915])).

tff(c_30275,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_30235])).

tff(c_30693,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30675,c_30275])).

tff(c_30708,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30529,c_30693])).

tff(c_30754,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_30708])).

tff(c_30765,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30764,c_30754])).

tff(c_30770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29880,c_30765])).

tff(c_30771,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_30708])).

tff(c_30822,plain,(
    ~ v5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30821,c_30771])).

tff(c_30828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30279,c_30822])).

tff(c_30830,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_30235])).

tff(c_29873,plain,(
    ! [C_1129] :
      ( v1_relat_1(C_1129)
      | ~ m1_subset_1(C_1129,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29841,c_29871])).

tff(c_30850,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30830,c_29873])).

tff(c_30899,plain,(
    ! [C_1302,A_1303,B_1304] :
      ( v4_relat_1(C_1302,A_1303)
      | ~ m1_subset_1(C_1302,k1_zfmisc_1(k2_zfmisc_1(A_1303,B_1304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30906,plain,(
    ! [C_1305,A_1306] :
      ( v4_relat_1(C_1305,A_1306)
      | ~ m1_subset_1(C_1305,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29841,c_30899])).

tff(c_30932,plain,(
    ! [A_1309] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1309) ),
    inference(resolution,[status(thm)],[c_30830,c_30906])).

tff(c_30935,plain,(
    ! [A_1309] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1309) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30932,c_22])).

tff(c_31096,plain,(
    ! [A_1327] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1327) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30850,c_30935])).

tff(c_30941,plain,(
    ! [B_1310,A_1311] :
      ( k1_relat_1(k7_relat_1(B_1310,A_1311)) = A_1311
      | ~ r1_tarski(A_1311,k1_relat_1(B_1310))
      | ~ v1_relat_1(B_1310) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30955,plain,(
    ! [B_1310] :
      ( k1_relat_1(k7_relat_1(B_1310,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1310) ) ),
    inference(resolution,[status(thm)],[c_29821,c_30941])).

tff(c_31106,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31096,c_30955])).

tff(c_31117,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30850,c_31106])).

tff(c_31016,plain,(
    ! [A_1314,B_1315,C_1316] :
      ( k1_relset_1(A_1314,B_1315,C_1316) = k1_relat_1(C_1316)
      | ~ m1_subset_1(C_1316,k1_zfmisc_1(k2_zfmisc_1(A_1314,B_1315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_31038,plain,(
    ! [B_1320,C_1321] :
      ( k1_relset_1('#skF_1',B_1320,C_1321) = k1_relat_1(C_1321)
      | ~ m1_subset_1(C_1321,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29833,c_31016])).

tff(c_31043,plain,(
    ! [B_1320] : k1_relset_1('#skF_1',B_1320,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30830,c_31038])).

tff(c_31128,plain,(
    ! [B_1320] : k1_relset_1('#skF_1',B_1320,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31117,c_31043])).

tff(c_38,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_31158,plain,(
    ! [C_1332,B_1333] :
      ( v1_funct_2(C_1332,'#skF_1',B_1333)
      | k1_relset_1('#skF_1',B_1333,C_1332) != '#skF_1'
      | ~ m1_subset_1(C_1332,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29819,c_29819,c_29819,c_29819,c_69])).

tff(c_31160,plain,(
    ! [B_1333] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_1333)
      | k1_relset_1('#skF_1',B_1333,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_30830,c_31158])).

tff(c_31165,plain,(
    ! [B_1333] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_1333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31128,c_31160])).

tff(c_30829,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30235])).

tff(c_31206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31165,c_30829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:17:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.27/5.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.64/5.89  
% 13.64/5.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.64/5.89  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.64/5.89  
% 13.64/5.89  %Foreground sorts:
% 13.64/5.89  
% 13.64/5.89  
% 13.64/5.89  %Background operators:
% 13.64/5.89  
% 13.64/5.89  
% 13.64/5.89  %Foreground operators:
% 13.64/5.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.64/5.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.64/5.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.64/5.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.64/5.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.64/5.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.64/5.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.64/5.89  tff('#skF_2', type, '#skF_2': $i).
% 13.64/5.89  tff('#skF_3', type, '#skF_3': $i).
% 13.64/5.89  tff('#skF_1', type, '#skF_1': $i).
% 13.64/5.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.64/5.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.64/5.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.64/5.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.64/5.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.64/5.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.64/5.89  tff('#skF_4', type, '#skF_4': $i).
% 13.64/5.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.64/5.89  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.64/5.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.64/5.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.64/5.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.64/5.89  
% 13.72/5.92  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 13.72/5.92  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.72/5.92  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.72/5.92  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.72/5.92  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 13.72/5.92  tff(f_107, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 13.72/5.92  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 13.72/5.92  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.72/5.92  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 13.72/5.92  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 13.72/5.92  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.72/5.92  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 13.72/5.92  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.72/5.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.72/5.92  tff(c_62, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.72/5.92  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.72/5.92  tff(c_127, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.72/5.92  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_127])).
% 13.72/5.92  tff(c_60, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.72/5.92  tff(c_76, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_60])).
% 13.72/5.92  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.72/5.92  tff(c_29380, plain, (![A_1071, B_1072, C_1073]: (k1_relset_1(A_1071, B_1072, C_1073)=k1_relat_1(C_1073) | ~m1_subset_1(C_1073, k1_zfmisc_1(k2_zfmisc_1(A_1071, B_1072))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.72/5.92  tff(c_29394, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_29380])).
% 13.72/5.92  tff(c_29549, plain, (![B_1110, A_1111, C_1112]: (k1_xboole_0=B_1110 | k1_relset_1(A_1111, B_1110, C_1112)=A_1111 | ~v1_funct_2(C_1112, A_1111, B_1110) | ~m1_subset_1(C_1112, k1_zfmisc_1(k2_zfmisc_1(A_1111, B_1110))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.72/5.92  tff(c_29555, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_29549])).
% 13.72/5.92  tff(c_29565, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_29394, c_29555])).
% 13.72/5.92  tff(c_29566, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_76, c_29565])).
% 13.72/5.92  tff(c_24, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.72/5.92  tff(c_29581, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_29566, c_24])).
% 13.72/5.92  tff(c_29591, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_29581])).
% 13.72/5.92  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.72/5.92  tff(c_29503, plain, (![A_1104, B_1105, C_1106, D_1107]: (k2_partfun1(A_1104, B_1105, C_1106, D_1107)=k7_relat_1(C_1106, D_1107) | ~m1_subset_1(C_1106, k1_zfmisc_1(k2_zfmisc_1(A_1104, B_1105))) | ~v1_funct_1(C_1106))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.72/5.92  tff(c_29509, plain, (![D_1107]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1107)=k7_relat_1('#skF_4', D_1107) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_29503])).
% 13.72/5.92  tff(c_29520, plain, (![D_1107]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1107)=k7_relat_1('#skF_4', D_1107))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_29509])).
% 13.72/5.92  tff(c_542, plain, (![A_151, B_152, C_153, D_154]: (k2_partfun1(A_151, B_152, C_153, D_154)=k7_relat_1(C_153, D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(C_153))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.72/5.92  tff(c_546, plain, (![D_154]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_154)=k7_relat_1('#skF_4', D_154) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_542])).
% 13.72/5.92  tff(c_554, plain, (![D_154]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_154)=k7_relat_1('#skF_4', D_154))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_546])).
% 13.72/5.92  tff(c_716, plain, (![A_170, B_171, C_172, D_173]: (m1_subset_1(k2_partfun1(A_170, B_171, C_172, D_173), k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.72/5.92  tff(c_741, plain, (![D_154]: (m1_subset_1(k7_relat_1('#skF_4', D_154), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_554, c_716])).
% 13.72/5.92  tff(c_760, plain, (![D_174]: (m1_subset_1(k7_relat_1('#skF_4', D_174), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_741])).
% 13.72/5.92  tff(c_26, plain, (![C_16, A_14, B_15]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.72/5.92  tff(c_804, plain, (![D_174]: (v1_relat_1(k7_relat_1('#skF_4', D_174)))), inference(resolution, [status(thm)], [c_760, c_26])).
% 13.72/5.92  tff(c_28, plain, (![C_19, B_18, A_17]: (v5_relat_1(C_19, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.72/5.92  tff(c_802, plain, (![D_174]: (v5_relat_1(k7_relat_1('#skF_4', D_174), '#skF_2'))), inference(resolution, [status(thm)], [c_760, c_28])).
% 13.72/5.92  tff(c_18, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.72/5.92  tff(c_497, plain, (![A_138, B_139, C_140, D_141]: (v1_funct_1(k2_partfun1(A_138, B_139, C_140, D_141)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.72/5.92  tff(c_499, plain, (![D_141]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_141)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_497])).
% 13.72/5.92  tff(c_506, plain, (![D_141]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_141)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_499])).
% 13.72/5.92  tff(c_555, plain, (![D_141]: (v1_funct_1(k7_relat_1('#skF_4', D_141)))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_506])).
% 13.72/5.92  tff(c_449, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.72/5.92  tff(c_459, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_449])).
% 13.72/5.92  tff(c_640, plain, (![B_165, A_166, C_167]: (k1_xboole_0=B_165 | k1_relset_1(A_166, B_165, C_167)=A_166 | ~v1_funct_2(C_167, A_166, B_165) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.72/5.92  tff(c_646, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_640])).
% 13.72/5.92  tff(c_656, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_459, c_646])).
% 13.72/5.92  tff(c_657, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_76, c_656])).
% 13.72/5.92  tff(c_678, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_24])).
% 13.72/5.92  tff(c_856, plain, (![A_179]: (k1_relat_1(k7_relat_1('#skF_4', A_179))=A_179 | ~r1_tarski(A_179, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_678])).
% 13.72/5.92  tff(c_52, plain, (![B_35, A_34]: (m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_35), A_34))) | ~r1_tarski(k2_relat_1(B_35), A_34) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.72/5.92  tff(c_868, plain, (![A_179, A_34]: (m1_subset_1(k7_relat_1('#skF_4', A_179), k1_zfmisc_1(k2_zfmisc_1(A_179, A_34))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_179)), A_34) | ~v1_funct_1(k7_relat_1('#skF_4', A_179)) | ~v1_relat_1(k7_relat_1('#skF_4', A_179)) | ~r1_tarski(A_179, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_856, c_52])).
% 13.72/5.92  tff(c_29168, plain, (![A_1052, A_1053]: (m1_subset_1(k7_relat_1('#skF_4', A_1052), k1_zfmisc_1(k2_zfmisc_1(A_1052, A_1053))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_1052)), A_1053) | ~r1_tarski(A_1052, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_804, c_555, c_868])).
% 13.72/5.92  tff(c_309, plain, (![A_91, B_92, C_93, D_94]: (v1_funct_1(k2_partfun1(A_91, B_92, C_93, D_94)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.72/5.92  tff(c_311, plain, (![D_94]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_94)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_309])).
% 13.72/5.92  tff(c_318, plain, (![D_94]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_94)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_311])).
% 13.72/5.92  tff(c_58, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.72/5.92  tff(c_137, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 13.72/5.92  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_137])).
% 13.72/5.92  tff(c_322, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 13.72/5.92  tff(c_363, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_322])).
% 13.72/5.92  tff(c_556, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_363])).
% 13.72/5.92  tff(c_29191, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_29168, c_556])).
% 13.72/5.92  tff(c_29246, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_29191])).
% 13.72/5.92  tff(c_29269, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_29246])).
% 13.72/5.92  tff(c_29275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_804, c_802, c_29269])).
% 13.72/5.92  tff(c_29277, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_322])).
% 13.72/5.92  tff(c_29393, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_29277, c_29380])).
% 13.72/5.92  tff(c_29523, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_29520, c_29520, c_29393])).
% 13.72/5.92  tff(c_29276, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_322])).
% 13.72/5.92  tff(c_29529, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29520, c_29276])).
% 13.72/5.92  tff(c_29528, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_29520, c_29277])).
% 13.72/5.92  tff(c_29671, plain, (![B_1116, C_1117, A_1118]: (k1_xboole_0=B_1116 | v1_funct_2(C_1117, A_1118, B_1116) | k1_relset_1(A_1118, B_1116, C_1117)!=A_1118 | ~m1_subset_1(C_1117, k1_zfmisc_1(k2_zfmisc_1(A_1118, B_1116))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.72/5.92  tff(c_29674, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_29528, c_29671])).
% 13.72/5.92  tff(c_29689, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_29529, c_76, c_29674])).
% 13.72/5.92  tff(c_29807, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_29523, c_29689])).
% 13.72/5.92  tff(c_29814, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_29591, c_29807])).
% 13.72/5.92  tff(c_29818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_29814])).
% 13.72/5.92  tff(c_29819, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_60])).
% 13.72/5.92  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.72/5.92  tff(c_29833, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29819, c_29819, c_14])).
% 13.72/5.92  tff(c_29820, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 13.72/5.92  tff(c_29826, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29819, c_29820])).
% 13.72/5.92  tff(c_29857, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29833, c_29826, c_64])).
% 13.72/5.92  tff(c_30247, plain, (![C_1193, B_1194, A_1195]: (v5_relat_1(C_1193, B_1194) | ~m1_subset_1(C_1193, k1_zfmisc_1(k2_zfmisc_1(A_1195, B_1194))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.72/5.92  tff(c_30276, plain, (![C_1199, B_1200]: (v5_relat_1(C_1199, B_1200) | ~m1_subset_1(C_1199, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29833, c_30247])).
% 13.72/5.92  tff(c_30279, plain, (![B_1200]: (v5_relat_1('#skF_4', B_1200))), inference(resolution, [status(thm)], [c_29857, c_30276])).
% 13.72/5.92  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.72/5.92  tff(c_29841, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29819, c_29819, c_12])).
% 13.72/5.92  tff(c_29871, plain, (![C_1129, A_1130, B_1131]: (v1_relat_1(C_1129) | ~m1_subset_1(C_1129, k1_zfmisc_1(k2_zfmisc_1(A_1130, B_1131))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.72/5.92  tff(c_29876, plain, (![C_1132]: (v1_relat_1(C_1132) | ~m1_subset_1(C_1132, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29841, c_29871])).
% 13.72/5.92  tff(c_29880, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_29857, c_29876])).
% 13.72/5.92  tff(c_30310, plain, (![C_1205, A_1206, B_1207]: (v4_relat_1(C_1205, A_1206) | ~m1_subset_1(C_1205, k1_zfmisc_1(k2_zfmisc_1(A_1206, B_1207))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.72/5.92  tff(c_30317, plain, (![C_1208, A_1209]: (v4_relat_1(C_1208, A_1209) | ~m1_subset_1(C_1208, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29841, c_30310])).
% 13.72/5.92  tff(c_30321, plain, (![A_1210]: (v4_relat_1('#skF_4', A_1210))), inference(resolution, [status(thm)], [c_29857, c_30317])).
% 13.72/5.92  tff(c_22, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.72/5.92  tff(c_30324, plain, (![A_1210]: (k7_relat_1('#skF_4', A_1210)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30321, c_22])).
% 13.72/5.92  tff(c_30327, plain, (![A_1210]: (k7_relat_1('#skF_4', A_1210)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29880, c_30324])).
% 13.72/5.92  tff(c_30602, plain, (![A_1255, B_1256, C_1257, D_1258]: (k2_partfun1(A_1255, B_1256, C_1257, D_1258)=k7_relat_1(C_1257, D_1258) | ~m1_subset_1(C_1257, k1_zfmisc_1(k2_zfmisc_1(A_1255, B_1256))) | ~v1_funct_1(C_1257))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.72/5.92  tff(c_30813, plain, (![B_1292, C_1293, D_1294]: (k2_partfun1('#skF_1', B_1292, C_1293, D_1294)=k7_relat_1(C_1293, D_1294) | ~m1_subset_1(C_1293, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1293))), inference(superposition, [status(thm), theory('equality')], [c_29833, c_30602])).
% 13.72/5.92  tff(c_30817, plain, (![B_1292, D_1294]: (k2_partfun1('#skF_1', B_1292, '#skF_4', D_1294)=k7_relat_1('#skF_4', D_1294) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29857, c_30813])).
% 13.72/5.92  tff(c_30821, plain, (![B_1292, D_1294]: (k2_partfun1('#skF_1', B_1292, '#skF_4', D_1294)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30327, c_30817])).
% 13.72/5.92  tff(c_30756, plain, (![B_1282, C_1283, D_1284]: (k2_partfun1('#skF_1', B_1282, C_1283, D_1284)=k7_relat_1(C_1283, D_1284) | ~m1_subset_1(C_1283, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1283))), inference(superposition, [status(thm), theory('equality')], [c_29833, c_30602])).
% 13.72/5.92  tff(c_30760, plain, (![B_1282, D_1284]: (k2_partfun1('#skF_1', B_1282, '#skF_4', D_1284)=k7_relat_1('#skF_4', D_1284) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29857, c_30756])).
% 13.72/5.92  tff(c_30764, plain, (![B_1282, D_1284]: (k2_partfun1('#skF_1', B_1282, '#skF_4', D_1284)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30327, c_30760])).
% 13.72/5.92  tff(c_30519, plain, (![A_1236, B_1237, C_1238, D_1239]: (v1_funct_1(k2_partfun1(A_1236, B_1237, C_1238, D_1239)) | ~m1_subset_1(C_1238, k1_zfmisc_1(k2_zfmisc_1(A_1236, B_1237))) | ~v1_funct_1(C_1238))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.72/5.92  tff(c_30524, plain, (![A_1240, C_1241, D_1242]: (v1_funct_1(k2_partfun1(A_1240, '#skF_1', C_1241, D_1242)) | ~m1_subset_1(C_1241, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1241))), inference(superposition, [status(thm), theory('equality')], [c_29841, c_30519])).
% 13.72/5.92  tff(c_30526, plain, (![A_1240, D_1242]: (v1_funct_1(k2_partfun1(A_1240, '#skF_1', '#skF_4', D_1242)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29857, c_30524])).
% 13.72/5.92  tff(c_30529, plain, (![A_1240, D_1242]: (v1_funct_1(k2_partfun1(A_1240, '#skF_1', '#skF_4', D_1242)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30526])).
% 13.72/5.92  tff(c_30539, plain, (![B_1250, A_1251]: (m1_subset_1(B_1250, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1250), A_1251))) | ~r1_tarski(k2_relat_1(B_1250), A_1251) | ~v1_funct_1(B_1250) | ~v1_relat_1(B_1250))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.72/5.92  tff(c_30651, plain, (![B_1260]: (m1_subset_1(B_1260, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(B_1260), '#skF_1') | ~v1_funct_1(B_1260) | ~v1_relat_1(B_1260))), inference(superposition, [status(thm), theory('equality')], [c_29841, c_30539])).
% 13.72/5.92  tff(c_30675, plain, (![B_1264]: (m1_subset_1(B_1264, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(B_1264) | ~v5_relat_1(B_1264, '#skF_1') | ~v1_relat_1(B_1264))), inference(resolution, [status(thm)], [c_18, c_30651])).
% 13.72/5.92  tff(c_30221, plain, (![A_1183, B_1184, C_1185, D_1186]: (v1_funct_1(k2_partfun1(A_1183, B_1184, C_1185, D_1186)) | ~m1_subset_1(C_1185, k1_zfmisc_1(k2_zfmisc_1(A_1183, B_1184))) | ~v1_funct_1(C_1185))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.72/5.92  tff(c_30226, plain, (![A_1187, C_1188, D_1189]: (v1_funct_1(k2_partfun1(A_1187, '#skF_1', C_1188, D_1189)) | ~m1_subset_1(C_1188, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1188))), inference(superposition, [status(thm), theory('equality')], [c_29841, c_30221])).
% 13.72/5.92  tff(c_30228, plain, (![A_1187, D_1189]: (v1_funct_1(k2_partfun1(A_1187, '#skF_1', '#skF_4', D_1189)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29857, c_30226])).
% 13.72/5.92  tff(c_30231, plain, (![A_1187, D_1189]: (v1_funct_1(k2_partfun1(A_1187, '#skF_1', '#skF_4', D_1189)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30228])).
% 13.72/5.92  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.72/5.92  tff(c_29821, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_29819, c_8])).
% 13.72/5.92  tff(c_29881, plain, (![B_1133, A_1134]: (B_1133=A_1134 | ~r1_tarski(B_1133, A_1134) | ~r1_tarski(A_1134, B_1133))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.72/5.92  tff(c_29887, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_29881])).
% 13.72/5.92  tff(c_29895, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29821, c_29887])).
% 13.72/5.92  tff(c_29915, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29895, c_29826, c_29895, c_29895, c_29826, c_29826, c_29895, c_29841, c_29826, c_29826, c_58])).
% 13.72/5.92  tff(c_29916, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_29915])).
% 13.72/5.92  tff(c_30234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30231, c_29916])).
% 13.72/5.92  tff(c_30235, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_29915])).
% 13.72/5.92  tff(c_30275, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_30235])).
% 13.72/5.92  tff(c_30693, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_30675, c_30275])).
% 13.72/5.92  tff(c_30708, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30529, c_30693])).
% 13.72/5.92  tff(c_30754, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_30708])).
% 13.72/5.92  tff(c_30765, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30764, c_30754])).
% 13.72/5.92  tff(c_30770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29880, c_30765])).
% 13.72/5.92  tff(c_30771, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_30708])).
% 13.72/5.92  tff(c_30822, plain, (~v5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30821, c_30771])).
% 13.72/5.92  tff(c_30828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30279, c_30822])).
% 13.72/5.92  tff(c_30830, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_30235])).
% 13.72/5.92  tff(c_29873, plain, (![C_1129]: (v1_relat_1(C_1129) | ~m1_subset_1(C_1129, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29841, c_29871])).
% 13.72/5.92  tff(c_30850, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_30830, c_29873])).
% 13.72/5.92  tff(c_30899, plain, (![C_1302, A_1303, B_1304]: (v4_relat_1(C_1302, A_1303) | ~m1_subset_1(C_1302, k1_zfmisc_1(k2_zfmisc_1(A_1303, B_1304))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.72/5.92  tff(c_30906, plain, (![C_1305, A_1306]: (v4_relat_1(C_1305, A_1306) | ~m1_subset_1(C_1305, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29841, c_30899])).
% 13.72/5.92  tff(c_30932, plain, (![A_1309]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1309))), inference(resolution, [status(thm)], [c_30830, c_30906])).
% 13.72/5.92  tff(c_30935, plain, (![A_1309]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1309)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_30932, c_22])).
% 13.72/5.92  tff(c_31096, plain, (![A_1327]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1327)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30850, c_30935])).
% 13.72/5.92  tff(c_30941, plain, (![B_1310, A_1311]: (k1_relat_1(k7_relat_1(B_1310, A_1311))=A_1311 | ~r1_tarski(A_1311, k1_relat_1(B_1310)) | ~v1_relat_1(B_1310))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.72/5.92  tff(c_30955, plain, (![B_1310]: (k1_relat_1(k7_relat_1(B_1310, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1310))), inference(resolution, [status(thm)], [c_29821, c_30941])).
% 13.72/5.92  tff(c_31106, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_31096, c_30955])).
% 13.72/5.92  tff(c_31117, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30850, c_31106])).
% 13.72/5.92  tff(c_31016, plain, (![A_1314, B_1315, C_1316]: (k1_relset_1(A_1314, B_1315, C_1316)=k1_relat_1(C_1316) | ~m1_subset_1(C_1316, k1_zfmisc_1(k2_zfmisc_1(A_1314, B_1315))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.72/5.92  tff(c_31038, plain, (![B_1320, C_1321]: (k1_relset_1('#skF_1', B_1320, C_1321)=k1_relat_1(C_1321) | ~m1_subset_1(C_1321, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29833, c_31016])).
% 13.72/5.92  tff(c_31043, plain, (![B_1320]: (k1_relset_1('#skF_1', B_1320, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_30830, c_31038])).
% 13.72/5.92  tff(c_31128, plain, (![B_1320]: (k1_relset_1('#skF_1', B_1320, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31117, c_31043])).
% 13.72/5.92  tff(c_38, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.72/5.92  tff(c_69, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 13.72/5.92  tff(c_31158, plain, (![C_1332, B_1333]: (v1_funct_2(C_1332, '#skF_1', B_1333) | k1_relset_1('#skF_1', B_1333, C_1332)!='#skF_1' | ~m1_subset_1(C_1332, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_29819, c_29819, c_29819, c_29819, c_69])).
% 13.72/5.92  tff(c_31160, plain, (![B_1333]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_1333) | k1_relset_1('#skF_1', B_1333, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_30830, c_31158])).
% 13.72/5.92  tff(c_31165, plain, (![B_1333]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_1333))), inference(demodulation, [status(thm), theory('equality')], [c_31128, c_31160])).
% 13.72/5.92  tff(c_30829, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_30235])).
% 13.72/5.92  tff(c_31206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31165, c_30829])).
% 13.72/5.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.72/5.92  
% 13.72/5.92  Inference rules
% 13.72/5.92  ----------------------
% 13.72/5.92  #Ref     : 0
% 13.72/5.92  #Sup     : 6543
% 13.72/5.92  #Fact    : 0
% 13.72/5.92  #Define  : 0
% 13.72/5.92  #Split   : 20
% 13.72/5.92  #Chain   : 0
% 13.72/5.92  #Close   : 0
% 13.72/5.92  
% 13.72/5.92  Ordering : KBO
% 13.72/5.92  
% 13.72/5.92  Simplification rules
% 13.72/5.92  ----------------------
% 13.72/5.92  #Subsume      : 1459
% 13.72/5.92  #Demod        : 13769
% 13.72/5.92  #Tautology    : 2937
% 13.72/5.92  #SimpNegUnit  : 252
% 13.72/5.92  #BackRed      : 79
% 13.72/5.92  
% 13.72/5.92  #Partial instantiations: 0
% 13.72/5.92  #Strategies tried      : 1
% 13.72/5.92  
% 13.72/5.92  Timing (in seconds)
% 13.72/5.92  ----------------------
% 13.72/5.92  Preprocessing        : 0.36
% 13.72/5.93  Parsing              : 0.20
% 13.72/5.93  CNF conversion       : 0.02
% 13.72/5.93  Main loop            : 4.71
% 13.72/5.93  Inferencing          : 1.13
% 13.72/5.93  Reduction            : 2.26
% 13.72/5.93  Demodulation         : 1.84
% 13.72/5.93  BG Simplification    : 0.10
% 13.72/5.93  Subsumption          : 0.97
% 13.72/5.93  Abstraction          : 0.18
% 13.72/5.93  MUC search           : 0.00
% 13.72/5.93  Cooper               : 0.00
% 13.72/5.93  Total                : 5.13
% 13.72/5.93  Index Insertion      : 0.00
% 13.72/5.93  Index Deletion       : 0.00
% 13.72/5.93  Index Matching       : 0.00
% 13.72/5.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
