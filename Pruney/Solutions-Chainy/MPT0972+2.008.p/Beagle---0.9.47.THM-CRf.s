%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:35 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 286 expanded)
%              Number of leaves         :   36 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 852 expanded)
%              Number of equality atoms :   54 ( 203 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_316,plain,(
    ! [C_88,B_89,A_90] :
      ( v1_xboole_0(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(B_89,A_90)))
      | ~ v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_337,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_316])).

tff(c_344,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1013,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( r2_relset_1(A_167,B_168,C_169,C_169)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1032,plain,(
    ! [C_171] :
      ( r2_relset_1('#skF_3','#skF_4',C_171,C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_64,c_1013])).

tff(c_1044,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_1032])).

tff(c_120,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_139,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_120])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_514,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_535,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_514])).

tff(c_669,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_672,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_669])).

tff(c_692,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_535,c_672])).

tff(c_700,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_140,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_120])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_536,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_514])).

tff(c_675,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_669])).

tff(c_695,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_536,c_675])).

tff(c_707,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_695])).

tff(c_1092,plain,(
    ! [A_181,B_182] :
      ( r2_hidden('#skF_2'(A_181,B_182),k1_relat_1(A_181))
      | B_182 = A_181
      | k1_relat_1(B_182) != k1_relat_1(A_181)
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182)
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1113,plain,(
    ! [B_182] :
      ( r2_hidden('#skF_2'('#skF_6',B_182),'#skF_3')
      | B_182 = '#skF_6'
      | k1_relat_1(B_182) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_1092])).

tff(c_1225,plain,(
    ! [B_189] :
      ( r2_hidden('#skF_2'('#skF_6',B_189),'#skF_3')
      | B_189 = '#skF_6'
      | k1_relat_1(B_189) != '#skF_3'
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_62,c_707,c_1113])).

tff(c_56,plain,(
    ! [E_46] :
      ( k1_funct_1('#skF_5',E_46) = k1_funct_1('#skF_6',E_46)
      | ~ r2_hidden(E_46,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1377,plain,(
    ! [B_202] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_202)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_202))
      | B_202 = '#skF_6'
      | k1_relat_1(B_202) != '#skF_3'
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202) ) ),
    inference(resolution,[status(thm)],[c_1225,c_56])).

tff(c_26,plain,(
    ! [B_20,A_16] :
      ( k1_funct_1(B_20,'#skF_2'(A_16,B_20)) != k1_funct_1(A_16,'#skF_2'(A_16,B_20))
      | B_20 = A_16
      | k1_relat_1(B_20) != k1_relat_1(A_16)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1384,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1377,c_26])).

tff(c_1391,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_68,c_700,c_140,c_62,c_700,c_707,c_1384])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1405,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_54])).

tff(c_1418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_1405])).

tff(c_1419,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1447,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1419,c_2])).

tff(c_1449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_1447])).

tff(c_1450,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_1478,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_2])).

tff(c_1480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_1478])).

tff(c_1482,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_98,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_1495,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1482,c_101])).

tff(c_1481,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_1488,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1481,c_101])).

tff(c_1537,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1488])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1529,plain,(
    ! [A_7] : m1_subset_1('#skF_5',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_14])).

tff(c_1627,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_1529])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1922,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( r2_relset_1(A_245,B_246,C_247,C_247)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2114,plain,(
    ! [A_274,B_275,C_276] :
      ( r2_relset_1(A_274,B_275,C_276,C_276)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1922])).

tff(c_2125,plain,(
    ! [A_274,B_275] : r2_relset_1(A_274,B_275,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1627,c_2114])).

tff(c_338,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_316])).

tff(c_1575,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1482,c_338])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1597,plain,(
    ! [A_211] :
      ( A_211 = '#skF_6'
      | ~ v1_xboole_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_1575,c_4])).

tff(c_1606,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1482,c_1597])).

tff(c_1549,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_54])).

tff(c_1736,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1549])).

tff(c_2129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_1736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:11:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.04/1.69  
% 4.04/1.69  %Foreground sorts:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Background operators:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Foreground operators:
% 4.04/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.69  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.04/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.04/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.04/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.04/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.04/1.69  tff('#skF_6', type, '#skF_6': $i).
% 4.04/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.04/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.04/1.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.04/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.04/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.04/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.04/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.04/1.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.04/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.04/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.04/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.04/1.69  
% 4.04/1.71  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.04/1.71  tff(f_100, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.04/1.71  tff(f_110, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.04/1.71  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.04/1.71  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.04/1.71  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.04/1.71  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.04/1.71  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.04/1.71  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.04/1.71  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.04/1.71  tff(f_43, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.04/1.71  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_316, plain, (![C_88, B_89, A_90]: (v1_xboole_0(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(B_89, A_90))) | ~v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.71  tff(c_337, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_316])).
% 4.04/1.71  tff(c_344, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_337])).
% 4.04/1.71  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_1013, plain, (![A_167, B_168, C_169, D_170]: (r2_relset_1(A_167, B_168, C_169, C_169) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.04/1.71  tff(c_1032, plain, (![C_171]: (r2_relset_1('#skF_3', '#skF_4', C_171, C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_64, c_1013])).
% 4.04/1.71  tff(c_1044, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_1032])).
% 4.04/1.71  tff(c_120, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.71  tff(c_139, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_120])).
% 4.04/1.71  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_514, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.04/1.71  tff(c_535, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_514])).
% 4.04/1.71  tff(c_669, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.04/1.71  tff(c_672, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_669])).
% 4.04/1.71  tff(c_692, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_535, c_672])).
% 4.04/1.71  tff(c_700, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_692])).
% 4.04/1.71  tff(c_140, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_120])).
% 4.04/1.71  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_536, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_514])).
% 4.04/1.71  tff(c_675, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_669])).
% 4.04/1.71  tff(c_695, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_536, c_675])).
% 4.04/1.71  tff(c_707, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_695])).
% 4.04/1.71  tff(c_1092, plain, (![A_181, B_182]: (r2_hidden('#skF_2'(A_181, B_182), k1_relat_1(A_181)) | B_182=A_181 | k1_relat_1(B_182)!=k1_relat_1(A_181) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/1.71  tff(c_1113, plain, (![B_182]: (r2_hidden('#skF_2'('#skF_6', B_182), '#skF_3') | B_182='#skF_6' | k1_relat_1(B_182)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_182) | ~v1_relat_1(B_182) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_707, c_1092])).
% 4.04/1.71  tff(c_1225, plain, (![B_189]: (r2_hidden('#skF_2'('#skF_6', B_189), '#skF_3') | B_189='#skF_6' | k1_relat_1(B_189)!='#skF_3' | ~v1_funct_1(B_189) | ~v1_relat_1(B_189))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_62, c_707, c_1113])).
% 4.04/1.71  tff(c_56, plain, (![E_46]: (k1_funct_1('#skF_5', E_46)=k1_funct_1('#skF_6', E_46) | ~r2_hidden(E_46, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_1377, plain, (![B_202]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_202))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_202)) | B_202='#skF_6' | k1_relat_1(B_202)!='#skF_3' | ~v1_funct_1(B_202) | ~v1_relat_1(B_202))), inference(resolution, [status(thm)], [c_1225, c_56])).
% 4.04/1.71  tff(c_26, plain, (![B_20, A_16]: (k1_funct_1(B_20, '#skF_2'(A_16, B_20))!=k1_funct_1(A_16, '#skF_2'(A_16, B_20)) | B_20=A_16 | k1_relat_1(B_20)!=k1_relat_1(A_16) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/1.71  tff(c_1384, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1377, c_26])).
% 4.04/1.71  tff(c_1391, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_68, c_700, c_140, c_62, c_700, c_707, c_1384])).
% 4.04/1.71  tff(c_54, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.04/1.71  tff(c_1405, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_54])).
% 4.04/1.71  tff(c_1418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1044, c_1405])).
% 4.04/1.71  tff(c_1419, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_695])).
% 4.04/1.71  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.04/1.71  tff(c_1447, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1419, c_2])).
% 4.04/1.71  tff(c_1449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_1447])).
% 4.04/1.71  tff(c_1450, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_692])).
% 4.04/1.71  tff(c_1478, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_2])).
% 4.04/1.71  tff(c_1480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_1478])).
% 4.04/1.71  tff(c_1482, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_337])).
% 4.04/1.71  tff(c_98, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.04/1.71  tff(c_101, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_2, c_98])).
% 4.04/1.71  tff(c_1495, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1482, c_101])).
% 4.04/1.71  tff(c_1481, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_337])).
% 4.04/1.71  tff(c_1488, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1481, c_101])).
% 4.04/1.71  tff(c_1537, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1488])).
% 4.04/1.71  tff(c_14, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.04/1.71  tff(c_1529, plain, (![A_7]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_14])).
% 4.04/1.71  tff(c_1627, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_1529])).
% 4.04/1.71  tff(c_12, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.04/1.71  tff(c_1922, plain, (![A_245, B_246, C_247, D_248]: (r2_relset_1(A_245, B_246, C_247, C_247) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.04/1.71  tff(c_2114, plain, (![A_274, B_275, C_276]: (r2_relset_1(A_274, B_275, C_276, C_276) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(resolution, [status(thm)], [c_12, c_1922])).
% 4.04/1.71  tff(c_2125, plain, (![A_274, B_275]: (r2_relset_1(A_274, B_275, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1627, c_2114])).
% 4.04/1.71  tff(c_338, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_316])).
% 4.04/1.71  tff(c_1575, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1482, c_338])).
% 4.04/1.71  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.04/1.71  tff(c_1597, plain, (![A_211]: (A_211='#skF_6' | ~v1_xboole_0(A_211))), inference(resolution, [status(thm)], [c_1575, c_4])).
% 4.04/1.71  tff(c_1606, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_1482, c_1597])).
% 4.04/1.71  tff(c_1549, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_54])).
% 4.04/1.71  tff(c_1736, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1549])).
% 4.04/1.71  tff(c_2129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2125, c_1736])).
% 4.04/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.71  
% 4.04/1.71  Inference rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Ref     : 1
% 4.04/1.71  #Sup     : 436
% 4.04/1.71  #Fact    : 0
% 4.04/1.71  #Define  : 0
% 4.04/1.71  #Split   : 6
% 4.04/1.71  #Chain   : 0
% 4.04/1.71  #Close   : 0
% 4.04/1.71  
% 4.04/1.71  Ordering : KBO
% 4.04/1.71  
% 4.04/1.71  Simplification rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Subsume      : 113
% 4.04/1.71  #Demod        : 558
% 4.04/1.71  #Tautology    : 244
% 4.04/1.71  #SimpNegUnit  : 9
% 4.04/1.71  #BackRed      : 118
% 4.04/1.71  
% 4.04/1.71  #Partial instantiations: 0
% 4.04/1.71  #Strategies tried      : 1
% 4.04/1.71  
% 4.04/1.71  Timing (in seconds)
% 4.04/1.71  ----------------------
% 4.04/1.71  Preprocessing        : 0.34
% 4.04/1.71  Parsing              : 0.18
% 4.04/1.71  CNF conversion       : 0.02
% 4.04/1.71  Main loop            : 0.59
% 4.04/1.71  Inferencing          : 0.19
% 4.04/1.71  Reduction            : 0.22
% 4.04/1.71  Demodulation         : 0.16
% 4.04/1.71  BG Simplification    : 0.03
% 4.04/1.71  Subsumption          : 0.10
% 4.04/1.71  Abstraction          : 0.03
% 4.04/1.71  MUC search           : 0.00
% 4.04/1.71  Cooper               : 0.00
% 4.04/1.71  Total                : 0.96
% 4.04/1.71  Index Insertion      : 0.00
% 4.04/1.71  Index Deletion       : 0.00
% 4.04/1.71  Index Matching       : 0.00
% 4.04/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
