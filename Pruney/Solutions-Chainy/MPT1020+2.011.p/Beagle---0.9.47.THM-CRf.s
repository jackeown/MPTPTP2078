%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:51 EST 2020

% Result     : Theorem 9.39s
% Output     : CNFRefutation 9.39s
% Verified   : 
% Statistics : Number of formulae       :  238 (1160 expanded)
%              Number of leaves         :   48 ( 398 expanded)
%              Depth                    :   15
%              Number of atoms          :  417 (3245 expanded)
%              Number of equality atoms :  107 ( 419 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_173,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_47,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_7145,plain,(
    ! [C_473,B_474,A_475] :
      ( v1_xboole_0(C_473)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(B_474,A_475)))
      | ~ v1_xboole_0(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7162,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_7145])).

tff(c_7164,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7162])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_135,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_135])).

tff(c_448,plain,(
    ! [A_99,B_100,D_101] :
      ( r2_relset_1(A_99,B_100,D_101,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_461,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_448])).

tff(c_215,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_232,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_215])).

tff(c_463,plain,(
    ! [B_104,A_105] :
      ( k2_relat_1(B_104) = A_105
      | ~ v2_funct_2(B_104,A_105)
      | ~ v5_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_472,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_232,c_463])).

tff(c_484,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_472])).

tff(c_488,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_70,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_901,plain,(
    ! [C_139,B_140,A_141] :
      ( v2_funct_2(C_139,B_140)
      | ~ v3_funct_2(C_139,A_141,B_140)
      | ~ v1_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_920,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_901])).

tff(c_932,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_920])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_932])).

tff(c_935,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_154,plain,(
    ! [A_69] :
      ( k2_relat_1(A_69) = k1_xboole_0
      | k1_relat_1(A_69) != k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_152,c_154])).

tff(c_171,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_174,plain,(
    ! [A_70] :
      ( k1_relat_1(A_70) = k1_xboole_0
      | k2_relat_1(A_70) != k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_152,c_174])).

tff(c_193,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_183])).

tff(c_937,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_193])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_151,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_135])).

tff(c_231,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_215])).

tff(c_475,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_463])).

tff(c_487,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_475])).

tff(c_952,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_78,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1256,plain,(
    ! [C_161,B_162,A_163] :
      ( v2_funct_2(C_161,B_162)
      | ~ v3_funct_2(C_161,A_163,B_162)
      | ~ v1_funct_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1272,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1256])).

tff(c_1284,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1272])).

tff(c_1286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_1284])).

tff(c_1287,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_1306,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1316,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1306])).

tff(c_1323,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_1316])).

tff(c_50,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_32,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_83,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_32])).

tff(c_458,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_83,c_448])).

tff(c_1435,plain,(
    ! [C_172,A_173,B_174] :
      ( v2_funct_1(C_172)
      | ~ v3_funct_2(C_172,A_173,B_174)
      | ~ v1_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1451,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1435])).

tff(c_1463,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1451])).

tff(c_2238,plain,(
    ! [E_216,A_213,D_214,B_217,C_218,F_215] :
      ( m1_subset_1(k1_partfun1(A_213,B_217,C_218,D_214,E_216,F_215),k1_zfmisc_1(k2_zfmisc_1(A_213,D_214)))
      | ~ m1_subset_1(F_215,k1_zfmisc_1(k2_zfmisc_1(C_218,D_214)))
      | ~ v1_funct_1(F_215)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_213,B_217)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1604,plain,(
    ! [D_182,C_183,A_184,B_185] :
      ( D_182 = C_183
      | ~ r2_relset_1(A_184,B_185,C_183,D_182)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1618,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_66,c_1604])).

tff(c_1645,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1618])).

tff(c_1671,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1645])).

tff(c_2246,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2238,c_1671])).

tff(c_2282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_76,c_74,c_68,c_2246])).

tff(c_2283,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1645])).

tff(c_4262,plain,(
    ! [C_283,D_284,B_285,A_286] :
      ( k2_funct_1(C_283) = D_284
      | k1_xboole_0 = B_285
      | k1_xboole_0 = A_286
      | ~ v2_funct_1(C_283)
      | ~ r2_relset_1(A_286,A_286,k1_partfun1(A_286,B_285,B_285,A_286,C_283,D_284),k6_partfun1(A_286))
      | k2_relset_1(A_286,B_285,C_283) != B_285
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(B_285,A_286)))
      | ~ v1_funct_2(D_284,B_285,A_286)
      | ~ v1_funct_1(D_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_286,B_285)))
      | ~ v1_funct_2(C_283,A_286,B_285)
      | ~ v1_funct_1(C_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_4280,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2283,c_4262])).

tff(c_4288,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_68,c_1323,c_458,c_1463,c_4280])).

tff(c_4289,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_937,c_4288])).

tff(c_2611,plain,(
    ! [A_228,B_229] :
      ( k2_funct_2(A_228,B_229) = k2_funct_1(B_229)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(k2_zfmisc_1(A_228,A_228)))
      | ~ v3_funct_2(B_229,A_228,A_228)
      | ~ v1_funct_2(B_229,A_228,A_228)
      | ~ v1_funct_1(B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2621,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2611])).

tff(c_2631,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_2621])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_2635,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2631,c_64])).

tff(c_4291,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_2635])).

tff(c_4295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_4291])).

tff(c_4296,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_7092,plain,(
    ! [C_467,B_468,A_469] :
      ( v5_relat_1(C_467,B_468)
      | ~ m1_subset_1(C_467,k1_zfmisc_1(k2_zfmisc_1(A_469,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7109,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_7092])).

tff(c_8366,plain,(
    ! [B_555,A_556] :
      ( k2_relat_1(B_555) = A_556
      | ~ v2_funct_2(B_555,A_556)
      | ~ v5_relat_1(B_555,A_556)
      | ~ v1_relat_1(B_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8381,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7109,c_8366])).

tff(c_8399,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4296,c_8381])).

tff(c_8403,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8399])).

tff(c_4402,plain,(
    ! [C_301,B_302,A_303] :
      ( v1_xboole_0(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(B_302,A_303)))
      | ~ v1_xboole_0(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4419,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_4402])).

tff(c_4421,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4419])).

tff(c_4349,plain,(
    ! [C_291,B_292,A_293] :
      ( v5_relat_1(C_291,B_292)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4366,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4349])).

tff(c_4783,plain,(
    ! [B_330,A_331] :
      ( k2_relat_1(B_330) = A_331
      | ~ v2_funct_2(B_330,A_331)
      | ~ v5_relat_1(B_330,A_331)
      | ~ v1_relat_1(B_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4795,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4366,c_4783])).

tff(c_4810,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4296,c_4795])).

tff(c_4814,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4810])).

tff(c_5642,plain,(
    ! [C_376,B_377,A_378] :
      ( v2_funct_2(C_376,B_377)
      | ~ v3_funct_2(C_376,A_378,B_377)
      | ~ v1_funct_1(C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_378,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5654,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_5642])).

tff(c_5662,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_5654])).

tff(c_5664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4814,c_5662])).

tff(c_5665,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4810])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5690,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5665,c_2])).

tff(c_5694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4421,c_5690])).

tff(c_5696,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4419])).

tff(c_4420,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4402])).

tff(c_5712,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5696,c_4420])).

tff(c_105,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | B_59 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_111,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_2,c_105])).

tff(c_5718,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5712,c_111])).

tff(c_5695,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4419])).

tff(c_5702,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5695,c_111])).

tff(c_5763,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5718,c_5702])).

tff(c_5731,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_4296])).

tff(c_5811,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_5731])).

tff(c_170,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_154])).

tff(c_4306,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_4308,plain,(
    ! [A_287] :
      ( k1_relat_1(A_287) = k1_xboole_0
      | k2_relat_1(A_287) != k1_xboole_0
      | ~ v1_relat_1(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4320,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_4308])).

tff(c_4330,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4306,c_4320])).

tff(c_5726,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_4330])).

tff(c_5822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5811,c_5763,c_5763,c_5726])).

tff(c_5823,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_7108,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_7092])).

tff(c_8384,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7108,c_8366])).

tff(c_8402,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_5823,c_8384])).

tff(c_8404,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8402])).

tff(c_8797,plain,(
    ! [C_573,B_574,A_575] :
      ( v2_funct_2(C_573,B_574)
      | ~ v3_funct_2(C_573,A_575,B_574)
      | ~ v1_funct_1(C_573)
      | ~ m1_subset_1(C_573,k1_zfmisc_1(k2_zfmisc_1(A_575,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8806,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_8797])).

tff(c_8814,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_8806])).

tff(c_8816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8404,c_8814])).

tff(c_8817,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8402])).

tff(c_7501,plain,(
    ! [B_502,A_503] :
      ( k2_relat_1(B_502) = A_503
      | ~ v2_funct_2(B_502,A_503)
      | ~ v5_relat_1(B_502,A_503)
      | ~ v1_relat_1(B_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7516,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7108,c_7501])).

tff(c_7531,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_5823,c_7516])).

tff(c_7533,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7531])).

tff(c_7818,plain,(
    ! [C_515,B_516,A_517] :
      ( v2_funct_2(C_515,B_516)
      | ~ v3_funct_2(C_515,A_517,B_516)
      | ~ v1_funct_1(C_515)
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_517,B_516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7827,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_7818])).

tff(c_7835,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_7827])).

tff(c_7837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7533,c_7835])).

tff(c_7838,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7531])).

tff(c_7165,plain,(
    ! [B_476] :
      ( v2_funct_2(B_476,k2_relat_1(B_476))
      | ~ v5_relat_1(B_476,k2_relat_1(B_476))
      | ~ v1_relat_1(B_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7178,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4296,c_7165])).

tff(c_7187,plain,
    ( v2_funct_2('#skF_4',k1_xboole_0)
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4296,c_7178])).

tff(c_7302,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7187])).

tff(c_7841,plain,(
    ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7838,c_7302])).

tff(c_7868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7109,c_7841])).

tff(c_7869,plain,(
    v2_funct_2('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7187])).

tff(c_8826,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8817,c_7869])).

tff(c_8852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8403,c_8826])).

tff(c_8853,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8399])).

tff(c_8884,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8853,c_2])).

tff(c_8890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7164,c_8884])).

tff(c_8892,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7162])).

tff(c_7163,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_7145])).

tff(c_8900,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7163])).

tff(c_8909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8892,c_8900])).

tff(c_8910,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_7163])).

tff(c_8924,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8910,c_111])).

tff(c_8891,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7162])).

tff(c_8898,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8891,c_111])).

tff(c_8973,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_8898])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0('#skF_1'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_105])).

tff(c_119,plain,(
    ! [A_3] : '#skF_1'(A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_8])).

tff(c_8963,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8898,c_122])).

tff(c_9077,plain,(
    ! [A_587] : m1_subset_1('#skF_4',k1_zfmisc_1(A_587)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8973,c_8963])).

tff(c_28,plain,(
    ! [A_24,B_25,D_27] :
      ( r2_relset_1(A_24,B_25,D_27,D_27)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9101,plain,(
    ! [A_24,B_25] : r2_relset_1(A_24,B_25,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_9077,c_28])).

tff(c_8917,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8892,c_111])).

tff(c_8978,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_8917])).

tff(c_8991,plain,(
    v1_funct_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8978,c_8978,c_80])).

tff(c_9044,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8973,c_8991])).

tff(c_8990,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8978,c_8978,c_70])).

tff(c_8927,plain,(
    ! [C_576,A_577,B_578] :
      ( v1_xboole_0(C_576)
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_zfmisc_1(A_577,B_578)))
      | ~ v1_xboole_0(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9130,plain,(
    ! [A_590] :
      ( v1_xboole_0(k6_partfun1(A_590))
      | ~ v1_xboole_0(A_590) ) ),
    inference(resolution,[status(thm)],[c_83,c_8927])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8918,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_8892,c_4])).

tff(c_9066,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8978,c_8918])).

tff(c_9140,plain,(
    ! [A_593] :
      ( k6_partfun1(A_593) = '#skF_4'
      | ~ v1_xboole_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_9130,c_9066])).

tff(c_9148,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8910,c_9140])).

tff(c_14,plain,(
    ! [A_6] : k2_funct_1(k6_relat_1(A_6)) = k6_relat_1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [A_6] : k2_funct_1(k6_partfun1(A_6)) = k6_partfun1(A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_14])).

tff(c_9177,plain,(
    k6_partfun1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9148,c_84])).

tff(c_9186,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9148,c_9177])).

tff(c_9076,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8973,c_8963])).

tff(c_11029,plain,(
    ! [A_680,B_681] :
      ( k2_funct_2(A_680,B_681) = k2_funct_1(B_681)
      | ~ m1_subset_1(B_681,k1_zfmisc_1(k2_zfmisc_1(A_680,A_680)))
      | ~ v3_funct_2(B_681,A_680,A_680)
      | ~ v1_funct_2(B_681,A_680,A_680)
      | ~ v1_funct_1(B_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_11033,plain,(
    ! [A_680] :
      ( k2_funct_2(A_680,'#skF_4') = k2_funct_1('#skF_4')
      | ~ v3_funct_2('#skF_4',A_680,A_680)
      | ~ v1_funct_2('#skF_4',A_680,A_680)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9076,c_11029])).

tff(c_14118,plain,(
    ! [A_755] :
      ( k2_funct_2(A_755,'#skF_4') = '#skF_4'
      | ~ v3_funct_2('#skF_4',A_755,A_755)
      | ~ v1_funct_2('#skF_4',A_755,A_755) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9186,c_11033])).

tff(c_14121,plain,
    ( k2_funct_2('#skF_4','#skF_4') = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_8990,c_14118])).

tff(c_14124,plain,(
    k2_funct_2('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9044,c_14121])).

tff(c_8985,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8978,c_8978,c_8978,c_64])).

tff(c_9317,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8973,c_8985])).

tff(c_14125,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14124,c_9317])).

tff(c_14128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9101,c_14125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:59:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.39/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.05  
% 9.39/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.05  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 9.39/3.05  
% 9.39/3.05  %Foreground sorts:
% 9.39/3.05  
% 9.39/3.05  
% 9.39/3.05  %Background operators:
% 9.39/3.05  
% 9.39/3.05  
% 9.39/3.05  %Foreground operators:
% 9.39/3.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.39/3.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.39/3.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.39/3.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.39/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.39/3.05  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.39/3.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.39/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.39/3.05  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.39/3.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.39/3.05  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.39/3.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.39/3.05  tff('#skF_2', type, '#skF_2': $i).
% 9.39/3.05  tff('#skF_3', type, '#skF_3': $i).
% 9.39/3.05  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.39/3.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.39/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.39/3.05  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.39/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.39/3.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.39/3.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.39/3.05  tff('#skF_4', type, '#skF_4': $i).
% 9.39/3.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.39/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.39/3.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.39/3.05  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.39/3.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.39/3.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.39/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.39/3.05  
% 9.39/3.08  tff(f_205, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 9.39/3.08  tff(f_71, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.39/3.08  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.39/3.08  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.39/3.08  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.39/3.08  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.39/3.08  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 9.39/3.08  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 9.39/3.08  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.39/3.08  tff(f_129, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.39/3.08  tff(f_85, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 9.39/3.08  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.39/3.08  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 9.39/3.08  tff(f_127, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 9.39/3.08  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.39/3.08  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 9.39/3.08  tff(f_39, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 9.39/3.08  tff(f_64, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.39/3.08  tff(f_47, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 9.39/3.08  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_7145, plain, (![C_473, B_474, A_475]: (v1_xboole_0(C_473) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(B_474, A_475))) | ~v1_xboole_0(A_475))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.39/3.08  tff(c_7162, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_7145])).
% 9.39/3.08  tff(c_7164, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_7162])).
% 9.39/3.08  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_135, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.39/3.08  tff(c_152, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_135])).
% 9.39/3.08  tff(c_448, plain, (![A_99, B_100, D_101]: (r2_relset_1(A_99, B_100, D_101, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.39/3.08  tff(c_461, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_448])).
% 9.39/3.08  tff(c_215, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.39/3.08  tff(c_232, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_215])).
% 9.39/3.08  tff(c_463, plain, (![B_104, A_105]: (k2_relat_1(B_104)=A_105 | ~v2_funct_2(B_104, A_105) | ~v5_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.39/3.08  tff(c_472, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_232, c_463])).
% 9.39/3.08  tff(c_484, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_472])).
% 9.39/3.08  tff(c_488, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_484])).
% 9.39/3.08  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_70, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_901, plain, (![C_139, B_140, A_141]: (v2_funct_2(C_139, B_140) | ~v3_funct_2(C_139, A_141, B_140) | ~v1_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.39/3.08  tff(c_920, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_901])).
% 9.39/3.08  tff(c_932, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_920])).
% 9.39/3.08  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_932])).
% 9.39/3.08  tff(c_935, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_484])).
% 9.39/3.08  tff(c_154, plain, (![A_69]: (k2_relat_1(A_69)=k1_xboole_0 | k1_relat_1(A_69)!=k1_xboole_0 | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.39/3.08  tff(c_169, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_152, c_154])).
% 9.39/3.08  tff(c_171, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_169])).
% 9.39/3.08  tff(c_174, plain, (![A_70]: (k1_relat_1(A_70)=k1_xboole_0 | k2_relat_1(A_70)!=k1_xboole_0 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.39/3.08  tff(c_183, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_152, c_174])).
% 9.39/3.08  tff(c_193, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_171, c_183])).
% 9.39/3.08  tff(c_937, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_935, c_193])).
% 9.39/3.08  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_151, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_135])).
% 9.39/3.08  tff(c_231, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_215])).
% 9.39/3.08  tff(c_475, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_463])).
% 9.39/3.08  tff(c_487, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_475])).
% 9.39/3.08  tff(c_952, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_487])).
% 9.39/3.08  tff(c_78, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_1256, plain, (![C_161, B_162, A_163]: (v2_funct_2(C_161, B_162) | ~v3_funct_2(C_161, A_163, B_162) | ~v1_funct_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.39/3.08  tff(c_1272, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1256])).
% 9.39/3.08  tff(c_1284, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1272])).
% 9.39/3.08  tff(c_1286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_952, c_1284])).
% 9.39/3.08  tff(c_1287, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_487])).
% 9.39/3.08  tff(c_1306, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.39/3.08  tff(c_1316, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1306])).
% 9.39/3.08  tff(c_1323, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1287, c_1316])).
% 9.39/3.08  tff(c_50, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.39/3.08  tff(c_32, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.39/3.08  tff(c_83, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_32])).
% 9.39/3.08  tff(c_458, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_83, c_448])).
% 9.39/3.08  tff(c_1435, plain, (![C_172, A_173, B_174]: (v2_funct_1(C_172) | ~v3_funct_2(C_172, A_173, B_174) | ~v1_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.39/3.08  tff(c_1451, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1435])).
% 9.39/3.08  tff(c_1463, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1451])).
% 9.39/3.08  tff(c_2238, plain, (![E_216, A_213, D_214, B_217, C_218, F_215]: (m1_subset_1(k1_partfun1(A_213, B_217, C_218, D_214, E_216, F_215), k1_zfmisc_1(k2_zfmisc_1(A_213, D_214))) | ~m1_subset_1(F_215, k1_zfmisc_1(k2_zfmisc_1(C_218, D_214))) | ~v1_funct_1(F_215) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_213, B_217))) | ~v1_funct_1(E_216))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.39/3.08  tff(c_66, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_1604, plain, (![D_182, C_183, A_184, B_185]: (D_182=C_183 | ~r2_relset_1(A_184, B_185, C_183, D_182) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.39/3.08  tff(c_1618, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_66, c_1604])).
% 9.39/3.08  tff(c_1645, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1618])).
% 9.39/3.08  tff(c_1671, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1645])).
% 9.39/3.08  tff(c_2246, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2238, c_1671])).
% 9.39/3.08  tff(c_2282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_76, c_74, c_68, c_2246])).
% 9.39/3.08  tff(c_2283, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1645])).
% 9.39/3.08  tff(c_4262, plain, (![C_283, D_284, B_285, A_286]: (k2_funct_1(C_283)=D_284 | k1_xboole_0=B_285 | k1_xboole_0=A_286 | ~v2_funct_1(C_283) | ~r2_relset_1(A_286, A_286, k1_partfun1(A_286, B_285, B_285, A_286, C_283, D_284), k6_partfun1(A_286)) | k2_relset_1(A_286, B_285, C_283)!=B_285 | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1(B_285, A_286))) | ~v1_funct_2(D_284, B_285, A_286) | ~v1_funct_1(D_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_286, B_285))) | ~v1_funct_2(C_283, A_286, B_285) | ~v1_funct_1(C_283))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.39/3.08  tff(c_4280, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2283, c_4262])).
% 9.39/3.08  tff(c_4288, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_68, c_1323, c_458, c_1463, c_4280])).
% 9.39/3.08  tff(c_4289, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_937, c_4288])).
% 9.39/3.08  tff(c_2611, plain, (![A_228, B_229]: (k2_funct_2(A_228, B_229)=k2_funct_1(B_229) | ~m1_subset_1(B_229, k1_zfmisc_1(k2_zfmisc_1(A_228, A_228))) | ~v3_funct_2(B_229, A_228, A_228) | ~v1_funct_2(B_229, A_228, A_228) | ~v1_funct_1(B_229))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.39/3.08  tff(c_2621, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2611])).
% 9.39/3.08  tff(c_2631, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_2621])).
% 9.39/3.08  tff(c_64, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.39/3.08  tff(c_2635, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2631, c_64])).
% 9.39/3.08  tff(c_4291, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_2635])).
% 9.39/3.08  tff(c_4295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_4291])).
% 9.39/3.08  tff(c_4296, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_169])).
% 9.39/3.08  tff(c_7092, plain, (![C_467, B_468, A_469]: (v5_relat_1(C_467, B_468) | ~m1_subset_1(C_467, k1_zfmisc_1(k2_zfmisc_1(A_469, B_468))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.39/3.08  tff(c_7109, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_7092])).
% 9.39/3.08  tff(c_8366, plain, (![B_555, A_556]: (k2_relat_1(B_555)=A_556 | ~v2_funct_2(B_555, A_556) | ~v5_relat_1(B_555, A_556) | ~v1_relat_1(B_555))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.39/3.08  tff(c_8381, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_7109, c_8366])).
% 9.39/3.08  tff(c_8399, plain, (k1_xboole_0='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_4296, c_8381])).
% 9.39/3.08  tff(c_8403, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_8399])).
% 9.39/3.08  tff(c_4402, plain, (![C_301, B_302, A_303]: (v1_xboole_0(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(B_302, A_303))) | ~v1_xboole_0(A_303))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.39/3.08  tff(c_4419, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_4402])).
% 9.39/3.08  tff(c_4421, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4419])).
% 9.39/3.08  tff(c_4349, plain, (![C_291, B_292, A_293]: (v5_relat_1(C_291, B_292) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.39/3.08  tff(c_4366, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_4349])).
% 9.39/3.08  tff(c_4783, plain, (![B_330, A_331]: (k2_relat_1(B_330)=A_331 | ~v2_funct_2(B_330, A_331) | ~v5_relat_1(B_330, A_331) | ~v1_relat_1(B_330))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.39/3.08  tff(c_4795, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4366, c_4783])).
% 9.39/3.08  tff(c_4810, plain, (k1_xboole_0='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_4296, c_4795])).
% 9.39/3.08  tff(c_4814, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_4810])).
% 9.39/3.08  tff(c_5642, plain, (![C_376, B_377, A_378]: (v2_funct_2(C_376, B_377) | ~v3_funct_2(C_376, A_378, B_377) | ~v1_funct_1(C_376) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_378, B_377))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.39/3.08  tff(c_5654, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_5642])).
% 9.39/3.08  tff(c_5662, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_5654])).
% 9.39/3.08  tff(c_5664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4814, c_5662])).
% 9.39/3.08  tff(c_5665, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4810])).
% 9.39/3.08  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.39/3.08  tff(c_5690, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5665, c_2])).
% 9.39/3.08  tff(c_5694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4421, c_5690])).
% 9.39/3.08  tff(c_5696, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_4419])).
% 9.39/3.08  tff(c_4420, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4402])).
% 9.39/3.08  tff(c_5712, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5696, c_4420])).
% 9.39/3.08  tff(c_105, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | B_59=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.39/3.08  tff(c_111, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_2, c_105])).
% 9.39/3.08  tff(c_5718, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5712, c_111])).
% 9.39/3.08  tff(c_5695, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_4419])).
% 9.39/3.08  tff(c_5702, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5695, c_111])).
% 9.39/3.08  tff(c_5763, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5718, c_5702])).
% 9.39/3.08  tff(c_5731, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5702, c_4296])).
% 9.39/3.08  tff(c_5811, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_5731])).
% 9.39/3.08  tff(c_170, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_151, c_154])).
% 9.39/3.08  tff(c_4306, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_170])).
% 9.39/3.08  tff(c_4308, plain, (![A_287]: (k1_relat_1(A_287)=k1_xboole_0 | k2_relat_1(A_287)!=k1_xboole_0 | ~v1_relat_1(A_287))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.39/3.08  tff(c_4320, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_151, c_4308])).
% 9.39/3.08  tff(c_4330, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4306, c_4320])).
% 9.39/3.08  tff(c_5726, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5702, c_4330])).
% 9.39/3.08  tff(c_5822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5811, c_5763, c_5763, c_5726])).
% 9.39/3.08  tff(c_5823, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_170])).
% 9.39/3.08  tff(c_7108, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_7092])).
% 9.39/3.08  tff(c_8384, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7108, c_8366])).
% 9.39/3.08  tff(c_8402, plain, (k1_xboole_0='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_5823, c_8384])).
% 9.39/3.08  tff(c_8404, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_8402])).
% 9.39/3.08  tff(c_8797, plain, (![C_573, B_574, A_575]: (v2_funct_2(C_573, B_574) | ~v3_funct_2(C_573, A_575, B_574) | ~v1_funct_1(C_573) | ~m1_subset_1(C_573, k1_zfmisc_1(k2_zfmisc_1(A_575, B_574))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.39/3.08  tff(c_8806, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_8797])).
% 9.39/3.08  tff(c_8814, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_8806])).
% 9.39/3.08  tff(c_8816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8404, c_8814])).
% 9.39/3.08  tff(c_8817, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8402])).
% 9.39/3.08  tff(c_7501, plain, (![B_502, A_503]: (k2_relat_1(B_502)=A_503 | ~v2_funct_2(B_502, A_503) | ~v5_relat_1(B_502, A_503) | ~v1_relat_1(B_502))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.39/3.08  tff(c_7516, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7108, c_7501])).
% 9.39/3.08  tff(c_7531, plain, (k1_xboole_0='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_5823, c_7516])).
% 9.39/3.08  tff(c_7533, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_7531])).
% 9.39/3.08  tff(c_7818, plain, (![C_515, B_516, A_517]: (v2_funct_2(C_515, B_516) | ~v3_funct_2(C_515, A_517, B_516) | ~v1_funct_1(C_515) | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_517, B_516))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.39/3.08  tff(c_7827, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_7818])).
% 9.39/3.08  tff(c_7835, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_7827])).
% 9.39/3.08  tff(c_7837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7533, c_7835])).
% 9.39/3.08  tff(c_7838, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7531])).
% 9.39/3.08  tff(c_7165, plain, (![B_476]: (v2_funct_2(B_476, k2_relat_1(B_476)) | ~v5_relat_1(B_476, k2_relat_1(B_476)) | ~v1_relat_1(B_476))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.39/3.08  tff(c_7178, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4296, c_7165])).
% 9.39/3.08  tff(c_7187, plain, (v2_funct_2('#skF_4', k1_xboole_0) | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_4296, c_7178])).
% 9.39/3.08  tff(c_7302, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7187])).
% 9.39/3.08  tff(c_7841, plain, (~v5_relat_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7838, c_7302])).
% 9.39/3.08  tff(c_7868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7109, c_7841])).
% 9.39/3.08  tff(c_7869, plain, (v2_funct_2('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7187])).
% 9.39/3.08  tff(c_8826, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8817, c_7869])).
% 9.39/3.08  tff(c_8852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8403, c_8826])).
% 9.39/3.08  tff(c_8853, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8399])).
% 9.39/3.08  tff(c_8884, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8853, c_2])).
% 9.39/3.08  tff(c_8890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7164, c_8884])).
% 9.39/3.08  tff(c_8892, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_7162])).
% 9.39/3.08  tff(c_7163, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_7145])).
% 9.39/3.08  tff(c_8900, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_7163])).
% 9.39/3.08  tff(c_8909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8892, c_8900])).
% 9.39/3.08  tff(c_8910, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_7163])).
% 9.39/3.08  tff(c_8924, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8910, c_111])).
% 9.39/3.08  tff(c_8891, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_7162])).
% 9.39/3.08  tff(c_8898, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8891, c_111])).
% 9.39/3.08  tff(c_8973, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_8898])).
% 9.39/3.08  tff(c_6, plain, (![A_3]: (v1_xboole_0('#skF_1'(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.39/3.08  tff(c_112, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_2, c_105])).
% 9.39/3.08  tff(c_119, plain, (![A_3]: ('#skF_1'(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_112])).
% 9.39/3.08  tff(c_8, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.39/3.08  tff(c_122, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_8])).
% 9.39/3.08  tff(c_8963, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_8898, c_122])).
% 9.39/3.08  tff(c_9077, plain, (![A_587]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_587)))), inference(demodulation, [status(thm), theory('equality')], [c_8973, c_8963])).
% 9.39/3.08  tff(c_28, plain, (![A_24, B_25, D_27]: (r2_relset_1(A_24, B_25, D_27, D_27) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.39/3.08  tff(c_9101, plain, (![A_24, B_25]: (r2_relset_1(A_24, B_25, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_9077, c_28])).
% 9.39/3.08  tff(c_8917, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8892, c_111])).
% 9.39/3.08  tff(c_8978, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_8917])).
% 9.39/3.08  tff(c_8991, plain, (v1_funct_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8978, c_8978, c_80])).
% 9.39/3.08  tff(c_9044, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8973, c_8991])).
% 9.39/3.08  tff(c_8990, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8978, c_8978, c_70])).
% 9.39/3.08  tff(c_8927, plain, (![C_576, A_577, B_578]: (v1_xboole_0(C_576) | ~m1_subset_1(C_576, k1_zfmisc_1(k2_zfmisc_1(A_577, B_578))) | ~v1_xboole_0(A_577))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.39/3.08  tff(c_9130, plain, (![A_590]: (v1_xboole_0(k6_partfun1(A_590)) | ~v1_xboole_0(A_590))), inference(resolution, [status(thm)], [c_83, c_8927])).
% 9.39/3.08  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.39/3.08  tff(c_8918, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_8892, c_4])).
% 9.39/3.08  tff(c_9066, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8978, c_8918])).
% 9.39/3.08  tff(c_9140, plain, (![A_593]: (k6_partfun1(A_593)='#skF_4' | ~v1_xboole_0(A_593))), inference(resolution, [status(thm)], [c_9130, c_9066])).
% 9.39/3.08  tff(c_9148, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8910, c_9140])).
% 9.39/3.08  tff(c_14, plain, (![A_6]: (k2_funct_1(k6_relat_1(A_6))=k6_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.39/3.08  tff(c_84, plain, (![A_6]: (k2_funct_1(k6_partfun1(A_6))=k6_partfun1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_14])).
% 9.39/3.08  tff(c_9177, plain, (k6_partfun1('#skF_4')=k2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9148, c_84])).
% 9.39/3.08  tff(c_9186, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9148, c_9177])).
% 9.39/3.08  tff(c_9076, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_8973, c_8963])).
% 9.39/3.08  tff(c_11029, plain, (![A_680, B_681]: (k2_funct_2(A_680, B_681)=k2_funct_1(B_681) | ~m1_subset_1(B_681, k1_zfmisc_1(k2_zfmisc_1(A_680, A_680))) | ~v3_funct_2(B_681, A_680, A_680) | ~v1_funct_2(B_681, A_680, A_680) | ~v1_funct_1(B_681))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.39/3.08  tff(c_11033, plain, (![A_680]: (k2_funct_2(A_680, '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', A_680, A_680) | ~v1_funct_2('#skF_4', A_680, A_680) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9076, c_11029])).
% 9.39/3.08  tff(c_14118, plain, (![A_755]: (k2_funct_2(A_755, '#skF_4')='#skF_4' | ~v3_funct_2('#skF_4', A_755, A_755) | ~v1_funct_2('#skF_4', A_755, A_755))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9186, c_11033])).
% 9.39/3.08  tff(c_14121, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4' | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_8990, c_14118])).
% 9.39/3.08  tff(c_14124, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9044, c_14121])).
% 9.39/3.08  tff(c_8985, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8978, c_8978, c_8978, c_64])).
% 9.39/3.08  tff(c_9317, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8973, c_8985])).
% 9.39/3.08  tff(c_14125, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14124, c_9317])).
% 9.39/3.08  tff(c_14128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9101, c_14125])).
% 9.39/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.08  
% 9.39/3.08  Inference rules
% 9.39/3.08  ----------------------
% 9.39/3.08  #Ref     : 0
% 9.39/3.08  #Sup     : 3403
% 9.39/3.08  #Fact    : 0
% 9.39/3.08  #Define  : 0
% 9.39/3.08  #Split   : 59
% 9.39/3.08  #Chain   : 0
% 9.39/3.08  #Close   : 0
% 9.39/3.08  
% 9.39/3.08  Ordering : KBO
% 9.39/3.08  
% 9.39/3.08  Simplification rules
% 9.39/3.08  ----------------------
% 9.39/3.08  #Subsume      : 680
% 9.39/3.08  #Demod        : 3159
% 9.39/3.08  #Tautology    : 1188
% 9.39/3.08  #SimpNegUnit  : 51
% 9.39/3.08  #BackRed      : 449
% 9.39/3.08  
% 9.39/3.08  #Partial instantiations: 0
% 9.39/3.08  #Strategies tried      : 1
% 9.39/3.08  
% 9.39/3.08  Timing (in seconds)
% 9.39/3.08  ----------------------
% 9.39/3.09  Preprocessing        : 0.37
% 9.39/3.09  Parsing              : 0.20
% 9.39/3.09  CNF conversion       : 0.03
% 9.39/3.09  Main loop            : 1.90
% 9.39/3.09  Inferencing          : 0.57
% 9.39/3.09  Reduction            : 0.70
% 9.39/3.09  Demodulation         : 0.51
% 9.39/3.09  BG Simplification    : 0.07
% 9.39/3.09  Subsumption          : 0.41
% 9.39/3.09  Abstraction          : 0.08
% 9.39/3.09  MUC search           : 0.00
% 9.39/3.09  Cooper               : 0.00
% 9.39/3.09  Total                : 2.34
% 9.39/3.09  Index Insertion      : 0.00
% 9.39/3.09  Index Deletion       : 0.00
% 9.39/3.09  Index Matching       : 0.00
% 9.39/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
