%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:01 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 169 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 ( 666 expanded)
%              Number of equality atoms :   73 ( 226 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_38,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_117,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_128,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_187,plain,(
    ! [B_61,A_62,C_63] :
      ( k1_xboole_0 = B_61
      | k1_relset_1(A_62,B_61,C_63) = A_62
      | ~ v1_funct_2(C_63,A_62,B_61)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_193,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_187])).

tff(c_201,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_128,c_193])).

tff(c_202,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_201])).

tff(c_77,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_89,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_103,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_112,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_116,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_112])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_129,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_117])).

tff(c_196,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_187])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_129,c_196])).

tff(c_206,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_205])).

tff(c_36,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k2_funct_1(A_1) = B_3
      | k6_relat_1(k1_relat_1(A_1)) != k5_relat_1(A_1,B_3)
      | k2_relat_1(A_1) != k1_relat_1(B_3)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_485,plain,(
    ! [A_106,B_107] :
      ( k2_funct_1(A_106) = B_107
      | k6_partfun1(k1_relat_1(A_106)) != k5_relat_1(A_106,B_107)
      | k2_relat_1(A_106) != k1_relat_1(B_107)
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_487,plain,(
    ! [B_107] :
      ( k2_funct_1('#skF_3') = B_107
      | k5_relat_1('#skF_3',B_107) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_107)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_485])).

tff(c_494,plain,(
    ! [B_108] :
      ( k2_funct_1('#skF_3') = B_108
      | k5_relat_1('#skF_3',B_108) != k6_partfun1('#skF_1')
      | k1_relat_1(B_108) != '#skF_2'
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_60,c_44,c_116,c_487])).

tff(c_503,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_494])).

tff(c_510,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_202,c_503])).

tff(c_511,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_510])).

tff(c_360,plain,(
    ! [A_96,C_92,E_94,F_91,B_95,D_93] :
      ( k1_partfun1(A_96,B_95,C_92,D_93,E_94,F_91) = k5_relat_1(E_94,F_91)
      | ~ m1_subset_1(F_91,k1_zfmisc_1(k2_zfmisc_1(C_92,D_93)))
      | ~ v1_funct_1(F_91)
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(E_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_364,plain,(
    ! [A_96,B_95,E_94] :
      ( k1_partfun1(A_96,B_95,'#skF_2','#skF_1',E_94,'#skF_4') = k5_relat_1(E_94,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(E_94) ) ),
    inference(resolution,[status(thm)],[c_50,c_360])).

tff(c_374,plain,(
    ! [A_97,B_98,E_99] :
      ( k1_partfun1(A_97,B_98,'#skF_2','#skF_1',E_99,'#skF_4') = k5_relat_1(E_99,'#skF_4')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_1(E_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_364])).

tff(c_383,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_374])).

tff(c_390,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_383])).

tff(c_32,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_246,plain,(
    ! [D_68,C_69,A_70,B_71] :
      ( D_68 = C_69
      | ~ r2_relset_1(A_70,B_71,C_69,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_254,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_269,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_254])).

tff(c_279,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_397,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_279])).

tff(c_409,plain,(
    ! [F_105,A_104,B_101,C_100,D_102,E_103] :
      ( m1_subset_1(k1_partfun1(A_104,B_101,C_100,D_102,E_103,F_105),k1_zfmisc_1(k2_zfmisc_1(A_104,D_102)))
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_100,D_102)))
      | ~ v1_funct_1(F_105)
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_101)))
      | ~ v1_funct_1(E_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_454,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_409])).

tff(c_473,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_454])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_473])).

tff(c_476,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_569,plain,(
    ! [E_126,F_123,A_128,D_125,B_127,C_124] :
      ( k1_partfun1(A_128,B_127,C_124,D_125,E_126,F_123) = k5_relat_1(E_126,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_124,D_125)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_1(E_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_573,plain,(
    ! [A_128,B_127,E_126] :
      ( k1_partfun1(A_128,B_127,'#skF_2','#skF_1',E_126,'#skF_4') = k5_relat_1(E_126,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_1(E_126) ) ),
    inference(resolution,[status(thm)],[c_50,c_569])).

tff(c_836,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_573])).

tff(c_854,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_836])).

tff(c_868,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_476,c_854])).

tff(c_870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_511,c_868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.67  
% 3.04/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.67  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.04/1.67  
% 3.04/1.67  %Foreground sorts:
% 3.04/1.67  
% 3.04/1.67  
% 3.04/1.67  %Background operators:
% 3.04/1.67  
% 3.04/1.67  
% 3.04/1.67  %Foreground operators:
% 3.04/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.04/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.04/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.04/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.04/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.04/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.04/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.04/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.04/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.04/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.04/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.67  
% 3.32/1.69  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.32/1.69  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.32/1.69  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.32/1.69  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.32/1.69  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.32/1.69  tff(f_108, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.32/1.69  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.32/1.69  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.32/1.69  tff(f_96, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.32/1.69  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.32/1.69  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.32/1.69  tff(c_38, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_117, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.32/1.69  tff(c_128, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_117])).
% 3.32/1.69  tff(c_187, plain, (![B_61, A_62, C_63]: (k1_xboole_0=B_61 | k1_relset_1(A_62, B_61, C_63)=A_62 | ~v1_funct_2(C_63, A_62, B_61) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.32/1.69  tff(c_193, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_187])).
% 3.32/1.69  tff(c_201, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_128, c_193])).
% 3.32/1.69  tff(c_202, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_201])).
% 3.32/1.69  tff(c_77, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.32/1.69  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_77])).
% 3.32/1.69  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_89, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_77])).
% 3.32/1.69  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_103, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.32/1.69  tff(c_112, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_103])).
% 3.32/1.69  tff(c_116, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_112])).
% 3.32/1.69  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_129, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_117])).
% 3.32/1.69  tff(c_196, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_187])).
% 3.32/1.69  tff(c_205, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_129, c_196])).
% 3.32/1.69  tff(c_206, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_40, c_205])).
% 3.32/1.69  tff(c_36, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.69  tff(c_2, plain, (![A_1, B_3]: (k2_funct_1(A_1)=B_3 | k6_relat_1(k1_relat_1(A_1))!=k5_relat_1(A_1, B_3) | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v2_funct_1(A_1) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.32/1.69  tff(c_485, plain, (![A_106, B_107]: (k2_funct_1(A_106)=B_107 | k6_partfun1(k1_relat_1(A_106))!=k5_relat_1(A_106, B_107) | k2_relat_1(A_106)!=k1_relat_1(B_107) | ~v2_funct_1(A_106) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2])).
% 3.32/1.69  tff(c_487, plain, (![B_107]: (k2_funct_1('#skF_3')=B_107 | k5_relat_1('#skF_3', B_107)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_107) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_485])).
% 3.32/1.69  tff(c_494, plain, (![B_108]: (k2_funct_1('#skF_3')=B_108 | k5_relat_1('#skF_3', B_108)!=k6_partfun1('#skF_1') | k1_relat_1(B_108)!='#skF_2' | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_60, c_44, c_116, c_487])).
% 3.32/1.69  tff(c_503, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_494])).
% 3.32/1.69  tff(c_510, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_202, c_503])).
% 3.32/1.69  tff(c_511, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_510])).
% 3.32/1.69  tff(c_360, plain, (![A_96, C_92, E_94, F_91, B_95, D_93]: (k1_partfun1(A_96, B_95, C_92, D_93, E_94, F_91)=k5_relat_1(E_94, F_91) | ~m1_subset_1(F_91, k1_zfmisc_1(k2_zfmisc_1(C_92, D_93))) | ~v1_funct_1(F_91) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(E_94))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.69  tff(c_364, plain, (![A_96, B_95, E_94]: (k1_partfun1(A_96, B_95, '#skF_2', '#skF_1', E_94, '#skF_4')=k5_relat_1(E_94, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(E_94))), inference(resolution, [status(thm)], [c_50, c_360])).
% 3.32/1.69  tff(c_374, plain, (![A_97, B_98, E_99]: (k1_partfun1(A_97, B_98, '#skF_2', '#skF_1', E_99, '#skF_4')=k5_relat_1(E_99, '#skF_4') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_1(E_99))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_364])).
% 3.32/1.69  tff(c_383, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_374])).
% 3.32/1.69  tff(c_390, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_383])).
% 3.32/1.69  tff(c_32, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.69  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.32/1.69  tff(c_246, plain, (![D_68, C_69, A_70, B_71]: (D_68=C_69 | ~r2_relset_1(A_70, B_71, C_69, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.32/1.69  tff(c_254, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_246])).
% 3.32/1.69  tff(c_269, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_254])).
% 3.32/1.69  tff(c_279, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_269])).
% 3.32/1.69  tff(c_397, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_279])).
% 3.32/1.69  tff(c_409, plain, (![F_105, A_104, B_101, C_100, D_102, E_103]: (m1_subset_1(k1_partfun1(A_104, B_101, C_100, D_102, E_103, F_105), k1_zfmisc_1(k2_zfmisc_1(A_104, D_102))) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_100, D_102))) | ~v1_funct_1(F_105) | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_101))) | ~v1_funct_1(E_103))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.32/1.69  tff(c_454, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_390, c_409])).
% 3.32/1.69  tff(c_473, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_454])).
% 3.32/1.69  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_473])).
% 3.32/1.69  tff(c_476, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_269])).
% 3.32/1.69  tff(c_569, plain, (![E_126, F_123, A_128, D_125, B_127, C_124]: (k1_partfun1(A_128, B_127, C_124, D_125, E_126, F_123)=k5_relat_1(E_126, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_124, D_125))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_1(E_126))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.69  tff(c_573, plain, (![A_128, B_127, E_126]: (k1_partfun1(A_128, B_127, '#skF_2', '#skF_1', E_126, '#skF_4')=k5_relat_1(E_126, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_1(E_126))), inference(resolution, [status(thm)], [c_50, c_569])).
% 3.32/1.69  tff(c_836, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_573])).
% 3.32/1.69  tff(c_854, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_836])).
% 3.32/1.69  tff(c_868, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_476, c_854])).
% 3.32/1.69  tff(c_870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_511, c_868])).
% 3.32/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.69  
% 3.32/1.69  Inference rules
% 3.32/1.69  ----------------------
% 3.32/1.69  #Ref     : 0
% 3.32/1.69  #Sup     : 173
% 3.32/1.69  #Fact    : 0
% 3.32/1.69  #Define  : 0
% 3.32/1.69  #Split   : 8
% 3.32/1.69  #Chain   : 0
% 3.32/1.69  #Close   : 0
% 3.32/1.69  
% 3.32/1.69  Ordering : KBO
% 3.32/1.69  
% 3.32/1.69  Simplification rules
% 3.32/1.69  ----------------------
% 3.32/1.69  #Subsume      : 2
% 3.32/1.69  #Demod        : 113
% 3.32/1.69  #Tautology    : 48
% 3.32/1.69  #SimpNegUnit  : 14
% 3.32/1.69  #BackRed      : 9
% 3.32/1.69  
% 3.32/1.69  #Partial instantiations: 0
% 3.32/1.69  #Strategies tried      : 1
% 3.32/1.69  
% 3.32/1.69  Timing (in seconds)
% 3.32/1.69  ----------------------
% 3.32/1.69  Preprocessing        : 0.42
% 3.32/1.69  Parsing              : 0.25
% 3.32/1.69  CNF conversion       : 0.02
% 3.32/1.69  Main loop            : 0.39
% 3.32/1.69  Inferencing          : 0.14
% 3.32/1.69  Reduction            : 0.13
% 3.32/1.69  Demodulation         : 0.09
% 3.32/1.69  BG Simplification    : 0.02
% 3.32/1.69  Subsumption          : 0.07
% 3.32/1.69  Abstraction          : 0.02
% 3.32/1.69  MUC search           : 0.00
% 3.32/1.69  Cooper               : 0.00
% 3.32/1.69  Total                : 0.85
% 3.32/1.69  Index Insertion      : 0.00
% 3.32/1.69  Index Deletion       : 0.00
% 3.32/1.69  Index Matching       : 0.00
% 3.32/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
