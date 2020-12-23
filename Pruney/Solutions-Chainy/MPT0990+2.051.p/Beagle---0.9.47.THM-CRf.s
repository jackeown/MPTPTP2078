%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:03 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 174 expanded)
%              Number of leaves         :   36 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 ( 670 expanded)
%              Number of equality atoms :   73 ( 230 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_132,negated_conjecture,(
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

tff(f_82,axiom,(
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

tff(f_106,axiom,(
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

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_36,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_132,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_132])).

tff(c_208,plain,(
    ! [B_64,A_65,C_66] :
      ( k1_xboole_0 = B_64
      | k1_relset_1(A_65,B_64,C_66) = A_65
      | ~ v1_funct_2(C_66,A_65,B_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_208])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_143,c_214])).

tff(c_223,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_222])).

tff(c_75,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_75])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_87,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_100,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_109,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_113,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_109])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_144,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_132])).

tff(c_217,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_208])).

tff(c_226,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_144,c_217])).

tff(c_227,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_226])).

tff(c_34,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

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

tff(c_482,plain,(
    ! [A_106,B_107] :
      ( k2_funct_1(A_106) = B_107
      | k6_partfun1(k1_relat_1(A_106)) != k5_relat_1(A_106,B_107)
      | k2_relat_1(A_106) != k1_relat_1(B_107)
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_484,plain,(
    ! [B_107] :
      ( k2_funct_1('#skF_3') = B_107
      | k5_relat_1('#skF_3',B_107) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_107)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_482])).

tff(c_491,plain,(
    ! [B_108] :
      ( k2_funct_1('#skF_3') = B_108
      | k5_relat_1('#skF_3',B_108) != k6_partfun1('#skF_1')
      | k1_relat_1(B_108) != '#skF_2'
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_58,c_42,c_113,c_484])).

tff(c_500,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_491])).

tff(c_507,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_223,c_500])).

tff(c_508,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_507])).

tff(c_356,plain,(
    ! [D_92,A_95,B_94,F_90,C_91,E_93] :
      ( k1_partfun1(A_95,B_94,C_91,D_92,E_93,F_90) = k5_relat_1(E_93,F_90)
      | ~ m1_subset_1(F_90,k1_zfmisc_1(k2_zfmisc_1(C_91,D_92)))
      | ~ v1_funct_1(F_90)
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94)))
      | ~ v1_funct_1(E_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_360,plain,(
    ! [A_95,B_94,E_93] :
      ( k1_partfun1(A_95,B_94,'#skF_2','#skF_1',E_93,'#skF_4') = k5_relat_1(E_93,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94)))
      | ~ v1_funct_1(E_93) ) ),
    inference(resolution,[status(thm)],[c_48,c_356])).

tff(c_370,plain,(
    ! [A_96,B_97,E_98] :
      ( k1_partfun1(A_96,B_97,'#skF_2','#skF_1',E_98,'#skF_4') = k5_relat_1(E_98,'#skF_4')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_360])).

tff(c_379,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_370])).

tff(c_386,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_379])).

tff(c_14,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_251,plain,(
    ! [D_68,C_69,A_70,B_71] :
      ( D_68 = C_69
      | ~ r2_relset_1(A_70,B_71,C_69,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_257,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_251])).

tff(c_270,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_257])).

tff(c_275,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_393,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_275])).

tff(c_406,plain,(
    ! [B_104,C_102,E_105,A_100,D_101,F_103] :
      ( m1_subset_1(k1_partfun1(A_100,B_104,C_102,D_101,E_105,F_103),k1_zfmisc_1(k2_zfmisc_1(A_100,D_101)))
      | ~ m1_subset_1(F_103,k1_zfmisc_1(k2_zfmisc_1(C_102,D_101)))
      | ~ v1_funct_1(F_103)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_100,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_451,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_406])).

tff(c_470,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_451])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_470])).

tff(c_473,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_566,plain,(
    ! [E_126,F_123,A_128,D_125,B_127,C_124] :
      ( k1_partfun1(A_128,B_127,C_124,D_125,E_126,F_123) = k5_relat_1(E_126,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_124,D_125)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_1(E_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_570,plain,(
    ! [A_128,B_127,E_126] :
      ( k1_partfun1(A_128,B_127,'#skF_2','#skF_1',E_126,'#skF_4') = k5_relat_1(E_126,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_1(E_126) ) ),
    inference(resolution,[status(thm)],[c_48,c_566])).

tff(c_833,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_570])).

tff(c_851,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_833])).

tff(c_865,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_473,c_851])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.60  
% 3.42/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.61  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.42/1.61  
% 3.42/1.61  %Foreground sorts:
% 3.42/1.61  
% 3.42/1.61  
% 3.42/1.61  %Background operators:
% 3.42/1.61  
% 3.42/1.61  
% 3.42/1.61  %Foreground operators:
% 3.42/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.42/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.42/1.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.61  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.42/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.42/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.61  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.42/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.42/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.61  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.61  
% 3.42/1.63  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.42/1.63  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.63  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.42/1.63  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.42/1.63  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.42/1.63  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.42/1.63  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.42/1.63  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.42/1.63  tff(f_64, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.42/1.63  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.42/1.63  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.42/1.63  tff(c_36, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_132, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.42/1.63  tff(c_143, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_132])).
% 3.42/1.63  tff(c_208, plain, (![B_64, A_65, C_66]: (k1_xboole_0=B_64 | k1_relset_1(A_65, B_64, C_66)=A_65 | ~v1_funct_2(C_66, A_65, B_64) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.42/1.63  tff(c_214, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_208])).
% 3.42/1.63  tff(c_222, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_143, c_214])).
% 3.42/1.63  tff(c_223, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_222])).
% 3.42/1.63  tff(c_75, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.63  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_75])).
% 3.42/1.63  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_87, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_75])).
% 3.42/1.63  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_100, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.63  tff(c_109, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_100])).
% 3.42/1.63  tff(c_113, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_109])).
% 3.42/1.63  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_144, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_132])).
% 3.42/1.63  tff(c_217, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_208])).
% 3.42/1.63  tff(c_226, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_144, c_217])).
% 3.42/1.63  tff(c_227, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_38, c_226])).
% 3.42/1.63  tff(c_34, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.42/1.63  tff(c_2, plain, (![A_1, B_3]: (k2_funct_1(A_1)=B_3 | k6_relat_1(k1_relat_1(A_1))!=k5_relat_1(A_1, B_3) | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v2_funct_1(A_1) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.63  tff(c_482, plain, (![A_106, B_107]: (k2_funct_1(A_106)=B_107 | k6_partfun1(k1_relat_1(A_106))!=k5_relat_1(A_106, B_107) | k2_relat_1(A_106)!=k1_relat_1(B_107) | ~v2_funct_1(A_106) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2])).
% 3.42/1.63  tff(c_484, plain, (![B_107]: (k2_funct_1('#skF_3')=B_107 | k5_relat_1('#skF_3', B_107)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_107) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_482])).
% 3.42/1.63  tff(c_491, plain, (![B_108]: (k2_funct_1('#skF_3')=B_108 | k5_relat_1('#skF_3', B_108)!=k6_partfun1('#skF_1') | k1_relat_1(B_108)!='#skF_2' | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_58, c_42, c_113, c_484])).
% 3.42/1.63  tff(c_500, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_491])).
% 3.42/1.63  tff(c_507, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_223, c_500])).
% 3.42/1.63  tff(c_508, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_507])).
% 3.42/1.63  tff(c_356, plain, (![D_92, A_95, B_94, F_90, C_91, E_93]: (k1_partfun1(A_95, B_94, C_91, D_92, E_93, F_90)=k5_relat_1(E_93, F_90) | ~m1_subset_1(F_90, k1_zfmisc_1(k2_zfmisc_1(C_91, D_92))) | ~v1_funct_1(F_90) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))) | ~v1_funct_1(E_93))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.42/1.63  tff(c_360, plain, (![A_95, B_94, E_93]: (k1_partfun1(A_95, B_94, '#skF_2', '#skF_1', E_93, '#skF_4')=k5_relat_1(E_93, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))) | ~v1_funct_1(E_93))), inference(resolution, [status(thm)], [c_48, c_356])).
% 3.42/1.63  tff(c_370, plain, (![A_96, B_97, E_98]: (k1_partfun1(A_96, B_97, '#skF_2', '#skF_1', E_98, '#skF_4')=k5_relat_1(E_98, '#skF_4') | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_1(E_98))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_360])).
% 3.42/1.63  tff(c_379, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_370])).
% 3.42/1.63  tff(c_386, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_379])).
% 3.42/1.63  tff(c_14, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.63  tff(c_59, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 3.42/1.63  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.42/1.63  tff(c_251, plain, (![D_68, C_69, A_70, B_71]: (D_68=C_69 | ~r2_relset_1(A_70, B_71, C_69, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.42/1.63  tff(c_257, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_251])).
% 3.42/1.63  tff(c_270, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_257])).
% 3.42/1.63  tff(c_275, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_270])).
% 3.42/1.63  tff(c_393, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_275])).
% 3.42/1.63  tff(c_406, plain, (![B_104, C_102, E_105, A_100, D_101, F_103]: (m1_subset_1(k1_partfun1(A_100, B_104, C_102, D_101, E_105, F_103), k1_zfmisc_1(k2_zfmisc_1(A_100, D_101))) | ~m1_subset_1(F_103, k1_zfmisc_1(k2_zfmisc_1(C_102, D_101))) | ~v1_funct_1(F_103) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_100, B_104))) | ~v1_funct_1(E_105))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.42/1.63  tff(c_451, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_386, c_406])).
% 3.42/1.63  tff(c_470, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_451])).
% 3.42/1.63  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_393, c_470])).
% 3.42/1.63  tff(c_473, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_270])).
% 3.42/1.63  tff(c_566, plain, (![E_126, F_123, A_128, D_125, B_127, C_124]: (k1_partfun1(A_128, B_127, C_124, D_125, E_126, F_123)=k5_relat_1(E_126, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_124, D_125))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_1(E_126))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.42/1.63  tff(c_570, plain, (![A_128, B_127, E_126]: (k1_partfun1(A_128, B_127, '#skF_2', '#skF_1', E_126, '#skF_4')=k5_relat_1(E_126, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_1(E_126))), inference(resolution, [status(thm)], [c_48, c_566])).
% 3.42/1.63  tff(c_833, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_570])).
% 3.42/1.63  tff(c_851, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_833])).
% 3.42/1.63  tff(c_865, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_473, c_851])).
% 3.42/1.63  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_865])).
% 3.42/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.63  
% 3.42/1.63  Inference rules
% 3.42/1.63  ----------------------
% 3.42/1.63  #Ref     : 0
% 3.42/1.63  #Sup     : 173
% 3.42/1.63  #Fact    : 0
% 3.42/1.63  #Define  : 0
% 3.42/1.63  #Split   : 8
% 3.42/1.63  #Chain   : 0
% 3.42/1.63  #Close   : 0
% 3.42/1.63  
% 3.42/1.63  Ordering : KBO
% 3.42/1.63  
% 3.42/1.63  Simplification rules
% 3.42/1.63  ----------------------
% 3.42/1.63  #Subsume      : 2
% 3.42/1.63  #Demod        : 114
% 3.42/1.63  #Tautology    : 48
% 3.42/1.63  #SimpNegUnit  : 14
% 3.42/1.63  #BackRed      : 9
% 3.42/1.63  
% 3.42/1.63  #Partial instantiations: 0
% 3.42/1.63  #Strategies tried      : 1
% 3.42/1.63  
% 3.42/1.63  Timing (in seconds)
% 3.42/1.63  ----------------------
% 3.75/1.63  Preprocessing        : 0.36
% 3.75/1.63  Parsing              : 0.19
% 3.75/1.63  CNF conversion       : 0.02
% 3.75/1.63  Main loop            : 0.44
% 3.75/1.63  Inferencing          : 0.16
% 3.75/1.63  Reduction            : 0.15
% 3.75/1.63  Demodulation         : 0.10
% 3.75/1.63  BG Simplification    : 0.03
% 3.75/1.63  Subsumption          : 0.07
% 3.75/1.63  Abstraction          : 0.02
% 3.75/1.63  MUC search           : 0.00
% 3.75/1.63  Cooper               : 0.00
% 3.75/1.63  Total                : 0.85
% 3.75/1.63  Index Insertion      : 0.00
% 3.75/1.63  Index Deletion       : 0.00
% 3.75/1.64  Index Matching       : 0.00
% 3.75/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
