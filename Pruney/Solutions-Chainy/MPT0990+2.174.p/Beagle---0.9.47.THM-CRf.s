%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:22 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 171 expanded)
%              Number of leaves         :   39 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 612 expanded)
%              Number of equality atoms :   77 ( 212 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_137,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_38,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_109,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_120,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_212,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_218,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_212])).

tff(c_226,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_120,c_218])).

tff(c_227,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_226])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_78])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_84])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_87,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_78])).

tff(c_96,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_140,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_149,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_140])).

tff(c_153,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_149])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_121,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_109])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_212])).

tff(c_230,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_121,c_221])).

tff(c_231,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_230])).

tff(c_36,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k1_relat_1(A_6)) != k5_relat_1(A_6,B_8)
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1163,plain,(
    ! [A_141,B_142] :
      ( k2_funct_1(A_141) = B_142
      | k6_partfun1(k1_relat_1(A_141)) != k5_relat_1(A_141,B_142)
      | k2_relat_1(A_141) != k1_relat_1(B_142)
      | ~ v2_funct_1(A_141)
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142)
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_1165,plain,(
    ! [B_142] :
      ( k2_funct_1('#skF_3') = B_142
      | k5_relat_1('#skF_3',B_142) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_142)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_1163])).

tff(c_1172,plain,(
    ! [B_143] :
      ( k2_funct_1('#skF_3') = B_143
      | k5_relat_1('#skF_3',B_143) != k6_partfun1('#skF_1')
      | k1_relat_1(B_143) != '#skF_2'
      | ~ v1_funct_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60,c_44,c_153,c_1165])).

tff(c_1181,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_93,c_1172])).

tff(c_1191,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_227,c_1181])).

tff(c_1192,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1191])).

tff(c_285,plain,(
    ! [F_84,A_81,C_83,B_85,E_86,D_82] :
      ( k4_relset_1(A_81,B_85,C_83,D_82,E_86,F_84) = k5_relat_1(E_86,F_84)
      | ~ m1_subset_1(F_84,k1_zfmisc_1(k2_zfmisc_1(C_83,D_82)))
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_81,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_295,plain,(
    ! [A_87,B_88,E_89] :
      ( k4_relset_1(A_87,B_88,'#skF_2','#skF_1',E_89,'#skF_4') = k5_relat_1(E_89,'#skF_4')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(resolution,[status(thm)],[c_50,c_285])).

tff(c_307,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_295])).

tff(c_398,plain,(
    ! [A_108,B_104,C_105,E_107,F_103,D_106] :
      ( m1_subset_1(k4_relset_1(A_108,B_104,C_105,D_106,E_107,F_103),k1_zfmisc_1(k2_zfmisc_1(A_108,D_106)))
      | ~ m1_subset_1(F_103,k1_zfmisc_1(k2_zfmisc_1(C_105,D_106)))
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_452,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_398])).

tff(c_480,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_452])).

tff(c_685,plain,(
    ! [B_115,A_110,D_114,C_112,E_113,F_111] :
      ( k1_partfun1(A_110,B_115,C_112,D_114,E_113,F_111) = k5_relat_1(E_113,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_112,D_114)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_115)))
      | ~ v1_funct_1(E_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_699,plain,(
    ! [A_110,B_115,E_113] :
      ( k1_partfun1(A_110,B_115,'#skF_2','#skF_1',E_113,'#skF_4') = k5_relat_1(E_113,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_115)))
      | ~ v1_funct_1(E_113) ) ),
    inference(resolution,[status(thm)],[c_50,c_685])).

tff(c_1052,plain,(
    ! [A_128,B_129,E_130] :
      ( k1_partfun1(A_128,B_129,'#skF_2','#skF_1',E_130,'#skF_4') = k5_relat_1(E_130,'#skF_4')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_699])).

tff(c_1088,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1052])).

tff(c_1104,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1088])).

tff(c_20,plain,(
    ! [A_31] : m1_subset_1(k6_relat_1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_61,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_255,plain,(
    ! [D_76,C_77,A_78,B_79] :
      ( D_76 = C_77
      | ~ r2_relset_1(A_78,B_79,C_77,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_263,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_255])).

tff(c_278,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_263])).

tff(c_284,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_1109,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_284])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1109])).

tff(c_1114,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_1481,plain,(
    ! [A_155,D_159,F_156,E_158,B_160,C_157] :
      ( k1_partfun1(A_155,B_160,C_157,D_159,E_158,F_156) = k5_relat_1(E_158,F_156)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(C_157,D_159)))
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_155,B_160)))
      | ~ v1_funct_1(E_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1495,plain,(
    ! [A_155,B_160,E_158] :
      ( k1_partfun1(A_155,B_160,'#skF_2','#skF_1',E_158,'#skF_4') = k5_relat_1(E_158,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_155,B_160)))
      | ~ v1_funct_1(E_158) ) ),
    inference(resolution,[status(thm)],[c_50,c_1481])).

tff(c_1723,plain,(
    ! [A_168,B_169,E_170] :
      ( k1_partfun1(A_168,B_169,'#skF_2','#skF_1',E_170,'#skF_4') = k5_relat_1(E_170,'#skF_4')
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_1(E_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1495])).

tff(c_1753,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1723])).

tff(c_1767,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1114,c_1753])).

tff(c_1769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1192,c_1767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.71  
% 3.70/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.71  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.70/1.71  
% 3.70/1.71  %Foreground sorts:
% 3.70/1.71  
% 3.70/1.71  
% 3.70/1.71  %Background operators:
% 3.70/1.71  
% 3.70/1.71  
% 3.70/1.71  %Foreground operators:
% 3.70/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.70/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.70/1.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.70/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.71  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.70/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.70/1.71  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.71  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.70/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.70/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.71  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.70/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.70/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.71  
% 3.70/1.73  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.70/1.73  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.70/1.73  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.70/1.73  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.70/1.73  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.70/1.73  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.70/1.73  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.70/1.73  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 3.70/1.73  tff(f_71, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.70/1.73  tff(f_57, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.70/1.73  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.70/1.73  tff(f_81, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.70/1.73  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.70/1.73  tff(c_38, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_109, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.70/1.73  tff(c_120, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_109])).
% 3.70/1.73  tff(c_212, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.70/1.73  tff(c_218, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_212])).
% 3.70/1.73  tff(c_226, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_120, c_218])).
% 3.70/1.73  tff(c_227, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_226])).
% 3.70/1.73  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.73  tff(c_78, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.70/1.73  tff(c_84, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_78])).
% 3.70/1.73  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_84])).
% 3.70/1.73  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_87, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_78])).
% 3.70/1.73  tff(c_96, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_87])).
% 3.70/1.73  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_140, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.70/1.73  tff(c_149, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_140])).
% 3.70/1.73  tff(c_153, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_149])).
% 3.70/1.73  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_121, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_109])).
% 3.70/1.73  tff(c_221, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_212])).
% 3.70/1.73  tff(c_230, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_121, c_221])).
% 3.70/1.73  tff(c_231, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_40, c_230])).
% 3.70/1.73  tff(c_36, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.70/1.73  tff(c_6, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k1_relat_1(A_6))!=k5_relat_1(A_6, B_8) | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.70/1.73  tff(c_1163, plain, (![A_141, B_142]: (k2_funct_1(A_141)=B_142 | k6_partfun1(k1_relat_1(A_141))!=k5_relat_1(A_141, B_142) | k2_relat_1(A_141)!=k1_relat_1(B_142) | ~v2_funct_1(A_141) | ~v1_funct_1(B_142) | ~v1_relat_1(B_142) | ~v1_funct_1(A_141) | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 3.70/1.73  tff(c_1165, plain, (![B_142]: (k2_funct_1('#skF_3')=B_142 | k5_relat_1('#skF_3', B_142)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_142) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_142) | ~v1_relat_1(B_142) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_1163])).
% 3.70/1.73  tff(c_1172, plain, (![B_143]: (k2_funct_1('#skF_3')=B_143 | k5_relat_1('#skF_3', B_143)!=k6_partfun1('#skF_1') | k1_relat_1(B_143)!='#skF_2' | ~v1_funct_1(B_143) | ~v1_relat_1(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60, c_44, c_153, c_1165])).
% 3.70/1.73  tff(c_1181, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_93, c_1172])).
% 3.70/1.73  tff(c_1191, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_227, c_1181])).
% 3.70/1.73  tff(c_1192, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_1191])).
% 3.70/1.73  tff(c_285, plain, (![F_84, A_81, C_83, B_85, E_86, D_82]: (k4_relset_1(A_81, B_85, C_83, D_82, E_86, F_84)=k5_relat_1(E_86, F_84) | ~m1_subset_1(F_84, k1_zfmisc_1(k2_zfmisc_1(C_83, D_82))) | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_81, B_85))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.73  tff(c_295, plain, (![A_87, B_88, E_89]: (k4_relset_1(A_87, B_88, '#skF_2', '#skF_1', E_89, '#skF_4')=k5_relat_1(E_89, '#skF_4') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(resolution, [status(thm)], [c_50, c_285])).
% 3.70/1.73  tff(c_307, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_295])).
% 3.70/1.73  tff(c_398, plain, (![A_108, B_104, C_105, E_107, F_103, D_106]: (m1_subset_1(k4_relset_1(A_108, B_104, C_105, D_106, E_107, F_103), k1_zfmisc_1(k2_zfmisc_1(A_108, D_106))) | ~m1_subset_1(F_103, k1_zfmisc_1(k2_zfmisc_1(C_105, D_106))) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_104))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.70/1.73  tff(c_452, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_307, c_398])).
% 3.70/1.73  tff(c_480, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_452])).
% 3.70/1.73  tff(c_685, plain, (![B_115, A_110, D_114, C_112, E_113, F_111]: (k1_partfun1(A_110, B_115, C_112, D_114, E_113, F_111)=k5_relat_1(E_113, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_112, D_114))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_115))) | ~v1_funct_1(E_113))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.70/1.73  tff(c_699, plain, (![A_110, B_115, E_113]: (k1_partfun1(A_110, B_115, '#skF_2', '#skF_1', E_113, '#skF_4')=k5_relat_1(E_113, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_115))) | ~v1_funct_1(E_113))), inference(resolution, [status(thm)], [c_50, c_685])).
% 3.70/1.73  tff(c_1052, plain, (![A_128, B_129, E_130]: (k1_partfun1(A_128, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')=k5_relat_1(E_130, '#skF_4') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_699])).
% 3.70/1.73  tff(c_1088, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1052])).
% 3.70/1.73  tff(c_1104, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1088])).
% 3.70/1.73  tff(c_20, plain, (![A_31]: (m1_subset_1(k6_relat_1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.70/1.73  tff(c_61, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_20])).
% 3.70/1.73  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.73  tff(c_255, plain, (![D_76, C_77, A_78, B_79]: (D_76=C_77 | ~r2_relset_1(A_78, B_79, C_77, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.73  tff(c_263, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_255])).
% 3.70/1.73  tff(c_278, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_263])).
% 3.70/1.73  tff(c_284, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_278])).
% 3.70/1.73  tff(c_1109, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_284])).
% 3.70/1.73  tff(c_1113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_480, c_1109])).
% 3.70/1.73  tff(c_1114, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_278])).
% 3.70/1.73  tff(c_1481, plain, (![A_155, D_159, F_156, E_158, B_160, C_157]: (k1_partfun1(A_155, B_160, C_157, D_159, E_158, F_156)=k5_relat_1(E_158, F_156) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(C_157, D_159))) | ~v1_funct_1(F_156) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_155, B_160))) | ~v1_funct_1(E_158))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.70/1.73  tff(c_1495, plain, (![A_155, B_160, E_158]: (k1_partfun1(A_155, B_160, '#skF_2', '#skF_1', E_158, '#skF_4')=k5_relat_1(E_158, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_155, B_160))) | ~v1_funct_1(E_158))), inference(resolution, [status(thm)], [c_50, c_1481])).
% 3.70/1.73  tff(c_1723, plain, (![A_168, B_169, E_170]: (k1_partfun1(A_168, B_169, '#skF_2', '#skF_1', E_170, '#skF_4')=k5_relat_1(E_170, '#skF_4') | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_1(E_170))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1495])).
% 3.70/1.73  tff(c_1753, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1723])).
% 3.70/1.73  tff(c_1767, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1114, c_1753])).
% 3.70/1.73  tff(c_1769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1192, c_1767])).
% 3.70/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.73  
% 3.70/1.73  Inference rules
% 3.70/1.73  ----------------------
% 3.70/1.73  #Ref     : 0
% 3.70/1.73  #Sup     : 403
% 3.70/1.73  #Fact    : 0
% 3.70/1.73  #Define  : 0
% 3.70/1.73  #Split   : 8
% 3.70/1.73  #Chain   : 0
% 3.70/1.73  #Close   : 0
% 3.70/1.73  
% 3.70/1.73  Ordering : KBO
% 3.70/1.73  
% 3.70/1.73  Simplification rules
% 3.70/1.73  ----------------------
% 3.70/1.73  #Subsume      : 1
% 3.70/1.73  #Demod        : 116
% 3.70/1.73  #Tautology    : 89
% 3.70/1.73  #SimpNegUnit  : 34
% 3.70/1.73  #BackRed      : 5
% 3.70/1.73  
% 3.70/1.73  #Partial instantiations: 0
% 3.70/1.73  #Strategies tried      : 1
% 3.70/1.73  
% 3.70/1.73  Timing (in seconds)
% 3.70/1.73  ----------------------
% 3.70/1.74  Preprocessing        : 0.35
% 3.70/1.74  Parsing              : 0.18
% 3.70/1.74  CNF conversion       : 0.02
% 3.70/1.74  Main loop            : 0.55
% 3.70/1.74  Inferencing          : 0.19
% 3.70/1.74  Reduction            : 0.18
% 3.70/1.74  Demodulation         : 0.13
% 3.70/1.74  BG Simplification    : 0.03
% 3.70/1.74  Subsumption          : 0.09
% 3.70/1.74  Abstraction          : 0.03
% 3.70/1.74  MUC search           : 0.00
% 3.70/1.74  Cooper               : 0.00
% 3.70/1.74  Total                : 0.94
% 3.70/1.74  Index Insertion      : 0.00
% 3.70/1.74  Index Deletion       : 0.00
% 3.70/1.74  Index Matching       : 0.00
% 3.70/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
