%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:43 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 152 expanded)
%              Number of leaves         :   35 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 474 expanded)
%              Number of equality atoms :   46 ( 164 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,B,D) = B
                & k2_relset_1(B,C,E) = C )
             => ( C = k1_xboole_0
                | k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_353,plain,(
    ! [C_96,E_95,D_91,B_92,F_94,A_93] :
      ( k1_partfun1(A_93,B_92,C_96,D_91,E_95,F_94) = k5_relat_1(E_95,F_94)
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(C_96,D_91)))
      | ~ v1_funct_1(F_94)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_1(E_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_355,plain,(
    ! [A_93,B_92,E_95] :
      ( k1_partfun1(A_93,B_92,'#skF_2','#skF_3',E_95,'#skF_5') = k5_relat_1(E_95,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_1(E_95) ) ),
    inference(resolution,[status(thm)],[c_46,c_353])).

tff(c_364,plain,(
    ! [A_97,B_98,E_99] :
      ( k1_partfun1(A_97,B_98,'#skF_2','#skF_3',E_99,'#skF_5') = k5_relat_1(E_99,'#skF_5')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_1(E_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_355])).

tff(c_370,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_364])).

tff(c_376,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_370])).

tff(c_38,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_383,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_38])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_80,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_72,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_121,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_127,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_121])).

tff(c_131,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [A_4] :
      ( r1_tarski('#skF_2',A_4)
      | ~ v5_relat_1('#skF_4',A_4)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_6])).

tff(c_170,plain,(
    ! [A_59] :
      ( r1_tarski('#skF_2',A_59)
      | ~ v5_relat_1('#skF_4',A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_149])).

tff(c_174,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_170])).

tff(c_42,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_124,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_121])).

tff(c_129,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_124])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_103,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_196,plain,(
    ! [B_71,A_72,C_73] :
      ( k1_xboole_0 = B_71
      | k1_relset_1(A_72,B_71,C_73) = A_72
      | ~ v1_funct_2(C_73,A_72,B_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_196])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_110,c_199])).

tff(c_206,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_205])).

tff(c_183,plain,(
    ! [B_67,A_68] :
      ( k2_relat_1(k5_relat_1(B_67,A_68)) = k2_relat_1(A_68)
      | ~ r1_tarski(k1_relat_1(A_68),k2_relat_1(B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_186,plain,(
    ! [A_68] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_68)) = k2_relat_1(A_68)
      | ~ r1_tarski(k1_relat_1(A_68),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_183])).

tff(c_191,plain,(
    ! [A_68] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_68)) = k2_relat_1(A_68)
      | ~ r1_tarski(k1_relat_1(A_68),'#skF_2')
      | ~ v1_relat_1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_186])).

tff(c_217,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_191])).

tff(c_226,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_174,c_129,c_217])).

tff(c_401,plain,(
    ! [C_103,A_108,E_105,D_107,F_104,B_106] :
      ( m1_subset_1(k1_partfun1(A_108,B_106,C_103,D_107,E_105,F_104),k1_zfmisc_1(k2_zfmisc_1(A_108,D_107)))
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(C_103,D_107)))
      | ~ v1_funct_1(F_104)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_108,B_106)))
      | ~ v1_funct_1(E_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_453,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_401])).

tff(c_476,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_453])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_503,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_476,c_18])).

tff(c_541,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_503])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_383,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:29:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.44  
% 2.91/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.44  
% 2.91/1.44  %Foreground sorts:
% 2.91/1.44  
% 2.91/1.44  
% 2.91/1.44  %Background operators:
% 2.91/1.44  
% 2.91/1.44  
% 2.91/1.44  %Foreground operators:
% 2.91/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.91/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.91/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.91/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.44  
% 2.91/1.45  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 2.91/1.45  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.91/1.45  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.91/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.91/1.45  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.91/1.45  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.91/1.45  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.91/1.45  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.91/1.45  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.91/1.45  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.91/1.45  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.91/1.45  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_353, plain, (![C_96, E_95, D_91, B_92, F_94, A_93]: (k1_partfun1(A_93, B_92, C_96, D_91, E_95, F_94)=k5_relat_1(E_95, F_94) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(C_96, D_91))) | ~v1_funct_1(F_94) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_1(E_95))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.91/1.45  tff(c_355, plain, (![A_93, B_92, E_95]: (k1_partfun1(A_93, B_92, '#skF_2', '#skF_3', E_95, '#skF_5')=k5_relat_1(E_95, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_1(E_95))), inference(resolution, [status(thm)], [c_46, c_353])).
% 2.91/1.45  tff(c_364, plain, (![A_97, B_98, E_99]: (k1_partfun1(A_97, B_98, '#skF_2', '#skF_3', E_99, '#skF_5')=k5_relat_1(E_99, '#skF_5') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_1(E_99))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_355])).
% 2.91/1.45  tff(c_370, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_364])).
% 2.91/1.45  tff(c_376, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_370])).
% 2.91/1.45  tff(c_38, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_383, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_376, c_38])).
% 2.91/1.45  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.91/1.45  tff(c_66, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.45  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_66])).
% 2.91/1.45  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_69])).
% 2.91/1.45  tff(c_80, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.91/1.45  tff(c_88, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_80])).
% 2.91/1.45  tff(c_72, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_66])).
% 2.91/1.45  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_72])).
% 2.91/1.45  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_121, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.91/1.45  tff(c_127, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_121])).
% 2.91/1.45  tff(c_131, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_127])).
% 2.91/1.45  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.45  tff(c_149, plain, (![A_4]: (r1_tarski('#skF_2', A_4) | ~v5_relat_1('#skF_4', A_4) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_6])).
% 2.91/1.45  tff(c_170, plain, (![A_59]: (r1_tarski('#skF_2', A_59) | ~v5_relat_1('#skF_4', A_59))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_149])).
% 2.91/1.45  tff(c_174, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_170])).
% 2.91/1.45  tff(c_42, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_124, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_121])).
% 2.91/1.45  tff(c_129, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_124])).
% 2.91/1.45  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.91/1.45  tff(c_103, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.91/1.45  tff(c_110, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_103])).
% 2.91/1.45  tff(c_196, plain, (![B_71, A_72, C_73]: (k1_xboole_0=B_71 | k1_relset_1(A_72, B_71, C_73)=A_72 | ~v1_funct_2(C_73, A_72, B_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.91/1.45  tff(c_199, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_196])).
% 2.91/1.45  tff(c_205, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_110, c_199])).
% 2.91/1.45  tff(c_206, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_205])).
% 2.91/1.45  tff(c_183, plain, (![B_67, A_68]: (k2_relat_1(k5_relat_1(B_67, A_68))=k2_relat_1(A_68) | ~r1_tarski(k1_relat_1(A_68), k2_relat_1(B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.45  tff(c_186, plain, (![A_68]: (k2_relat_1(k5_relat_1('#skF_4', A_68))=k2_relat_1(A_68) | ~r1_tarski(k1_relat_1(A_68), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_131, c_183])).
% 2.91/1.46  tff(c_191, plain, (![A_68]: (k2_relat_1(k5_relat_1('#skF_4', A_68))=k2_relat_1(A_68) | ~r1_tarski(k1_relat_1(A_68), '#skF_2') | ~v1_relat_1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_186])).
% 2.91/1.46  tff(c_217, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_206, c_191])).
% 2.91/1.46  tff(c_226, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_174, c_129, c_217])).
% 2.91/1.46  tff(c_401, plain, (![C_103, A_108, E_105, D_107, F_104, B_106]: (m1_subset_1(k1_partfun1(A_108, B_106, C_103, D_107, E_105, F_104), k1_zfmisc_1(k2_zfmisc_1(A_108, D_107))) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(C_103, D_107))) | ~v1_funct_1(F_104) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_108, B_106))) | ~v1_funct_1(E_105))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.91/1.46  tff(c_453, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_376, c_401])).
% 2.91/1.46  tff(c_476, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_453])).
% 2.91/1.46  tff(c_18, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.91/1.46  tff(c_503, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_476, c_18])).
% 2.91/1.46  tff(c_541, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_503])).
% 2.91/1.46  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_383, c_541])).
% 2.91/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.46  
% 2.91/1.46  Inference rules
% 2.91/1.46  ----------------------
% 2.91/1.46  #Ref     : 0
% 2.91/1.46  #Sup     : 109
% 2.91/1.46  #Fact    : 0
% 2.91/1.46  #Define  : 0
% 2.91/1.46  #Split   : 5
% 2.91/1.46  #Chain   : 0
% 2.91/1.46  #Close   : 0
% 2.91/1.46  
% 2.91/1.46  Ordering : KBO
% 2.91/1.46  
% 2.91/1.46  Simplification rules
% 2.91/1.46  ----------------------
% 2.91/1.46  #Subsume      : 6
% 2.91/1.46  #Demod        : 68
% 2.91/1.46  #Tautology    : 32
% 2.91/1.46  #SimpNegUnit  : 5
% 2.91/1.46  #BackRed      : 5
% 2.91/1.46  
% 2.91/1.46  #Partial instantiations: 0
% 2.91/1.46  #Strategies tried      : 1
% 2.91/1.46  
% 2.91/1.46  Timing (in seconds)
% 2.91/1.46  ----------------------
% 3.06/1.46  Preprocessing        : 0.33
% 3.06/1.46  Parsing              : 0.17
% 3.06/1.46  CNF conversion       : 0.02
% 3.06/1.46  Main loop            : 0.31
% 3.06/1.46  Inferencing          : 0.11
% 3.06/1.46  Reduction            : 0.10
% 3.06/1.46  Demodulation         : 0.07
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.46  Subsumption          : 0.05
% 3.06/1.46  Abstraction          : 0.01
% 3.06/1.46  MUC search           : 0.00
% 3.06/1.46  Cooper               : 0.00
% 3.06/1.46  Total                : 0.68
% 3.06/1.46  Index Insertion      : 0.00
% 3.06/1.46  Index Deletion       : 0.00
% 3.06/1.46  Index Matching       : 0.00
% 3.06/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
