%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:40 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 723 expanded)
%              Number of leaves         :   44 ( 268 expanded)
%              Depth                    :   13
%              Number of atoms          :  266 (2572 expanded)
%              Number of equality atoms :   93 ( 663 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_147,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_75,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_75])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_140,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_147,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_140])).

tff(c_179,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_182,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_179])).

tff(c_188,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_147,c_182])).

tff(c_202,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_82,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_75])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_300,plain,(
    ! [B_110,C_111,A_112] :
      ( k1_funct_1(k5_relat_1(B_110,C_111),A_112) = k1_funct_1(C_111,k1_funct_1(B_110,A_112))
      | ~ r2_hidden(A_112,k1_relat_1(B_110))
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_318,plain,(
    ! [B_115,C_116,A_117] :
      ( k1_funct_1(k5_relat_1(B_115,C_116),A_117) = k1_funct_1(C_116,k1_funct_1(B_115,A_117))
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115)
      | v1_xboole_0(k1_relat_1(B_115))
      | ~ m1_subset_1(A_117,k1_relat_1(B_115)) ) ),
    inference(resolution,[status(thm)],[c_6,c_300])).

tff(c_320,plain,(
    ! [C_116,A_117] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_116),A_117) = k1_funct_1(C_116,k1_funct_1('#skF_4',A_117))
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_117,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_318])).

tff(c_322,plain,(
    ! [C_116,A_117] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_116),A_117) = k1_funct_1(C_116,k1_funct_1('#skF_4',A_117))
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_117,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_82,c_68,c_320])).

tff(c_323,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_323,c_2])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_329])).

tff(c_335,plain,(
    ! [C_116,A_117] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_116),A_117) = k1_funct_1(C_116,k1_funct_1('#skF_4',A_117))
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | ~ m1_subset_1(A_117,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_354,plain,(
    ! [F_124,B_121,D_123,C_122,A_120,E_125] :
      ( k1_partfun1(A_120,B_121,C_122,D_123,E_125,F_124) = k5_relat_1(E_125,F_124)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_122,D_123)))
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_358,plain,(
    ! [A_120,B_121,E_125] :
      ( k1_partfun1(A_120,B_121,'#skF_3','#skF_1',E_125,'#skF_5') = k5_relat_1(E_125,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_125) ) ),
    inference(resolution,[status(thm)],[c_60,c_354])).

tff(c_398,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_3','#skF_1',E_136,'#skF_5') = k5_relat_1(E_136,'#skF_5')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_358])).

tff(c_401,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_398])).

tff(c_407,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_401])).

tff(c_148,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_56,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_153,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_56])).

tff(c_378,plain,(
    ! [A_132,D_133,C_130,B_131,E_129] :
      ( k1_partfun1(A_132,B_131,B_131,C_130,D_133,E_129) = k8_funct_2(A_132,B_131,C_130,D_133,E_129)
      | k1_xboole_0 = B_131
      | ~ r1_tarski(k2_relset_1(A_132,B_131,D_133),k1_relset_1(B_131,C_130,E_129))
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(B_131,C_130)))
      | ~ v1_funct_1(E_129)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(D_133,A_132,B_131)
      | ~ v1_funct_1(D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_384,plain,(
    ! [A_132,D_133] :
      ( k1_partfun1(A_132,'#skF_3','#skF_3','#skF_1',D_133,'#skF_5') = k8_funct_2(A_132,'#skF_3','#skF_1',D_133,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_132,'#skF_3',D_133),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_132,'#skF_3')))
      | ~ v1_funct_2(D_133,A_132,'#skF_3')
      | ~ v1_funct_1(D_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_378])).

tff(c_389,plain,(
    ! [A_132,D_133] :
      ( k1_partfun1(A_132,'#skF_3','#skF_3','#skF_1',D_133,'#skF_5') = k8_funct_2(A_132,'#skF_3','#skF_1',D_133,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_132,'#skF_3',D_133),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_132,'#skF_3')))
      | ~ v1_funct_2(D_133,A_132,'#skF_3')
      | ~ v1_funct_1(D_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_384])).

tff(c_420,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_438,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_54])).

tff(c_93,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_100,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_93])).

tff(c_103,plain,(
    ! [B_73,A_74] :
      ( k7_relat_1(B_73,A_74) = B_73
      | ~ v4_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_103])).

tff(c_115,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_109])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_130,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(k1_relat_1(B_79),A_80)
      | k7_relat_1(B_79,A_80) != k1_xboole_0
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_xboole_0(B_3,A_2)
      | ~ r1_tarski(B_3,A_2)
      | v1_xboole_0(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [B_87,A_88] :
      ( ~ r1_tarski(k1_relat_1(B_87),A_88)
      | v1_xboole_0(k1_relat_1(B_87))
      | k7_relat_1(B_87,A_88) != k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_130,c_4])).

tff(c_164,plain,(
    ! [B_89,A_90] :
      ( v1_xboole_0(k1_relat_1(B_89))
      | k7_relat_1(B_89,A_90) != k1_xboole_0
      | ~ v4_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_168,plain,
    ( v1_xboole_0(k1_relat_1('#skF_4'))
    | k7_relat_1('#skF_4','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_164])).

tff(c_174,plain,
    ( v1_xboole_0(k1_relat_1('#skF_4'))
    | k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_115,c_168])).

tff(c_176,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_429,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_176])).

tff(c_40,plain,(
    ! [C_38,A_36] :
      ( k1_xboole_0 = C_38
      | ~ v1_funct_2(C_38,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_512,plain,(
    ! [C_152,A_153] :
      ( C_152 = '#skF_3'
      | ~ v1_funct_2(C_152,A_153,'#skF_3')
      | A_153 = '#skF_3'
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_420,c_420,c_420,c_40])).

tff(c_515,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_512])).

tff(c_518,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_515])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_429,c_518])).

tff(c_523,plain,(
    ! [A_154,D_155] :
      ( k1_partfun1(A_154,'#skF_3','#skF_3','#skF_1',D_155,'#skF_5') = k8_funct_2(A_154,'#skF_3','#skF_1',D_155,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_154,'#skF_3',D_155),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_zfmisc_1(A_154,'#skF_3')))
      | ~ v1_funct_2(D_155,A_154,'#skF_3')
      | ~ v1_funct_1(D_155) ) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_526,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_523])).

tff(c_529,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_407,c_526])).

tff(c_52,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_530,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_52])).

tff(c_537,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_530])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_83,c_62,c_537])).

tff(c_545,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_560,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_54])).

tff(c_551,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_176])).

tff(c_644,plain,(
    ! [C_183,A_184] :
      ( C_183 = '#skF_3'
      | ~ v1_funct_2(C_183,A_184,'#skF_3')
      | A_184 = '#skF_3'
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_184,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_545,c_545,c_545,c_40])).

tff(c_647,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_644])).

tff(c_650,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_647])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_560,c_551,c_650])).

tff(c_653,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_654,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_672,plain,(
    ! [A_185] :
      ( A_185 = '#skF_4'
      | ~ v1_xboole_0(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_2])).

tff(c_676,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_653,c_672])).

tff(c_678,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_653])).

tff(c_662,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_54])).

tff(c_679,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_147])).

tff(c_48,plain,(
    ! [B_37,A_36,C_38] :
      ( k1_xboole_0 = B_37
      | k1_relset_1(A_36,B_37,C_38) = A_36
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_794,plain,(
    ! [B_204,A_205,C_206] :
      ( B_204 = '#skF_4'
      | k1_relset_1(A_205,B_204,C_206) = A_205
      | ~ v1_funct_2(C_206,A_205,B_204)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_48])).

tff(c_797,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_794])).

tff(c_803,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_679,c_797])).

tff(c_804,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_662,c_803])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_817,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_70])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.52  
% 3.41/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.41/1.52  
% 3.41/1.52  %Foreground sorts:
% 3.41/1.52  
% 3.41/1.52  
% 3.41/1.52  %Background operators:
% 3.41/1.52  
% 3.41/1.52  
% 3.41/1.52  %Foreground operators:
% 3.41/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.41/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.41/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.41/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.41/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.41/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.41/1.52  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.41/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.41/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.41/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.41/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.41/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.41/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.41/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.41/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.41/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.52  
% 3.60/1.54  tff(f_182, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.60/1.54  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.60/1.54  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.60/1.54  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.60/1.54  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.60/1.54  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.60/1.54  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.60/1.54  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.60/1.54  tff(f_129, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 3.60/1.54  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.60/1.54  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.60/1.54  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.60/1.54  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.60/1.54  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.60/1.54  tff(c_58, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_75, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.60/1.54  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_75])).
% 3.60/1.54  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_140, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.60/1.54  tff(c_147, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_140])).
% 3.60/1.54  tff(c_179, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.60/1.54  tff(c_182, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_179])).
% 3.60/1.54  tff(c_188, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_147, c_182])).
% 3.60/1.54  tff(c_202, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_188])).
% 3.60/1.54  tff(c_82, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_75])).
% 3.60/1.54  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.60/1.54  tff(c_300, plain, (![B_110, C_111, A_112]: (k1_funct_1(k5_relat_1(B_110, C_111), A_112)=k1_funct_1(C_111, k1_funct_1(B_110, A_112)) | ~r2_hidden(A_112, k1_relat_1(B_110)) | ~v1_funct_1(C_111) | ~v1_relat_1(C_111) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.60/1.54  tff(c_318, plain, (![B_115, C_116, A_117]: (k1_funct_1(k5_relat_1(B_115, C_116), A_117)=k1_funct_1(C_116, k1_funct_1(B_115, A_117)) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115) | v1_xboole_0(k1_relat_1(B_115)) | ~m1_subset_1(A_117, k1_relat_1(B_115)))), inference(resolution, [status(thm)], [c_6, c_300])).
% 3.60/1.54  tff(c_320, plain, (![C_116, A_117]: (k1_funct_1(k5_relat_1('#skF_4', C_116), A_117)=k1_funct_1(C_116, k1_funct_1('#skF_4', A_117)) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_117, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_318])).
% 3.60/1.54  tff(c_322, plain, (![C_116, A_117]: (k1_funct_1(k5_relat_1('#skF_4', C_116), A_117)=k1_funct_1(C_116, k1_funct_1('#skF_4', A_117)) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_117, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_82, c_68, c_320])).
% 3.60/1.54  tff(c_323, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_322])).
% 3.60/1.54  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.60/1.54  tff(c_329, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_323, c_2])).
% 3.60/1.54  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_329])).
% 3.60/1.54  tff(c_335, plain, (![C_116, A_117]: (k1_funct_1(k5_relat_1('#skF_4', C_116), A_117)=k1_funct_1(C_116, k1_funct_1('#skF_4', A_117)) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116) | ~m1_subset_1(A_117, '#skF_2'))), inference(splitRight, [status(thm)], [c_322])).
% 3.60/1.54  tff(c_354, plain, (![F_124, B_121, D_123, C_122, A_120, E_125]: (k1_partfun1(A_120, B_121, C_122, D_123, E_125, F_124)=k5_relat_1(E_125, F_124) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_122, D_123))) | ~v1_funct_1(F_124) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_125))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.60/1.54  tff(c_358, plain, (![A_120, B_121, E_125]: (k1_partfun1(A_120, B_121, '#skF_3', '#skF_1', E_125, '#skF_5')=k5_relat_1(E_125, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_125))), inference(resolution, [status(thm)], [c_60, c_354])).
% 3.60/1.54  tff(c_398, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_3', '#skF_1', E_136, '#skF_5')=k5_relat_1(E_136, '#skF_5') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_358])).
% 3.60/1.54  tff(c_401, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_398])).
% 3.60/1.54  tff(c_407, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_401])).
% 3.60/1.54  tff(c_148, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_140])).
% 3.60/1.54  tff(c_56, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_153, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_56])).
% 3.60/1.54  tff(c_378, plain, (![A_132, D_133, C_130, B_131, E_129]: (k1_partfun1(A_132, B_131, B_131, C_130, D_133, E_129)=k8_funct_2(A_132, B_131, C_130, D_133, E_129) | k1_xboole_0=B_131 | ~r1_tarski(k2_relset_1(A_132, B_131, D_133), k1_relset_1(B_131, C_130, E_129)) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(B_131, C_130))) | ~v1_funct_1(E_129) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(D_133, A_132, B_131) | ~v1_funct_1(D_133))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.60/1.54  tff(c_384, plain, (![A_132, D_133]: (k1_partfun1(A_132, '#skF_3', '#skF_3', '#skF_1', D_133, '#skF_5')=k8_funct_2(A_132, '#skF_3', '#skF_1', D_133, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_132, '#skF_3', D_133), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_132, '#skF_3'))) | ~v1_funct_2(D_133, A_132, '#skF_3') | ~v1_funct_1(D_133))), inference(superposition, [status(thm), theory('equality')], [c_148, c_378])).
% 3.60/1.54  tff(c_389, plain, (![A_132, D_133]: (k1_partfun1(A_132, '#skF_3', '#skF_3', '#skF_1', D_133, '#skF_5')=k8_funct_2(A_132, '#skF_3', '#skF_1', D_133, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_132, '#skF_3', D_133), k1_relat_1('#skF_5')) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_132, '#skF_3'))) | ~v1_funct_2(D_133, A_132, '#skF_3') | ~v1_funct_1(D_133))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_384])).
% 3.60/1.54  tff(c_420, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_389])).
% 3.60/1.54  tff(c_438, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_54])).
% 3.60/1.54  tff(c_93, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.60/1.54  tff(c_100, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_93])).
% 3.60/1.54  tff(c_103, plain, (![B_73, A_74]: (k7_relat_1(B_73, A_74)=B_73 | ~v4_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.54  tff(c_109, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_103])).
% 3.60/1.54  tff(c_115, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_109])).
% 3.60/1.54  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.60/1.54  tff(c_130, plain, (![B_79, A_80]: (r1_xboole_0(k1_relat_1(B_79), A_80) | k7_relat_1(B_79, A_80)!=k1_xboole_0 | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.60/1.54  tff(c_4, plain, (![B_3, A_2]: (~r1_xboole_0(B_3, A_2) | ~r1_tarski(B_3, A_2) | v1_xboole_0(B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.60/1.54  tff(c_159, plain, (![B_87, A_88]: (~r1_tarski(k1_relat_1(B_87), A_88) | v1_xboole_0(k1_relat_1(B_87)) | k7_relat_1(B_87, A_88)!=k1_xboole_0 | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_130, c_4])).
% 3.60/1.54  tff(c_164, plain, (![B_89, A_90]: (v1_xboole_0(k1_relat_1(B_89)) | k7_relat_1(B_89, A_90)!=k1_xboole_0 | ~v4_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_10, c_159])).
% 3.60/1.54  tff(c_168, plain, (v1_xboole_0(k1_relat_1('#skF_4')) | k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_164])).
% 3.60/1.54  tff(c_174, plain, (v1_xboole_0(k1_relat_1('#skF_4')) | k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_115, c_168])).
% 3.60/1.54  tff(c_176, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_174])).
% 3.60/1.54  tff(c_429, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_176])).
% 3.60/1.54  tff(c_40, plain, (![C_38, A_36]: (k1_xboole_0=C_38 | ~v1_funct_2(C_38, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.60/1.54  tff(c_512, plain, (![C_152, A_153]: (C_152='#skF_3' | ~v1_funct_2(C_152, A_153, '#skF_3') | A_153='#skF_3' | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_420, c_420, c_420, c_40])).
% 3.60/1.54  tff(c_515, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_64, c_512])).
% 3.60/1.54  tff(c_518, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_515])).
% 3.60/1.54  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_438, c_429, c_518])).
% 3.60/1.54  tff(c_523, plain, (![A_154, D_155]: (k1_partfun1(A_154, '#skF_3', '#skF_3', '#skF_1', D_155, '#skF_5')=k8_funct_2(A_154, '#skF_3', '#skF_1', D_155, '#skF_5') | ~r1_tarski(k2_relset_1(A_154, '#skF_3', D_155), k1_relat_1('#skF_5')) | ~m1_subset_1(D_155, k1_zfmisc_1(k2_zfmisc_1(A_154, '#skF_3'))) | ~v1_funct_2(D_155, A_154, '#skF_3') | ~v1_funct_1(D_155))), inference(splitRight, [status(thm)], [c_389])).
% 3.60/1.54  tff(c_526, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_153, c_523])).
% 3.60/1.54  tff(c_529, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_407, c_526])).
% 3.60/1.54  tff(c_52, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_530, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_52])).
% 3.60/1.54  tff(c_537, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_530])).
% 3.60/1.54  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_83, c_62, c_537])).
% 3.60/1.54  tff(c_545, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_188])).
% 3.60/1.54  tff(c_560, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_545, c_54])).
% 3.60/1.54  tff(c_551, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_545, c_176])).
% 3.60/1.54  tff(c_644, plain, (![C_183, A_184]: (C_183='#skF_3' | ~v1_funct_2(C_183, A_184, '#skF_3') | A_184='#skF_3' | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_184, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_545, c_545, c_545, c_40])).
% 3.60/1.54  tff(c_647, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_64, c_644])).
% 3.60/1.54  tff(c_650, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_647])).
% 3.60/1.54  tff(c_652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_560, c_551, c_650])).
% 3.60/1.54  tff(c_653, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_174])).
% 3.60/1.54  tff(c_654, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_174])).
% 3.60/1.54  tff(c_672, plain, (![A_185]: (A_185='#skF_4' | ~v1_xboole_0(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_654, c_2])).
% 3.60/1.54  tff(c_676, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_653, c_672])).
% 3.60/1.54  tff(c_678, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_676, c_653])).
% 3.60/1.54  tff(c_662, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_54])).
% 3.60/1.54  tff(c_679, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_676, c_147])).
% 3.60/1.54  tff(c_48, plain, (![B_37, A_36, C_38]: (k1_xboole_0=B_37 | k1_relset_1(A_36, B_37, C_38)=A_36 | ~v1_funct_2(C_38, A_36, B_37) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.60/1.54  tff(c_794, plain, (![B_204, A_205, C_206]: (B_204='#skF_4' | k1_relset_1(A_205, B_204, C_206)=A_205 | ~v1_funct_2(C_206, A_205, B_204) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))))), inference(demodulation, [status(thm), theory('equality')], [c_654, c_48])).
% 3.60/1.54  tff(c_797, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_794])).
% 3.60/1.54  tff(c_803, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_679, c_797])).
% 3.60/1.54  tff(c_804, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_662, c_803])).
% 3.60/1.54  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.60/1.54  tff(c_817, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_804, c_70])).
% 3.60/1.54  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_678, c_817])).
% 3.60/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.54  
% 3.60/1.54  Inference rules
% 3.60/1.54  ----------------------
% 3.60/1.54  #Ref     : 0
% 3.60/1.54  #Sup     : 138
% 3.60/1.54  #Fact    : 0
% 3.60/1.54  #Define  : 0
% 3.60/1.54  #Split   : 12
% 3.60/1.54  #Chain   : 0
% 3.60/1.54  #Close   : 0
% 3.60/1.54  
% 3.60/1.54  Ordering : KBO
% 3.60/1.54  
% 3.60/1.54  Simplification rules
% 3.60/1.54  ----------------------
% 3.60/1.54  #Subsume      : 21
% 3.60/1.54  #Demod        : 203
% 3.60/1.54  #Tautology    : 61
% 3.60/1.54  #SimpNegUnit  : 16
% 3.60/1.54  #BackRed      : 57
% 3.60/1.54  
% 3.60/1.54  #Partial instantiations: 0
% 3.60/1.54  #Strategies tried      : 1
% 3.60/1.54  
% 3.60/1.54  Timing (in seconds)
% 3.60/1.54  ----------------------
% 3.60/1.55  Preprocessing        : 0.38
% 3.60/1.55  Parsing              : 0.21
% 3.60/1.55  CNF conversion       : 0.03
% 3.60/1.55  Main loop            : 0.39
% 3.60/1.55  Inferencing          : 0.14
% 3.60/1.55  Reduction            : 0.13
% 3.60/1.55  Demodulation         : 0.09
% 3.60/1.55  BG Simplification    : 0.03
% 3.60/1.55  Subsumption          : 0.07
% 3.60/1.55  Abstraction          : 0.02
% 3.60/1.55  MUC search           : 0.00
% 3.60/1.55  Cooper               : 0.00
% 3.60/1.55  Total                : 0.82
% 3.60/1.55  Index Insertion      : 0.00
% 3.60/1.55  Index Deletion       : 0.00
% 3.60/1.55  Index Matching       : 0.00
% 3.60/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
