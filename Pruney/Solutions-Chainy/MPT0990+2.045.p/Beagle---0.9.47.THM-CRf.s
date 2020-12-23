%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:02 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 665 expanded)
%              Number of leaves         :   40 ( 255 expanded)
%              Depth                    :   18
%              Number of atoms          :  298 (2886 expanded)
%              Number of equality atoms :  111 (1086 expanded)
%              Maximal formula depth    :   16 (   4 average)
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

tff(f_189,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_163,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_99,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_99])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_111,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_99])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_142,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_142])).

tff(c_250,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_256,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_250])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_153,c_256])).

tff(c_265,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_264])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_124,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_130,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_124])).

tff(c_136,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130])).

tff(c_42,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_10,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_relat_1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_533,plain,(
    ! [A_125,B_126] :
      ( k2_funct_1(A_125) = B_126
      | k6_partfun1(k2_relat_1(A_125)) != k5_relat_1(B_126,A_125)
      | k2_relat_1(B_126) != k1_relat_1(A_125)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_539,plain,(
    ! [B_126] :
      ( k2_funct_1('#skF_3') = B_126
      | k5_relat_1(B_126,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_126) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_533])).

tff(c_544,plain,(
    ! [B_127] :
      ( k2_funct_1('#skF_3') = B_127
      | k5_relat_1(B_127,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_127) != '#skF_1'
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_60,c_265,c_539])).

tff(c_547,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_544])).

tff(c_556,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_547])).

tff(c_557,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_556])).

tff(c_562,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_22,plain,(
    ! [A_19] : m1_subset_1(k6_relat_1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,(
    ! [A_19] : m1_subset_1(k6_partfun1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_113,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_120,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_77,c_113])).

tff(c_137,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_124])).

tff(c_459,plain,(
    ! [E_121,A_124,B_122,F_120,D_123,C_119] :
      ( m1_subset_1(k1_partfun1(A_124,B_122,C_119,D_123,E_121,F_120),k1_zfmisc_1(k2_zfmisc_1(A_124,D_123)))
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_119,D_123)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_280,plain,(
    ! [D_83,C_84,A_85,B_86] :
      ( D_83 = C_84
      | ~ r2_relset_1(A_85,B_86,C_84,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_288,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_280])).

tff(c_303,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_288])).

tff(c_317,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_478,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_459,c_317])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_478])).

tff(c_524,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_1074,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( k2_relset_1(A_172,B_173,C_174) = B_173
      | ~ r2_relset_1(B_173,B_173,k1_partfun1(B_173,A_172,A_172,B_173,D_175,C_174),k6_partfun1(B_173))
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(B_173,A_172)))
      | ~ v1_funct_2(D_175,B_173,A_172)
      | ~ v1_funct_1(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(C_174,A_172,B_173)
      | ~ v1_funct_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1080,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_1074])).

tff(c_1084,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_120,c_137,c_1080])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_562,c_1084])).

tff(c_1087,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_154,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_250])).

tff(c_268,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_154,c_259])).

tff(c_269,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_268])).

tff(c_1088,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_78,plain,(
    ! [A_3,B_5] :
      ( k2_funct_1(A_3) = B_5
      | k6_partfun1(k2_relat_1(A_3)) != k5_relat_1(B_5,A_3)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_1092,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_78])).

tff(c_1096,plain,(
    ! [B_5] :
      ( k2_funct_1('#skF_4') = B_5
      | k5_relat_1(B_5,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_5) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_70,c_269,c_1092])).

tff(c_1104,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1096])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_1528,plain,(
    ! [C_222,D_223,A_221,B_224,E_220] :
      ( k1_xboole_0 = C_222
      | v2_funct_1(E_220)
      | k2_relset_1(A_221,B_224,D_223) != B_224
      | ~ v2_funct_1(k1_partfun1(A_221,B_224,B_224,C_222,D_223,E_220))
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(B_224,C_222)))
      | ~ v1_funct_2(E_220,B_224,C_222)
      | ~ v1_funct_1(E_220)
      | ~ m1_subset_1(D_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_224)))
      | ~ v1_funct_2(D_223,A_221,B_224)
      | ~ v1_funct_1(D_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1530,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_1528])).

tff(c_1532,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_81,c_64,c_1530])).

tff(c_1534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1104,c_58,c_1532])).

tff(c_1536,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_1537,plain,(
    ! [B_225] :
      ( k2_funct_1('#skF_4') = B_225
      | k5_relat_1(B_225,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_225) != '#skF_2'
      | ~ v1_funct_1(B_225)
      | ~ v1_relat_1(B_225) ) ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_1543,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_1537])).

tff(c_1552,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_136,c_1543])).

tff(c_1554,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1552])).

tff(c_1587,plain,(
    ! [B_237,C_241,F_239,D_236,E_240,A_238] :
      ( k1_partfun1(A_238,B_237,C_241,D_236,E_240,F_239) = k5_relat_1(E_240,F_239)
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(C_241,D_236)))
      | ~ v1_funct_1(F_239)
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_237)))
      | ~ v1_funct_1(E_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1593,plain,(
    ! [A_238,B_237,E_240] :
      ( k1_partfun1(A_238,B_237,'#skF_2','#skF_1',E_240,'#skF_4') = k5_relat_1(E_240,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_237)))
      | ~ v1_funct_1(E_240) ) ),
    inference(resolution,[status(thm)],[c_66,c_1587])).

tff(c_1688,plain,(
    ! [A_253,B_254,E_255] :
      ( k1_partfun1(A_253,B_254,'#skF_2','#skF_1',E_255,'#skF_4') = k5_relat_1(E_255,'#skF_4')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_1(E_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1593])).

tff(c_1697,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1688])).

tff(c_1705,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_524,c_1697])).

tff(c_1707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1554,c_1705])).

tff(c_1708,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1552])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_1717,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1708,c_79])).

tff(c_1723,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_70,c_1536,c_269,c_1717])).

tff(c_1725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1087,c_1723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.82  
% 4.68/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.82  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.68/1.82  
% 4.68/1.82  %Foreground sorts:
% 4.68/1.82  
% 4.68/1.82  
% 4.68/1.82  %Background operators:
% 4.68/1.82  
% 4.68/1.82  
% 4.68/1.82  %Foreground operators:
% 4.68/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.68/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.68/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.68/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.68/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.68/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.82  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.68/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.82  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.68/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.68/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.82  
% 4.81/1.85  tff(f_189, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.81/1.85  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.81/1.85  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.81/1.85  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.81/1.85  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.81/1.85  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.81/1.85  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.81/1.85  tff(f_78, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.81/1.85  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.81/1.85  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.81/1.85  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.81/1.85  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.81/1.85  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 4.81/1.85  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.81/1.85  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.81/1.85  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_99, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.81/1.85  tff(c_112, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_99])).
% 4.81/1.85  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_111, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_99])).
% 4.81/1.85  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_142, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.81/1.85  tff(c_153, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_142])).
% 4.81/1.85  tff(c_250, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.81/1.85  tff(c_256, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_250])).
% 4.81/1.85  tff(c_264, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_153, c_256])).
% 4.81/1.85  tff(c_265, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_264])).
% 4.81/1.85  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_124, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.81/1.85  tff(c_130, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_124])).
% 4.81/1.85  tff(c_136, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_130])).
% 4.81/1.85  tff(c_42, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.81/1.85  tff(c_10, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_relat_1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.81/1.85  tff(c_533, plain, (![A_125, B_126]: (k2_funct_1(A_125)=B_126 | k6_partfun1(k2_relat_1(A_125))!=k5_relat_1(B_126, A_125) | k2_relat_1(B_126)!=k1_relat_1(A_125) | ~v2_funct_1(A_125) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 4.81/1.85  tff(c_539, plain, (![B_126]: (k2_funct_1('#skF_3')=B_126 | k5_relat_1(B_126, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_126)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_533])).
% 4.81/1.85  tff(c_544, plain, (![B_127]: (k2_funct_1('#skF_3')=B_127 | k5_relat_1(B_127, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_127)!='#skF_1' | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_60, c_265, c_539])).
% 4.81/1.85  tff(c_547, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_112, c_544])).
% 4.81/1.85  tff(c_556, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_547])).
% 4.81/1.85  tff(c_557, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_556])).
% 4.81/1.85  tff(c_562, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_557])).
% 4.81/1.85  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_22, plain, (![A_19]: (m1_subset_1(k6_relat_1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.81/1.85  tff(c_77, plain, (![A_19]: (m1_subset_1(k6_partfun1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 4.81/1.85  tff(c_113, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.81/1.85  tff(c_120, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_77, c_113])).
% 4.81/1.85  tff(c_137, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_124])).
% 4.81/1.85  tff(c_459, plain, (![E_121, A_124, B_122, F_120, D_123, C_119]: (m1_subset_1(k1_partfun1(A_124, B_122, C_119, D_123, E_121, F_120), k1_zfmisc_1(k2_zfmisc_1(A_124, D_123))) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_119, D_123))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.81/1.85  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_280, plain, (![D_83, C_84, A_85, B_86]: (D_83=C_84 | ~r2_relset_1(A_85, B_86, C_84, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.81/1.85  tff(c_288, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_280])).
% 4.81/1.85  tff(c_303, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_288])).
% 4.81/1.85  tff(c_317, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_303])).
% 4.81/1.85  tff(c_478, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_459, c_317])).
% 4.81/1.85  tff(c_523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_478])).
% 4.81/1.85  tff(c_524, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_303])).
% 4.81/1.85  tff(c_1074, plain, (![A_172, B_173, C_174, D_175]: (k2_relset_1(A_172, B_173, C_174)=B_173 | ~r2_relset_1(B_173, B_173, k1_partfun1(B_173, A_172, A_172, B_173, D_175, C_174), k6_partfun1(B_173)) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(B_173, A_172))) | ~v1_funct_2(D_175, B_173, A_172) | ~v1_funct_1(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(C_174, A_172, B_173) | ~v1_funct_1(C_174))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.81/1.85  tff(c_1080, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_524, c_1074])).
% 4.81/1.85  tff(c_1084, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_120, c_137, c_1080])).
% 4.81/1.85  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_562, c_1084])).
% 4.81/1.85  tff(c_1087, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_557])).
% 4.81/1.85  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.81/1.85  tff(c_154, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_142])).
% 4.81/1.85  tff(c_259, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_250])).
% 4.81/1.85  tff(c_268, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_154, c_259])).
% 4.81/1.85  tff(c_269, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_268])).
% 4.81/1.85  tff(c_1088, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_557])).
% 4.81/1.85  tff(c_78, plain, (![A_3, B_5]: (k2_funct_1(A_3)=B_5 | k6_partfun1(k2_relat_1(A_3))!=k5_relat_1(B_5, A_3) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 4.81/1.85  tff(c_1092, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1088, c_78])).
% 4.81/1.85  tff(c_1096, plain, (![B_5]: (k2_funct_1('#skF_4')=B_5 | k5_relat_1(B_5, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_5)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_70, c_269, c_1092])).
% 4.81/1.85  tff(c_1104, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1096])).
% 4.81/1.85  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.81/1.85  tff(c_81, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4])).
% 4.81/1.85  tff(c_1528, plain, (![C_222, D_223, A_221, B_224, E_220]: (k1_xboole_0=C_222 | v2_funct_1(E_220) | k2_relset_1(A_221, B_224, D_223)!=B_224 | ~v2_funct_1(k1_partfun1(A_221, B_224, B_224, C_222, D_223, E_220)) | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(B_224, C_222))) | ~v1_funct_2(E_220, B_224, C_222) | ~v1_funct_1(E_220) | ~m1_subset_1(D_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_224))) | ~v1_funct_2(D_223, A_221, B_224) | ~v1_funct_1(D_223))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.81/1.85  tff(c_1530, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_524, c_1528])).
% 4.81/1.85  tff(c_1532, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_81, c_64, c_1530])).
% 4.81/1.85  tff(c_1534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1104, c_58, c_1532])).
% 4.81/1.85  tff(c_1536, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1096])).
% 4.81/1.85  tff(c_1537, plain, (![B_225]: (k2_funct_1('#skF_4')=B_225 | k5_relat_1(B_225, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_225)!='#skF_2' | ~v1_funct_1(B_225) | ~v1_relat_1(B_225))), inference(splitRight, [status(thm)], [c_1096])).
% 4.81/1.85  tff(c_1543, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_111, c_1537])).
% 4.81/1.85  tff(c_1552, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_136, c_1543])).
% 4.81/1.85  tff(c_1554, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1552])).
% 4.81/1.85  tff(c_1587, plain, (![B_237, C_241, F_239, D_236, E_240, A_238]: (k1_partfun1(A_238, B_237, C_241, D_236, E_240, F_239)=k5_relat_1(E_240, F_239) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(C_241, D_236))) | ~v1_funct_1(F_239) | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_237))) | ~v1_funct_1(E_240))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.81/1.85  tff(c_1593, plain, (![A_238, B_237, E_240]: (k1_partfun1(A_238, B_237, '#skF_2', '#skF_1', E_240, '#skF_4')=k5_relat_1(E_240, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_237))) | ~v1_funct_1(E_240))), inference(resolution, [status(thm)], [c_66, c_1587])).
% 4.81/1.85  tff(c_1688, plain, (![A_253, B_254, E_255]: (k1_partfun1(A_253, B_254, '#skF_2', '#skF_1', E_255, '#skF_4')=k5_relat_1(E_255, '#skF_4') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_1(E_255))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1593])).
% 4.81/1.85  tff(c_1697, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1688])).
% 4.81/1.85  tff(c_1705, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_524, c_1697])).
% 4.81/1.85  tff(c_1707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1554, c_1705])).
% 4.81/1.85  tff(c_1708, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1552])).
% 4.81/1.85  tff(c_8, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.81/1.85  tff(c_79, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 4.81/1.85  tff(c_1717, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1708, c_79])).
% 4.81/1.85  tff(c_1723, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_70, c_1536, c_269, c_1717])).
% 4.81/1.85  tff(c_1725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1087, c_1723])).
% 4.81/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.85  
% 4.81/1.85  Inference rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Ref     : 0
% 4.81/1.85  #Sup     : 359
% 4.81/1.85  #Fact    : 0
% 4.81/1.85  #Define  : 0
% 4.81/1.85  #Split   : 18
% 4.81/1.85  #Chain   : 0
% 4.81/1.85  #Close   : 0
% 4.81/1.85  
% 4.81/1.85  Ordering : KBO
% 4.81/1.85  
% 4.81/1.85  Simplification rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Subsume      : 4
% 4.81/1.85  #Demod        : 274
% 4.81/1.85  #Tautology    : 99
% 4.81/1.85  #SimpNegUnit  : 33
% 4.81/1.85  #BackRed      : 14
% 4.81/1.85  
% 4.81/1.85  #Partial instantiations: 0
% 4.81/1.85  #Strategies tried      : 1
% 4.81/1.85  
% 4.81/1.85  Timing (in seconds)
% 4.81/1.85  ----------------------
% 4.81/1.85  Preprocessing        : 0.37
% 4.81/1.85  Parsing              : 0.19
% 4.81/1.85  CNF conversion       : 0.03
% 4.81/1.85  Main loop            : 0.70
% 4.81/1.85  Inferencing          : 0.25
% 4.81/1.85  Reduction            : 0.25
% 4.81/1.85  Demodulation         : 0.16
% 4.81/1.85  BG Simplification    : 0.03
% 4.81/1.85  Subsumption          : 0.12
% 4.81/1.85  Abstraction          : 0.03
% 4.81/1.85  MUC search           : 0.00
% 4.81/1.85  Cooper               : 0.00
% 4.81/1.85  Total                : 1.12
% 4.81/1.85  Index Insertion      : 0.00
% 4.81/1.85  Index Deletion       : 0.00
% 4.81/1.85  Index Matching       : 0.00
% 4.81/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
