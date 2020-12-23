%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:23 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  238 (1399 expanded)
%              Number of leaves         :   47 ( 485 expanded)
%              Depth                    :   13
%              Number of atoms          :  443 (3951 expanded)
%              Number of equality atoms :  109 ( 730 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_132,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_154,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_80,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_72,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_189,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_66,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_88,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_900,plain,(
    ! [B_150,C_154,A_149,D_152,E_153,F_151] :
      ( k1_partfun1(A_149,B_150,C_154,D_152,E_153,F_151) = k5_relat_1(E_153,F_151)
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_154,D_152)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(E_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_907,plain,(
    ! [A_149,B_150,E_153] :
      ( k1_partfun1(A_149,B_150,'#skF_2','#skF_1',E_153,'#skF_4') = k5_relat_1(E_153,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(E_153) ) ),
    inference(resolution,[status(thm)],[c_76,c_900])).

tff(c_1159,plain,(
    ! [A_176,B_177,E_178] :
      ( k1_partfun1(A_176,B_177,'#skF_2','#skF_1',E_178,'#skF_4') = k5_relat_1(E_178,'#skF_4')
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(E_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_907])).

tff(c_1175,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1159])).

tff(c_1190,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1175])).

tff(c_60,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1301,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_60])).

tff(c_1305,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1301])).

tff(c_54,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_87,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_686,plain,(
    ! [D_120,C_121,A_122,B_123] :
      ( D_120 = C_121
      | ~ r2_relset_1(A_122,B_123,C_121,D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_692,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_686])).

tff(c_703,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_692])).

tff(c_2007,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1190,c_1190,c_703])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1361,plain,(
    ! [C_196,E_198,D_195,B_197,A_199] :
      ( k1_xboole_0 = C_196
      | v2_funct_1(D_195)
      | ~ v2_funct_1(k1_partfun1(A_199,B_197,B_197,C_196,D_195,E_198))
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(B_197,C_196)))
      | ~ v1_funct_2(E_198,B_197,C_196)
      | ~ v1_funct_1(E_198)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197)))
      | ~ v1_funct_2(D_195,A_199,B_197)
      | ~ v1_funct_1(D_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1363,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_1361])).

tff(c_1365,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_1363])).

tff(c_1366,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1365])).

tff(c_1373,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1366])).

tff(c_2010,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2007,c_1373])).

tff(c_2022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2010])).

tff(c_2023,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1366])).

tff(c_110,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_116,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_40])).

tff(c_42,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_89,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42])).

tff(c_127,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_89])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,(
    ! [A_64] : m1_subset_1(k6_partfun1(A_64),k1_zfmisc_1(k2_zfmisc_1(A_64,A_64))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54])).

tff(c_204,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_200])).

tff(c_212,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_204])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_334,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_391,plain,(
    ! [C_86,B_87] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_398,plain,(
    ! [B_87] : v5_relat_1(k1_xboole_0,B_87) ),
    inference(resolution,[status(thm)],[c_212,c_391])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_402,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v5_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_416,plain,(
    ! [A_90] :
      ( r1_tarski(k1_xboole_0,A_90)
      | ~ v5_relat_1(k1_xboole_0,A_90)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_402])).

tff(c_423,plain,(
    ! [A_90] : r1_tarski(k1_xboole_0,A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_398,c_416])).

tff(c_2045,plain,(
    ! [A_90] : r1_tarski('#skF_1',A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2023,c_423])).

tff(c_2052,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2023,c_2023,c_16])).

tff(c_217,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | ~ m1_subset_1(A_65,k1_zfmisc_1(B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_234,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_217])).

tff(c_255,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_265,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_234,c_255])).

tff(c_378,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_2303,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_378])).

tff(c_2308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2045,c_2303])).

tff(c_2309,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_2312,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2309,c_82])).

tff(c_2952,plain,(
    ! [D_301,C_302,A_303,B_304] :
      ( D_301 = C_302
      | ~ r2_relset_1(A_303,B_304,C_302,D_301)
      | ~ m1_subset_1(D_301,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304)))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2964,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_2952])).

tff(c_2986,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_2964])).

tff(c_3048,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2986])).

tff(c_3482,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3048])).

tff(c_3489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2312,c_2309,c_80,c_76,c_3482])).

tff(c_3490,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2986])).

tff(c_4343,plain,(
    ! [C_447,A_450,D_446,B_448,E_449] :
      ( k1_xboole_0 = C_447
      | v2_funct_1(D_446)
      | ~ v2_funct_1(k1_partfun1(A_450,B_448,B_448,C_447,D_446,E_449))
      | ~ m1_subset_1(E_449,k1_zfmisc_1(k2_zfmisc_1(B_448,C_447)))
      | ~ v1_funct_2(E_449,B_448,C_447)
      | ~ v1_funct_1(E_449)
      | ~ m1_subset_1(D_446,k1_zfmisc_1(k2_zfmisc_1(A_450,B_448)))
      | ~ v1_funct_2(D_446,A_450,B_448)
      | ~ v1_funct_1(D_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4345,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3490,c_4343])).

tff(c_4347,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_2312,c_2309,c_80,c_78,c_76,c_88,c_4345])).

tff(c_4348,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_4347])).

tff(c_2649,plain,(
    ! [C_263,B_264] :
      ( v5_relat_1(C_263,B_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_2656,plain,(
    ! [B_264] : v5_relat_1(k1_xboole_0,B_264) ),
    inference(resolution,[status(thm)],[c_212,c_2649])).

tff(c_2338,plain,(
    ! [B_230,A_231] :
      ( r1_tarski(k2_relat_1(B_230),A_231)
      | ~ v5_relat_1(B_230,A_231)
      | ~ v1_relat_1(B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2352,plain,(
    ! [A_231] :
      ( r1_tarski(k1_xboole_0,A_231)
      | ~ v5_relat_1(k1_xboole_0,A_231)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2338])).

tff(c_2359,plain,(
    ! [A_231] :
      ( r1_tarski(k1_xboole_0,A_231)
      | ~ v5_relat_1(k1_xboole_0,A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2352])).

tff(c_2658,plain,(
    ! [A_231] : r1_tarski(k1_xboole_0,A_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2656,c_2359])).

tff(c_4371,plain,(
    ! [A_231] : r1_tarski('#skF_1',A_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4348,c_2658])).

tff(c_4381,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4348,c_4348,c_14])).

tff(c_233,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_217])).

tff(c_266,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_233,c_255])).

tff(c_2373,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_4632,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4381,c_2373])).

tff(c_4637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4371,c_4632])).

tff(c_4638,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_4641,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4638,c_76])).

tff(c_5737,plain,(
    ! [B_576,D_575,E_577,C_580,F_579,A_578] :
      ( m1_subset_1(k1_partfun1(A_578,B_576,C_580,D_575,E_577,F_579),k1_zfmisc_1(k2_zfmisc_1(A_578,D_575)))
      | ~ m1_subset_1(F_579,k1_zfmisc_1(k2_zfmisc_1(C_580,D_575)))
      | ~ v1_funct_1(F_579)
      | ~ m1_subset_1(E_577,k1_zfmisc_1(k2_zfmisc_1(A_578,B_576)))
      | ~ v1_funct_1(E_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5346,plain,(
    ! [D_528,C_529,A_530,B_531] :
      ( D_528 = C_529
      | ~ r2_relset_1(A_530,B_531,C_529,D_528)
      | ~ m1_subset_1(D_528,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531)))
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5352,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_5346])).

tff(c_5363,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_5352])).

tff(c_5387,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5363])).

tff(c_5742,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5737,c_5387])).

tff(c_5775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2312,c_2309,c_80,c_4641,c_4638,c_5742])).

tff(c_5776,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5363])).

tff(c_6450,plain,(
    ! [E_663,D_660,B_662,C_661,A_664] :
      ( k1_xboole_0 = C_661
      | v2_funct_1(D_660)
      | ~ v2_funct_1(k1_partfun1(A_664,B_662,B_662,C_661,D_660,E_663))
      | ~ m1_subset_1(E_663,k1_zfmisc_1(k2_zfmisc_1(B_662,C_661)))
      | ~ v1_funct_2(E_663,B_662,C_661)
      | ~ v1_funct_1(E_663)
      | ~ m1_subset_1(D_660,k1_zfmisc_1(k2_zfmisc_1(A_664,B_662)))
      | ~ v1_funct_2(D_660,A_664,B_662)
      | ~ v1_funct_1(D_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6452,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5776,c_6450])).

tff(c_6454,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_2312,c_2309,c_80,c_78,c_4641,c_4638,c_88,c_6452])).

tff(c_6455,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_6454])).

tff(c_5162,plain,(
    ! [C_512,B_513] :
      ( v5_relat_1(C_512,B_513)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_5169,plain,(
    ! [B_513] : v5_relat_1(k1_xboole_0,B_513) ),
    inference(resolution,[status(thm)],[c_212,c_5162])).

tff(c_5171,plain,(
    ! [A_231] : r1_tarski(k1_xboole_0,A_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_2359])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4978,plain,(
    ! [C_497] :
      ( v5_relat_1(C_497,'#skF_1')
      | ~ m1_subset_1(C_497,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4638,c_46])).

tff(c_4998,plain,(
    ! [A_498] :
      ( v5_relat_1(A_498,'#skF_1')
      | ~ r1_tarski(A_498,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_4978])).

tff(c_5003,plain,
    ( r1_tarski(k1_xboole_0,'#skF_1')
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4998,c_2359])).

tff(c_5026,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5003])).

tff(c_5203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_5026])).

tff(c_5204,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5003])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5224,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5204,c_4])).

tff(c_5235,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5224])).

tff(c_6475,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6455,c_5235])).

tff(c_6499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6475])).

tff(c_6500,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5224])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4649,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4638,c_12])).

tff(c_4712,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4649])).

tff(c_6513,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6500,c_4712])).

tff(c_6733,plain,(
    ! [A_679] : k2_zfmisc_1(A_679,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6500,c_6500,c_14])).

tff(c_6744,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6733,c_4638])).

tff(c_6764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6513,c_6744])).

tff(c_6766,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4649])).

tff(c_2320,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2309,c_12])).

tff(c_4711,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2320])).

tff(c_6767,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6766,c_4711])).

tff(c_6775,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6766,c_6766,c_14])).

tff(c_6776,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6766,c_6766,c_16])).

tff(c_6765,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4649])).

tff(c_6988,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6766,c_6766,c_6765])).

tff(c_6989,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6988])).

tff(c_6991,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6989,c_2309])).

tff(c_6997,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6776,c_6991])).

tff(c_6999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6767,c_6997])).

tff(c_7000,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6988])).

tff(c_7017,plain,(
    k2_zfmisc_1('#skF_1','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7000,c_2309])).

tff(c_7024,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6775,c_7017])).

tff(c_7026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6767,c_7024])).

tff(c_7028,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2320])).

tff(c_129,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_88])).

tff(c_7038,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7028,c_129])).

tff(c_7047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_7038])).

tff(c_7048,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_28,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7126,plain,(
    ! [B_702,A_703] :
      ( v1_relat_1(B_702)
      | ~ m1_subset_1(B_702,k1_zfmisc_1(A_703))
      | ~ v1_relat_1(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7141,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_7126])).

tff(c_7154,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7141])).

tff(c_7334,plain,(
    ! [C_727,B_728,A_729] :
      ( v5_relat_1(C_727,B_728)
      | ~ m1_subset_1(C_727,k1_zfmisc_1(k2_zfmisc_1(A_729,B_728))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7358,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_7334])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7138,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_7126])).

tff(c_7151,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7138])).

tff(c_38,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38])).

tff(c_7949,plain,(
    ! [B_793,E_796,C_797,D_795,F_794,A_792] :
      ( k1_partfun1(A_792,B_793,C_797,D_795,E_796,F_794) = k5_relat_1(E_796,F_794)
      | ~ m1_subset_1(F_794,k1_zfmisc_1(k2_zfmisc_1(C_797,D_795)))
      | ~ v1_funct_1(F_794)
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(A_792,B_793)))
      | ~ v1_funct_1(E_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7958,plain,(
    ! [A_792,B_793,E_796] :
      ( k1_partfun1(A_792,B_793,'#skF_2','#skF_1',E_796,'#skF_4') = k5_relat_1(E_796,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(A_792,B_793)))
      | ~ v1_funct_1(E_796) ) ),
    inference(resolution,[status(thm)],[c_76,c_7949])).

tff(c_8400,plain,(
    ! [A_839,B_840,E_841] :
      ( k1_partfun1(A_839,B_840,'#skF_2','#skF_1',E_841,'#skF_4') = k5_relat_1(E_841,'#skF_4')
      | ~ m1_subset_1(E_841,k1_zfmisc_1(k2_zfmisc_1(A_839,B_840)))
      | ~ v1_funct_1(E_841) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7958])).

tff(c_8419,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_8400])).

tff(c_8440,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8419])).

tff(c_8592,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8440,c_60])).

tff(c_8598,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_8592])).

tff(c_7590,plain,(
    ! [D_757,C_758,A_759,B_760] :
      ( D_757 = C_758
      | ~ r2_relset_1(A_759,B_760,C_758,D_757)
      | ~ m1_subset_1(D_757,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760)))
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7600,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_7590])).

tff(c_7619,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_7600])).

tff(c_7711,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7619])).

tff(c_8672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8598,c_8440,c_7711])).

tff(c_8673,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7619])).

tff(c_8939,plain,(
    ! [D_880,E_881,C_882,F_879,B_878,A_877] :
      ( k1_partfun1(A_877,B_878,C_882,D_880,E_881,F_879) = k5_relat_1(E_881,F_879)
      | ~ m1_subset_1(F_879,k1_zfmisc_1(k2_zfmisc_1(C_882,D_880)))
      | ~ v1_funct_1(F_879)
      | ~ m1_subset_1(E_881,k1_zfmisc_1(k2_zfmisc_1(A_877,B_878)))
      | ~ v1_funct_1(E_881) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8948,plain,(
    ! [A_877,B_878,E_881] :
      ( k1_partfun1(A_877,B_878,'#skF_2','#skF_1',E_881,'#skF_4') = k5_relat_1(E_881,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_881,k1_zfmisc_1(k2_zfmisc_1(A_877,B_878)))
      | ~ v1_funct_1(E_881) ) ),
    inference(resolution,[status(thm)],[c_76,c_8939])).

tff(c_9401,plain,(
    ! [A_919,B_920,E_921] :
      ( k1_partfun1(A_919,B_920,'#skF_2','#skF_1',E_921,'#skF_4') = k5_relat_1(E_921,'#skF_4')
      | ~ m1_subset_1(E_921,k1_zfmisc_1(k2_zfmisc_1(A_919,B_920)))
      | ~ v1_funct_1(E_921) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8948])).

tff(c_9420,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_9401])).

tff(c_9441,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8673,c_9420])).

tff(c_30,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_16,B_18)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9448,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9441,c_30])).

tff(c_9452,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7151,c_7154,c_90,c_9448])).

tff(c_9459,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_9452,c_4])).

tff(c_9463,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_9459])).

tff(c_9467,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_9463])).

tff(c_9471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7154,c_7358,c_9467])).

tff(c_9472,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9459])).

tff(c_7257,plain,(
    ! [B_718,A_719] :
      ( v5_relat_1(B_718,A_719)
      | ~ r1_tarski(k2_relat_1(B_718),A_719)
      | ~ v1_relat_1(B_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7276,plain,(
    ! [B_718] :
      ( v5_relat_1(B_718,k2_relat_1(B_718))
      | ~ v1_relat_1(B_718) ) ),
    inference(resolution,[status(thm)],[c_8,c_7257])).

tff(c_7360,plain,(
    ! [B_732] :
      ( v2_funct_2(B_732,k2_relat_1(B_732))
      | ~ v5_relat_1(B_732,k2_relat_1(B_732))
      | ~ v1_relat_1(B_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7377,plain,(
    ! [B_718] :
      ( v2_funct_2(B_718,k2_relat_1(B_718))
      | ~ v1_relat_1(B_718) ) ),
    inference(resolution,[status(thm)],[c_7276,c_7360])).

tff(c_9483,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9472,c_7377])).

tff(c_9498,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7154,c_9483])).

tff(c_9500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7048,c_9498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.74  
% 7.49/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.75  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.49/2.75  
% 7.49/2.75  %Foreground sorts:
% 7.49/2.75  
% 7.49/2.75  
% 7.49/2.75  %Background operators:
% 7.49/2.75  
% 7.49/2.75  
% 7.49/2.75  %Foreground operators:
% 7.49/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.49/2.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.49/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.49/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.49/2.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.49/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.49/2.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.49/2.75  tff('#skF_2', type, '#skF_2': $i).
% 7.49/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.75  tff('#skF_1', type, '#skF_1': $i).
% 7.49/2.75  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.49/2.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.49/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.49/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.49/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.49/2.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.49/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.49/2.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.49/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.49/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.75  
% 7.74/2.78  tff(f_174, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.74/2.78  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.74/2.78  tff(f_132, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.74/2.78  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.74/2.78  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.74/2.78  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.74/2.78  tff(f_100, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.74/2.78  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.74/2.78  tff(f_154, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.74/2.78  tff(f_80, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.74/2.78  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.74/2.78  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.74/2.78  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.74/2.78  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.74/2.78  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.74/2.78  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.74/2.78  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.74/2.78  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.74/2.78  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.74/2.78  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.74/2.78  tff(c_72, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_189, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 7.74/2.78  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.74/2.78  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_66, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.74/2.78  tff(c_44, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.74/2.78  tff(c_88, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44])).
% 7.74/2.78  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_900, plain, (![B_150, C_154, A_149, D_152, E_153, F_151]: (k1_partfun1(A_149, B_150, C_154, D_152, E_153, F_151)=k5_relat_1(E_153, F_151) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_154, D_152))) | ~v1_funct_1(F_151) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(E_153))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.74/2.78  tff(c_907, plain, (![A_149, B_150, E_153]: (k1_partfun1(A_149, B_150, '#skF_2', '#skF_1', E_153, '#skF_4')=k5_relat_1(E_153, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(E_153))), inference(resolution, [status(thm)], [c_76, c_900])).
% 7.74/2.78  tff(c_1159, plain, (![A_176, B_177, E_178]: (k1_partfun1(A_176, B_177, '#skF_2', '#skF_1', E_178, '#skF_4')=k5_relat_1(E_178, '#skF_4') | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(E_178))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_907])).
% 7.74/2.78  tff(c_1175, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1159])).
% 7.74/2.78  tff(c_1190, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1175])).
% 7.74/2.78  tff(c_60, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.74/2.78  tff(c_1301, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1190, c_60])).
% 7.74/2.78  tff(c_1305, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1301])).
% 7.74/2.78  tff(c_54, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.74/2.78  tff(c_87, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54])).
% 7.74/2.78  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_686, plain, (![D_120, C_121, A_122, B_123]: (D_120=C_121 | ~r2_relset_1(A_122, B_123, C_121, D_120) | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.74/2.78  tff(c_692, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_686])).
% 7.74/2.78  tff(c_703, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_692])).
% 7.74/2.78  tff(c_2007, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1190, c_1190, c_703])).
% 7.74/2.78  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.74/2.78  tff(c_1361, plain, (![C_196, E_198, D_195, B_197, A_199]: (k1_xboole_0=C_196 | v2_funct_1(D_195) | ~v2_funct_1(k1_partfun1(A_199, B_197, B_197, C_196, D_195, E_198)) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(B_197, C_196))) | ~v1_funct_2(E_198, B_197, C_196) | ~v1_funct_1(E_198) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(A_199, B_197))) | ~v1_funct_2(D_195, A_199, B_197) | ~v1_funct_1(D_195))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.74/2.78  tff(c_1363, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1190, c_1361])).
% 7.74/2.78  tff(c_1365, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_1363])).
% 7.74/2.78  tff(c_1366, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_189, c_1365])).
% 7.74/2.78  tff(c_1373, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1366])).
% 7.74/2.78  tff(c_2010, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2007, c_1373])).
% 7.74/2.78  tff(c_2022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2010])).
% 7.74/2.78  tff(c_2023, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1366])).
% 7.74/2.78  tff(c_110, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.74/2.78  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.74/2.78  tff(c_116, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_110, c_40])).
% 7.74/2.78  tff(c_42, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.74/2.78  tff(c_89, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42])).
% 7.74/2.78  tff(c_127, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_89])).
% 7.74/2.78  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.74/2.78  tff(c_200, plain, (![A_64]: (m1_subset_1(k6_partfun1(A_64), k1_zfmisc_1(k2_zfmisc_1(A_64, A_64))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54])).
% 7.74/2.78  tff(c_204, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_200])).
% 7.74/2.78  tff(c_212, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_204])).
% 7.74/2.78  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.74/2.78  tff(c_334, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.74/2.78  tff(c_391, plain, (![C_86, B_87]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_334])).
% 7.74/2.78  tff(c_398, plain, (![B_87]: (v5_relat_1(k1_xboole_0, B_87))), inference(resolution, [status(thm)], [c_212, c_391])).
% 7.74/2.78  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.74/2.78  tff(c_402, plain, (![B_89, A_90]: (r1_tarski(k2_relat_1(B_89), A_90) | ~v5_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.74/2.78  tff(c_416, plain, (![A_90]: (r1_tarski(k1_xboole_0, A_90) | ~v5_relat_1(k1_xboole_0, A_90) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_402])).
% 7.74/2.78  tff(c_423, plain, (![A_90]: (r1_tarski(k1_xboole_0, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_398, c_416])).
% 7.74/2.78  tff(c_2045, plain, (![A_90]: (r1_tarski('#skF_1', A_90))), inference(demodulation, [status(thm), theory('equality')], [c_2023, c_423])).
% 7.74/2.78  tff(c_2052, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2023, c_2023, c_16])).
% 7.74/2.78  tff(c_217, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | ~m1_subset_1(A_65, k1_zfmisc_1(B_66)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.74/2.78  tff(c_234, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_217])).
% 7.74/2.78  tff(c_255, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.74/2.78  tff(c_265, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_234, c_255])).
% 7.74/2.78  tff(c_378, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_265])).
% 7.74/2.78  tff(c_2303, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_378])).
% 7.74/2.78  tff(c_2308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2045, c_2303])).
% 7.74/2.78  tff(c_2309, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_265])).
% 7.74/2.78  tff(c_2312, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2309, c_82])).
% 7.74/2.78  tff(c_2952, plain, (![D_301, C_302, A_303, B_304]: (D_301=C_302 | ~r2_relset_1(A_303, B_304, C_302, D_301) | ~m1_subset_1(D_301, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.74/2.78  tff(c_2964, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_2952])).
% 7.74/2.78  tff(c_2986, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_2964])).
% 7.74/2.78  tff(c_3048, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2986])).
% 7.74/2.78  tff(c_3482, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3048])).
% 7.74/2.78  tff(c_3489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_2312, c_2309, c_80, c_76, c_3482])).
% 7.74/2.78  tff(c_3490, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2986])).
% 7.74/2.78  tff(c_4343, plain, (![C_447, A_450, D_446, B_448, E_449]: (k1_xboole_0=C_447 | v2_funct_1(D_446) | ~v2_funct_1(k1_partfun1(A_450, B_448, B_448, C_447, D_446, E_449)) | ~m1_subset_1(E_449, k1_zfmisc_1(k2_zfmisc_1(B_448, C_447))) | ~v1_funct_2(E_449, B_448, C_447) | ~v1_funct_1(E_449) | ~m1_subset_1(D_446, k1_zfmisc_1(k2_zfmisc_1(A_450, B_448))) | ~v1_funct_2(D_446, A_450, B_448) | ~v1_funct_1(D_446))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.74/2.78  tff(c_4345, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3490, c_4343])).
% 7.74/2.78  tff(c_4347, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_2312, c_2309, c_80, c_78, c_76, c_88, c_4345])).
% 7.74/2.78  tff(c_4348, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_189, c_4347])).
% 7.74/2.78  tff(c_2649, plain, (![C_263, B_264]: (v5_relat_1(C_263, B_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_334])).
% 7.74/2.78  tff(c_2656, plain, (![B_264]: (v5_relat_1(k1_xboole_0, B_264))), inference(resolution, [status(thm)], [c_212, c_2649])).
% 7.74/2.78  tff(c_2338, plain, (![B_230, A_231]: (r1_tarski(k2_relat_1(B_230), A_231) | ~v5_relat_1(B_230, A_231) | ~v1_relat_1(B_230))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.74/2.78  tff(c_2352, plain, (![A_231]: (r1_tarski(k1_xboole_0, A_231) | ~v5_relat_1(k1_xboole_0, A_231) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2338])).
% 7.74/2.78  tff(c_2359, plain, (![A_231]: (r1_tarski(k1_xboole_0, A_231) | ~v5_relat_1(k1_xboole_0, A_231))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2352])).
% 7.74/2.78  tff(c_2658, plain, (![A_231]: (r1_tarski(k1_xboole_0, A_231))), inference(demodulation, [status(thm), theory('equality')], [c_2656, c_2359])).
% 7.74/2.78  tff(c_4371, plain, (![A_231]: (r1_tarski('#skF_1', A_231))), inference(demodulation, [status(thm), theory('equality')], [c_4348, c_2658])).
% 7.74/2.78  tff(c_4381, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4348, c_4348, c_14])).
% 7.74/2.78  tff(c_233, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_217])).
% 7.74/2.78  tff(c_266, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_233, c_255])).
% 7.74/2.78  tff(c_2373, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_266])).
% 7.74/2.78  tff(c_4632, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4381, c_2373])).
% 7.74/2.78  tff(c_4637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4371, c_4632])).
% 7.74/2.78  tff(c_4638, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_266])).
% 7.74/2.78  tff(c_4641, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4638, c_76])).
% 7.74/2.78  tff(c_5737, plain, (![B_576, D_575, E_577, C_580, F_579, A_578]: (m1_subset_1(k1_partfun1(A_578, B_576, C_580, D_575, E_577, F_579), k1_zfmisc_1(k2_zfmisc_1(A_578, D_575))) | ~m1_subset_1(F_579, k1_zfmisc_1(k2_zfmisc_1(C_580, D_575))) | ~v1_funct_1(F_579) | ~m1_subset_1(E_577, k1_zfmisc_1(k2_zfmisc_1(A_578, B_576))) | ~v1_funct_1(E_577))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.74/2.78  tff(c_5346, plain, (![D_528, C_529, A_530, B_531]: (D_528=C_529 | ~r2_relset_1(A_530, B_531, C_529, D_528) | ~m1_subset_1(D_528, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.74/2.78  tff(c_5352, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_5346])).
% 7.74/2.78  tff(c_5363, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_5352])).
% 7.74/2.78  tff(c_5387, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5363])).
% 7.74/2.78  tff(c_5742, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5737, c_5387])).
% 7.74/2.78  tff(c_5775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_2312, c_2309, c_80, c_4641, c_4638, c_5742])).
% 7.74/2.78  tff(c_5776, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5363])).
% 7.74/2.78  tff(c_6450, plain, (![E_663, D_660, B_662, C_661, A_664]: (k1_xboole_0=C_661 | v2_funct_1(D_660) | ~v2_funct_1(k1_partfun1(A_664, B_662, B_662, C_661, D_660, E_663)) | ~m1_subset_1(E_663, k1_zfmisc_1(k2_zfmisc_1(B_662, C_661))) | ~v1_funct_2(E_663, B_662, C_661) | ~v1_funct_1(E_663) | ~m1_subset_1(D_660, k1_zfmisc_1(k2_zfmisc_1(A_664, B_662))) | ~v1_funct_2(D_660, A_664, B_662) | ~v1_funct_1(D_660))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.74/2.78  tff(c_6452, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5776, c_6450])).
% 7.74/2.78  tff(c_6454, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_2312, c_2309, c_80, c_78, c_4641, c_4638, c_88, c_6452])).
% 7.74/2.78  tff(c_6455, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_189, c_6454])).
% 7.74/2.78  tff(c_5162, plain, (![C_512, B_513]: (v5_relat_1(C_512, B_513) | ~m1_subset_1(C_512, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_334])).
% 7.74/2.78  tff(c_5169, plain, (![B_513]: (v5_relat_1(k1_xboole_0, B_513))), inference(resolution, [status(thm)], [c_212, c_5162])).
% 7.74/2.78  tff(c_5171, plain, (![A_231]: (r1_tarski(k1_xboole_0, A_231))), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_2359])).
% 7.74/2.78  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.74/2.78  tff(c_46, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.74/2.78  tff(c_4978, plain, (![C_497]: (v5_relat_1(C_497, '#skF_1') | ~m1_subset_1(C_497, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4638, c_46])).
% 7.74/2.78  tff(c_4998, plain, (![A_498]: (v5_relat_1(A_498, '#skF_1') | ~r1_tarski(A_498, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_4978])).
% 7.74/2.78  tff(c_5003, plain, (r1_tarski(k1_xboole_0, '#skF_1') | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_4998, c_2359])).
% 7.74/2.78  tff(c_5026, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_5003])).
% 7.74/2.78  tff(c_5203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5171, c_5026])).
% 7.74/2.78  tff(c_5204, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(splitRight, [status(thm)], [c_5003])).
% 7.74/2.78  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.74/2.78  tff(c_5224, plain, (k1_xboole_0='#skF_1' | ~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_5204, c_4])).
% 7.74/2.78  tff(c_5235, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5224])).
% 7.74/2.78  tff(c_6475, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6455, c_5235])).
% 7.74/2.78  tff(c_6499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6475])).
% 7.74/2.78  tff(c_6500, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5224])).
% 7.74/2.78  tff(c_12, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.74/2.78  tff(c_4649, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4638, c_12])).
% 7.74/2.78  tff(c_4712, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_4649])).
% 7.74/2.78  tff(c_6513, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6500, c_4712])).
% 7.74/2.78  tff(c_6733, plain, (![A_679]: (k2_zfmisc_1(A_679, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6500, c_6500, c_14])).
% 7.74/2.78  tff(c_6744, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6733, c_4638])).
% 7.74/2.78  tff(c_6764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6513, c_6744])).
% 7.74/2.78  tff(c_6766, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4649])).
% 7.74/2.78  tff(c_2320, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2309, c_12])).
% 7.74/2.78  tff(c_4711, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_2320])).
% 7.74/2.78  tff(c_6767, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6766, c_4711])).
% 7.74/2.78  tff(c_6775, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6766, c_6766, c_14])).
% 7.74/2.78  tff(c_6776, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6766, c_6766, c_16])).
% 7.74/2.78  tff(c_6765, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4649])).
% 7.74/2.78  tff(c_6988, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6766, c_6766, c_6765])).
% 7.74/2.78  tff(c_6989, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_6988])).
% 7.74/2.78  tff(c_6991, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6989, c_2309])).
% 7.74/2.78  tff(c_6997, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6776, c_6991])).
% 7.74/2.78  tff(c_6999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6767, c_6997])).
% 7.74/2.78  tff(c_7000, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_6988])).
% 7.74/2.78  tff(c_7017, plain, (k2_zfmisc_1('#skF_1', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7000, c_2309])).
% 7.74/2.78  tff(c_7024, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6775, c_7017])).
% 7.74/2.78  tff(c_7026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6767, c_7024])).
% 7.74/2.78  tff(c_7028, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2320])).
% 7.74/2.78  tff(c_129, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_88])).
% 7.74/2.78  tff(c_7038, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7028, c_129])).
% 7.74/2.78  tff(c_7047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_7038])).
% 7.74/2.78  tff(c_7048, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 7.74/2.78  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.74/2.78  tff(c_7126, plain, (![B_702, A_703]: (v1_relat_1(B_702) | ~m1_subset_1(B_702, k1_zfmisc_1(A_703)) | ~v1_relat_1(A_703))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.74/2.78  tff(c_7141, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_7126])).
% 7.74/2.78  tff(c_7154, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7141])).
% 7.74/2.78  tff(c_7334, plain, (![C_727, B_728, A_729]: (v5_relat_1(C_727, B_728) | ~m1_subset_1(C_727, k1_zfmisc_1(k2_zfmisc_1(A_729, B_728))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.74/2.78  tff(c_7358, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_7334])).
% 7.74/2.78  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.74/2.78  tff(c_7138, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_7126])).
% 7.74/2.78  tff(c_7151, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7138])).
% 7.74/2.78  tff(c_38, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.74/2.78  tff(c_90, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38])).
% 7.74/2.78  tff(c_7949, plain, (![B_793, E_796, C_797, D_795, F_794, A_792]: (k1_partfun1(A_792, B_793, C_797, D_795, E_796, F_794)=k5_relat_1(E_796, F_794) | ~m1_subset_1(F_794, k1_zfmisc_1(k2_zfmisc_1(C_797, D_795))) | ~v1_funct_1(F_794) | ~m1_subset_1(E_796, k1_zfmisc_1(k2_zfmisc_1(A_792, B_793))) | ~v1_funct_1(E_796))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.74/2.78  tff(c_7958, plain, (![A_792, B_793, E_796]: (k1_partfun1(A_792, B_793, '#skF_2', '#skF_1', E_796, '#skF_4')=k5_relat_1(E_796, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_796, k1_zfmisc_1(k2_zfmisc_1(A_792, B_793))) | ~v1_funct_1(E_796))), inference(resolution, [status(thm)], [c_76, c_7949])).
% 7.74/2.78  tff(c_8400, plain, (![A_839, B_840, E_841]: (k1_partfun1(A_839, B_840, '#skF_2', '#skF_1', E_841, '#skF_4')=k5_relat_1(E_841, '#skF_4') | ~m1_subset_1(E_841, k1_zfmisc_1(k2_zfmisc_1(A_839, B_840))) | ~v1_funct_1(E_841))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7958])).
% 7.74/2.78  tff(c_8419, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_8400])).
% 7.74/2.78  tff(c_8440, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8419])).
% 7.74/2.78  tff(c_8592, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8440, c_60])).
% 7.74/2.78  tff(c_8598, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_8592])).
% 7.74/2.78  tff(c_7590, plain, (![D_757, C_758, A_759, B_760]: (D_757=C_758 | ~r2_relset_1(A_759, B_760, C_758, D_757) | ~m1_subset_1(D_757, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))) | ~m1_subset_1(C_758, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.74/2.78  tff(c_7600, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_7590])).
% 7.74/2.78  tff(c_7619, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_7600])).
% 7.74/2.78  tff(c_7711, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_7619])).
% 7.74/2.78  tff(c_8672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8598, c_8440, c_7711])).
% 7.74/2.78  tff(c_8673, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_7619])).
% 7.74/2.78  tff(c_8939, plain, (![D_880, E_881, C_882, F_879, B_878, A_877]: (k1_partfun1(A_877, B_878, C_882, D_880, E_881, F_879)=k5_relat_1(E_881, F_879) | ~m1_subset_1(F_879, k1_zfmisc_1(k2_zfmisc_1(C_882, D_880))) | ~v1_funct_1(F_879) | ~m1_subset_1(E_881, k1_zfmisc_1(k2_zfmisc_1(A_877, B_878))) | ~v1_funct_1(E_881))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.74/2.78  tff(c_8948, plain, (![A_877, B_878, E_881]: (k1_partfun1(A_877, B_878, '#skF_2', '#skF_1', E_881, '#skF_4')=k5_relat_1(E_881, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_881, k1_zfmisc_1(k2_zfmisc_1(A_877, B_878))) | ~v1_funct_1(E_881))), inference(resolution, [status(thm)], [c_76, c_8939])).
% 7.74/2.78  tff(c_9401, plain, (![A_919, B_920, E_921]: (k1_partfun1(A_919, B_920, '#skF_2', '#skF_1', E_921, '#skF_4')=k5_relat_1(E_921, '#skF_4') | ~m1_subset_1(E_921, k1_zfmisc_1(k2_zfmisc_1(A_919, B_920))) | ~v1_funct_1(E_921))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8948])).
% 7.74/2.78  tff(c_9420, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_9401])).
% 7.74/2.78  tff(c_9441, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8673, c_9420])).
% 7.74/2.78  tff(c_30, plain, (![A_16, B_18]: (r1_tarski(k2_relat_1(k5_relat_1(A_16, B_18)), k2_relat_1(B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.74/2.78  tff(c_9448, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9441, c_30])).
% 7.74/2.78  tff(c_9452, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7151, c_7154, c_90, c_9448])).
% 7.74/2.78  tff(c_9459, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_9452, c_4])).
% 7.74/2.78  tff(c_9463, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_9459])).
% 7.74/2.78  tff(c_9467, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_9463])).
% 7.74/2.78  tff(c_9471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7154, c_7358, c_9467])).
% 7.74/2.78  tff(c_9472, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_9459])).
% 7.74/2.78  tff(c_7257, plain, (![B_718, A_719]: (v5_relat_1(B_718, A_719) | ~r1_tarski(k2_relat_1(B_718), A_719) | ~v1_relat_1(B_718))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.74/2.78  tff(c_7276, plain, (![B_718]: (v5_relat_1(B_718, k2_relat_1(B_718)) | ~v1_relat_1(B_718))), inference(resolution, [status(thm)], [c_8, c_7257])).
% 7.74/2.78  tff(c_7360, plain, (![B_732]: (v2_funct_2(B_732, k2_relat_1(B_732)) | ~v5_relat_1(B_732, k2_relat_1(B_732)) | ~v1_relat_1(B_732))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.74/2.78  tff(c_7377, plain, (![B_718]: (v2_funct_2(B_718, k2_relat_1(B_718)) | ~v1_relat_1(B_718))), inference(resolution, [status(thm)], [c_7276, c_7360])).
% 7.74/2.78  tff(c_9483, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9472, c_7377])).
% 7.74/2.78  tff(c_9498, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7154, c_9483])).
% 7.74/2.78  tff(c_9500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7048, c_9498])).
% 7.74/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.78  
% 7.74/2.78  Inference rules
% 7.74/2.78  ----------------------
% 7.74/2.78  #Ref     : 0
% 7.74/2.78  #Sup     : 1956
% 7.74/2.78  #Fact    : 0
% 7.74/2.78  #Define  : 0
% 7.74/2.78  #Split   : 53
% 7.74/2.78  #Chain   : 0
% 7.74/2.78  #Close   : 0
% 7.74/2.78  
% 7.74/2.78  Ordering : KBO
% 7.74/2.78  
% 7.74/2.78  Simplification rules
% 7.74/2.78  ----------------------
% 7.74/2.78  #Subsume      : 193
% 7.74/2.78  #Demod        : 2021
% 7.74/2.78  #Tautology    : 775
% 7.74/2.78  #SimpNegUnit  : 41
% 7.74/2.78  #BackRed      : 302
% 7.74/2.78  
% 7.74/2.78  #Partial instantiations: 0
% 7.74/2.78  #Strategies tried      : 1
% 7.74/2.78  
% 7.74/2.78  Timing (in seconds)
% 7.74/2.78  ----------------------
% 7.74/2.78  Preprocessing        : 0.35
% 7.74/2.78  Parsing              : 0.20
% 7.74/2.78  CNF conversion       : 0.02
% 7.74/2.78  Main loop            : 1.56
% 7.74/2.78  Inferencing          : 0.51
% 7.74/2.78  Reduction            : 0.59
% 7.74/2.78  Demodulation         : 0.43
% 7.74/2.78  BG Simplification    : 0.05
% 7.74/2.78  Subsumption          : 0.27
% 7.74/2.78  Abstraction          : 0.06
% 7.74/2.78  MUC search           : 0.00
% 7.74/2.78  Cooper               : 0.00
% 7.74/2.78  Total                : 1.98
% 7.74/2.78  Index Insertion      : 0.00
% 7.74/2.78  Index Deletion       : 0.00
% 7.74/2.78  Index Matching       : 0.00
% 7.74/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
