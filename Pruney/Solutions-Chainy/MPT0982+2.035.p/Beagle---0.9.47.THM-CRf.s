%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:00 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 272 expanded)
%              Number of leaves         :   49 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  225 ( 801 expanded)
%              Number of equality atoms :   74 ( 224 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_355,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_367,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_355])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_369,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_56])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_126])).

tff(c_139,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_132])).

tff(c_456,plain,(
    ! [A_119,B_120,C_121] :
      ( m1_subset_1(k2_relset_1(A_119,B_120,C_121),k1_zfmisc_1(B_120))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_487,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_456])).

tff(c_500,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_487])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_538,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_500,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_135,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_126])).

tff(c_142,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_135])).

tff(c_368,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_355])).

tff(c_484,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_456])).

tff(c_498,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_484])).

tff(c_508,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_498,c_10])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_519,plain,(
    k3_xboole_0(k2_relat_1('#skF_5'),'#skF_3') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_508,c_8])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k10_relat_1(B_18,k3_xboole_0(k2_relat_1(B_18),A_17)) = k10_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2140,plain,
    ( k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k10_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_22])).

tff(c_2144,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k10_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2140])).

tff(c_173,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_186,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_173])).

tff(c_205,plain,(
    ! [B_81,A_82] :
      ( k7_relat_1(B_81,A_82) = B_81
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_211,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_186,c_205])).

tff(c_220,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_211])).

tff(c_273,plain,(
    ! [B_93,A_94] :
      ( k2_relat_1(k7_relat_1(B_93,A_94)) = k9_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_288,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_273])).

tff(c_296,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_288])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_409,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_422,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_409])).

tff(c_2462,plain,(
    ! [B_265,A_266,C_267] :
      ( k1_xboole_0 = B_265
      | k1_relset_1(A_266,B_265,C_267) = A_266
      | ~ v1_funct_2(C_267,A_266,B_265)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_266,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2479,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2462])).

tff(c_2490,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_422,c_2479])).

tff(c_2491,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2490])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k10_relat_1(B_22,k9_relat_1(B_22,A_21)) = A_21
      | ~ v2_funct_1(B_22)
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2495,plain,(
    ! [A_21] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_21)) = A_21
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_21,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_26])).

tff(c_2520,plain,(
    ! [A_268] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_268)) = A_268
      | ~ r1_tarski(A_268,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68,c_60,c_2495])).

tff(c_2533,plain,
    ( k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_2520])).

tff(c_2539,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2144,c_2533])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3075,plain,(
    ! [E_306,A_307,B_309,D_311,C_308,F_310] :
      ( k1_partfun1(A_307,B_309,C_308,D_311,E_306,F_310) = k5_relat_1(E_306,F_310)
      | ~ m1_subset_1(F_310,k1_zfmisc_1(k2_zfmisc_1(C_308,D_311)))
      | ~ v1_funct_1(F_310)
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_307,B_309)))
      | ~ v1_funct_1(E_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3093,plain,(
    ! [A_307,B_309,E_306] :
      ( k1_partfun1(A_307,B_309,'#skF_2','#skF_3',E_306,'#skF_5') = k5_relat_1(E_306,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_307,B_309)))
      | ~ v1_funct_1(E_306) ) ),
    inference(resolution,[status(thm)],[c_64,c_3075])).

tff(c_3832,plain,(
    ! [A_329,B_330,E_331] :
      ( k1_partfun1(A_329,B_330,'#skF_2','#skF_3',E_331,'#skF_5') = k5_relat_1(E_331,'#skF_5')
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(E_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3093])).

tff(c_3861,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3832])).

tff(c_3875,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3861])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_963,plain,(
    ! [A_174,E_173,B_178,D_176,F_177,C_175] :
      ( k4_relset_1(A_174,B_178,C_175,D_176,E_173,F_177) = k5_relat_1(E_173,F_177)
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(C_175,D_176)))
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1197,plain,(
    ! [A_196,B_197,E_198] :
      ( k4_relset_1(A_196,B_197,'#skF_2','#skF_3',E_198,'#skF_5') = k5_relat_1(E_198,'#skF_5')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(resolution,[status(thm)],[c_64,c_963])).

tff(c_1222,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1197])).

tff(c_34,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( m1_subset_1(k4_relset_1(A_29,B_30,C_31,D_32,E_33,F_34),k1_zfmisc_1(k2_zfmisc_1(A_29,D_32)))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1553,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_34])).

tff(c_1557,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_1553])).

tff(c_1617,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1557,c_10])).

tff(c_1317,plain,(
    ! [A_200,F_203,D_204,E_199,B_202,C_201] :
      ( k1_partfun1(A_200,B_202,C_201,D_204,E_199,F_203) = k5_relat_1(E_199,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_201,D_204)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_202)))
      | ~ v1_funct_1(E_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1333,plain,(
    ! [A_200,B_202,E_199] :
      ( k1_partfun1(A_200,B_202,'#skF_2','#skF_3',E_199,'#skF_5') = k5_relat_1(E_199,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_202)))
      | ~ v1_funct_1(E_199) ) ),
    inference(resolution,[status(thm)],[c_64,c_1317])).

tff(c_2037,plain,(
    ! [A_222,B_223,E_224] :
      ( k1_partfun1(A_222,B_223,'#skF_2','#skF_3',E_224,'#skF_5') = k5_relat_1(E_224,'#skF_5')
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_1(E_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1333])).

tff(c_2063,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_2037])).

tff(c_2076,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2063])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_490,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_456])).

tff(c_552,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_587,plain,(
    ~ r1_tarski(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_552])).

tff(c_2080,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2076,c_587])).

tff(c_2085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1617,c_2080])).

tff(c_2087,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_38,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_relset_1(A_38,B_39,C_40) = k2_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2103,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2087,c_38])).

tff(c_2118,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2103])).

tff(c_3886,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3875,c_2118])).

tff(c_20,plain,(
    ! [B_16,A_14] :
      ( k9_relat_1(B_16,k2_relat_1(A_14)) = k2_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2530,plain,(
    ! [A_14] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_14,'#skF_5'))) = k2_relat_1(A_14)
      | ~ r1_tarski(k2_relat_1(A_14),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2520])).

tff(c_2537,plain,(
    ! [A_14] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_14,'#skF_5'))) = k2_relat_1(A_14)
      | ~ r1_tarski(k2_relat_1(A_14),'#skF_2')
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2530])).

tff(c_3913,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3886,c_2537])).

tff(c_3925,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_538,c_2539,c_3913])).

tff(c_3927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_3925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.12  
% 5.94/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.13  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.94/2.13  
% 5.94/2.13  %Foreground sorts:
% 5.94/2.13  
% 5.94/2.13  
% 5.94/2.13  %Background operators:
% 5.94/2.13  
% 5.94/2.13  
% 5.94/2.13  %Foreground operators:
% 5.94/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.94/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.94/2.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.94/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.94/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.94/2.13  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.94/2.13  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.94/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.94/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.94/2.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.94/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.94/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.94/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.94/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.94/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.94/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.94/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.94/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.94/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.94/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.94/2.13  
% 5.94/2.15  tff(f_159, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 5.94/2.15  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.94/2.15  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.94/2.15  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.94/2.15  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.94/2.15  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.94/2.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.94/2.15  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.94/2.15  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 5.94/2.15  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.94/2.15  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.94/2.15  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.94/2.15  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.94/2.15  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.94/2.15  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 5.94/2.15  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.94/2.15  tff(f_109, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 5.94/2.15  tff(f_95, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 5.94/2.15  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 5.94/2.15  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_355, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_367, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_355])).
% 5.94/2.15  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_369, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_56])).
% 5.94/2.15  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.94/2.15  tff(c_126, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.94/2.15  tff(c_132, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_126])).
% 5.94/2.15  tff(c_139, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_132])).
% 5.94/2.15  tff(c_456, plain, (![A_119, B_120, C_121]: (m1_subset_1(k2_relset_1(A_119, B_120, C_121), k1_zfmisc_1(B_120)) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.94/2.15  tff(c_487, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_367, c_456])).
% 5.94/2.15  tff(c_500, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_487])).
% 5.94/2.15  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.94/2.15  tff(c_538, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_500, c_10])).
% 5.94/2.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.94/2.15  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_135, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_126])).
% 5.94/2.15  tff(c_142, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_135])).
% 5.94/2.15  tff(c_368, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_355])).
% 5.94/2.15  tff(c_484, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_368, c_456])).
% 5.94/2.15  tff(c_498, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_484])).
% 5.94/2.15  tff(c_508, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_498, c_10])).
% 5.94/2.15  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.94/2.15  tff(c_519, plain, (k3_xboole_0(k2_relat_1('#skF_5'), '#skF_3')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_508, c_8])).
% 5.94/2.15  tff(c_22, plain, (![B_18, A_17]: (k10_relat_1(B_18, k3_xboole_0(k2_relat_1(B_18), A_17))=k10_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.94/2.15  tff(c_2140, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k10_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_519, c_22])).
% 5.94/2.15  tff(c_2144, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k10_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2140])).
% 5.94/2.15  tff(c_173, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.94/2.15  tff(c_186, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_173])).
% 5.94/2.15  tff(c_205, plain, (![B_81, A_82]: (k7_relat_1(B_81, A_82)=B_81 | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.94/2.15  tff(c_211, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_186, c_205])).
% 5.94/2.15  tff(c_220, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_211])).
% 5.94/2.15  tff(c_273, plain, (![B_93, A_94]: (k2_relat_1(k7_relat_1(B_93, A_94))=k9_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.94/2.15  tff(c_288, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_220, c_273])).
% 5.94/2.15  tff(c_296, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_288])).
% 5.94/2.15  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_409, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.94/2.15  tff(c_422, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_409])).
% 5.94/2.15  tff(c_2462, plain, (![B_265, A_266, C_267]: (k1_xboole_0=B_265 | k1_relset_1(A_266, B_265, C_267)=A_266 | ~v1_funct_2(C_267, A_266, B_265) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_266, B_265))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.94/2.15  tff(c_2479, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_2462])).
% 5.94/2.15  tff(c_2490, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_422, c_2479])).
% 5.94/2.15  tff(c_2491, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_2490])).
% 5.94/2.15  tff(c_26, plain, (![B_22, A_21]: (k10_relat_1(B_22, k9_relat_1(B_22, A_21))=A_21 | ~v2_funct_1(B_22) | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.94/2.15  tff(c_2495, plain, (![A_21]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_21))=A_21 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_21, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2491, c_26])).
% 5.94/2.15  tff(c_2520, plain, (![A_268]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_268))=A_268 | ~r1_tarski(A_268, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68, c_60, c_2495])).
% 5.94/2.15  tff(c_2533, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_296, c_2520])).
% 5.94/2.15  tff(c_2539, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2144, c_2533])).
% 5.94/2.15  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_3075, plain, (![E_306, A_307, B_309, D_311, C_308, F_310]: (k1_partfun1(A_307, B_309, C_308, D_311, E_306, F_310)=k5_relat_1(E_306, F_310) | ~m1_subset_1(F_310, k1_zfmisc_1(k2_zfmisc_1(C_308, D_311))) | ~v1_funct_1(F_310) | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_307, B_309))) | ~v1_funct_1(E_306))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.94/2.15  tff(c_3093, plain, (![A_307, B_309, E_306]: (k1_partfun1(A_307, B_309, '#skF_2', '#skF_3', E_306, '#skF_5')=k5_relat_1(E_306, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_307, B_309))) | ~v1_funct_1(E_306))), inference(resolution, [status(thm)], [c_64, c_3075])).
% 5.94/2.15  tff(c_3832, plain, (![A_329, B_330, E_331]: (k1_partfun1(A_329, B_330, '#skF_2', '#skF_3', E_331, '#skF_5')=k5_relat_1(E_331, '#skF_5') | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(E_331))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3093])).
% 5.94/2.15  tff(c_3861, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3832])).
% 5.94/2.15  tff(c_3875, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3861])).
% 5.94/2.15  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.94/2.15  tff(c_963, plain, (![A_174, E_173, B_178, D_176, F_177, C_175]: (k4_relset_1(A_174, B_178, C_175, D_176, E_173, F_177)=k5_relat_1(E_173, F_177) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(C_175, D_176))) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_178))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.94/2.15  tff(c_1197, plain, (![A_196, B_197, E_198]: (k4_relset_1(A_196, B_197, '#skF_2', '#skF_3', E_198, '#skF_5')=k5_relat_1(E_198, '#skF_5') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(resolution, [status(thm)], [c_64, c_963])).
% 5.94/2.15  tff(c_1222, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_1197])).
% 5.94/2.15  tff(c_34, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (m1_subset_1(k4_relset_1(A_29, B_30, C_31, D_32, E_33, F_34), k1_zfmisc_1(k2_zfmisc_1(A_29, D_32))) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.94/2.15  tff(c_1553, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1222, c_34])).
% 5.94/2.15  tff(c_1557, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_1553])).
% 5.94/2.15  tff(c_1617, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1557, c_10])).
% 5.94/2.15  tff(c_1317, plain, (![A_200, F_203, D_204, E_199, B_202, C_201]: (k1_partfun1(A_200, B_202, C_201, D_204, E_199, F_203)=k5_relat_1(E_199, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_201, D_204))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_202))) | ~v1_funct_1(E_199))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.94/2.15  tff(c_1333, plain, (![A_200, B_202, E_199]: (k1_partfun1(A_200, B_202, '#skF_2', '#skF_3', E_199, '#skF_5')=k5_relat_1(E_199, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_202))) | ~v1_funct_1(E_199))), inference(resolution, [status(thm)], [c_64, c_1317])).
% 5.94/2.15  tff(c_2037, plain, (![A_222, B_223, E_224]: (k1_partfun1(A_222, B_223, '#skF_2', '#skF_3', E_224, '#skF_5')=k5_relat_1(E_224, '#skF_5') | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_1(E_224))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1333])).
% 5.94/2.15  tff(c_2063, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_2037])).
% 5.94/2.15  tff(c_2076, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2063])).
% 5.94/2.15  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.94/2.15  tff(c_490, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_456])).
% 5.94/2.15  tff(c_552, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_490])).
% 5.94/2.15  tff(c_587, plain, (~r1_tarski(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_552])).
% 5.94/2.15  tff(c_2080, plain, (~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2076, c_587])).
% 5.94/2.15  tff(c_2085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1617, c_2080])).
% 5.94/2.15  tff(c_2087, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_490])).
% 5.94/2.15  tff(c_38, plain, (![A_38, B_39, C_40]: (k2_relset_1(A_38, B_39, C_40)=k2_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2103, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2087, c_38])).
% 5.94/2.15  tff(c_2118, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2103])).
% 5.94/2.15  tff(c_3886, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3875, c_2118])).
% 5.94/2.15  tff(c_20, plain, (![B_16, A_14]: (k9_relat_1(B_16, k2_relat_1(A_14))=k2_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.94/2.15  tff(c_2530, plain, (![A_14]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_14, '#skF_5')))=k2_relat_1(A_14) | ~r1_tarski(k2_relat_1(A_14), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2520])).
% 5.94/2.15  tff(c_2537, plain, (![A_14]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_14, '#skF_5')))=k2_relat_1(A_14) | ~r1_tarski(k2_relat_1(A_14), '#skF_2') | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2530])).
% 5.94/2.15  tff(c_3913, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3886, c_2537])).
% 5.94/2.15  tff(c_3925, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_538, c_2539, c_3913])).
% 5.94/2.15  tff(c_3927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_3925])).
% 5.94/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.15  
% 5.94/2.15  Inference rules
% 5.94/2.15  ----------------------
% 5.94/2.15  #Ref     : 0
% 5.94/2.15  #Sup     : 907
% 5.94/2.15  #Fact    : 0
% 5.94/2.15  #Define  : 0
% 5.94/2.15  #Split   : 18
% 5.94/2.15  #Chain   : 0
% 5.94/2.15  #Close   : 0
% 5.94/2.15  
% 5.94/2.15  Ordering : KBO
% 5.94/2.15  
% 5.94/2.15  Simplification rules
% 5.94/2.15  ----------------------
% 5.94/2.15  #Subsume      : 70
% 5.94/2.15  #Demod        : 380
% 5.94/2.15  #Tautology    : 306
% 5.94/2.15  #SimpNegUnit  : 37
% 5.94/2.15  #BackRed      : 35
% 5.94/2.15  
% 5.94/2.15  #Partial instantiations: 0
% 5.94/2.15  #Strategies tried      : 1
% 5.94/2.15  
% 5.94/2.15  Timing (in seconds)
% 5.94/2.15  ----------------------
% 5.94/2.15  Preprocessing        : 0.36
% 5.94/2.15  Parsing              : 0.19
% 5.94/2.15  CNF conversion       : 0.02
% 5.94/2.15  Main loop            : 1.01
% 5.94/2.15  Inferencing          : 0.33
% 5.94/2.15  Reduction            : 0.38
% 5.94/2.15  Demodulation         : 0.26
% 5.94/2.15  BG Simplification    : 0.04
% 5.94/2.15  Subsumption          : 0.18
% 5.94/2.15  Abstraction          : 0.04
% 5.94/2.15  MUC search           : 0.00
% 5.94/2.15  Cooper               : 0.00
% 5.94/2.15  Total                : 1.42
% 5.94/2.15  Index Insertion      : 0.00
% 5.94/2.15  Index Deletion       : 0.00
% 5.94/2.15  Index Matching       : 0.00
% 5.94/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
