%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:57 EST 2020

% Result     : Theorem 38.27s
% Output     : CNFRefutation 38.54s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 655 expanded)
%              Number of leaves         :   54 ( 242 expanded)
%              Depth                    :   21
%              Number of atoms          :  272 (1369 expanded)
%              Number of equality atoms :  105 ( 285 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_205,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_177,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_158,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_181,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_193,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_66,plain,(
    ! [A_51,B_52] : v1_relat_1(k2_zfmisc_1(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_116,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_282,plain,(
    ! [B_116,A_117] :
      ( v1_relat_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_288,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_116,c_282])).

tff(c_295,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_288])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_784,plain,(
    ! [B_188,A_189] :
      ( v4_relat_1(B_188,A_189)
      | ~ r1_tarski(k1_relat_1(B_188),A_189)
      | ~ v1_relat_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_799,plain,(
    ! [B_190] :
      ( v4_relat_1(B_190,k1_relat_1(B_190))
      | ~ v1_relat_1(B_190) ) ),
    inference(resolution,[status(thm)],[c_6,c_784])).

tff(c_74,plain,(
    ! [B_59,A_58] :
      ( k7_relat_1(B_59,A_58) = B_59
      | ~ v4_relat_1(B_59,A_58)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_809,plain,(
    ! [B_191] :
      ( k7_relat_1(B_191,k1_relat_1(B_191)) = B_191
      | ~ v1_relat_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_799,c_74])).

tff(c_70,plain,(
    ! [B_56,A_55] :
      ( k2_relat_1(k7_relat_1(B_56,A_55)) = k9_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_819,plain,(
    ! [B_191] :
      ( k9_relat_1(B_191,k1_relat_1(B_191)) = k2_relat_1(B_191)
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_70])).

tff(c_67559,plain,(
    ! [B_1520] :
      ( k9_relat_1(B_1520,k1_relat_1(B_1520)) = k2_relat_1(B_1520)
      | ~ v1_relat_1(B_1520)
      | ~ v1_relat_1(B_1520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_70])).

tff(c_68,plain,(
    ! [B_54,A_53] :
      ( r1_tarski(k9_relat_1(B_54,A_53),k9_relat_1(B_54,k1_relat_1(B_54)))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_69198,plain,(
    ! [B_1662,A_1663] :
      ( r1_tarski(k9_relat_1(B_1662,A_1663),k2_relat_1(B_1662))
      | ~ v1_relat_1(B_1662)
      | ~ v1_relat_1(B_1662)
      | ~ v1_relat_1(B_1662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67559,c_68])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70779,plain,(
    ! [B_1733,A_1734] :
      ( k9_relat_1(B_1733,A_1734) = k2_relat_1(B_1733)
      | ~ r1_tarski(k2_relat_1(B_1733),k9_relat_1(B_1733,A_1734))
      | ~ v1_relat_1(B_1733) ) ),
    inference(resolution,[status(thm)],[c_69198,c_2])).

tff(c_70791,plain,(
    ! [B_191] :
      ( k9_relat_1(B_191,k1_relat_1(B_191)) = k2_relat_1(B_191)
      | ~ r1_tarski(k2_relat_1(B_191),k2_relat_1(B_191))
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_70779])).

tff(c_70832,plain,(
    ! [B_1735] :
      ( k9_relat_1(B_1735,k1_relat_1(B_1735)) = k2_relat_1(B_1735)
      | ~ v1_relat_1(B_1735) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_70791])).

tff(c_70883,plain,(
    ! [B_1735] :
      ( r1_tarski(k2_relat_1(B_1735),k9_relat_1(B_1735,k1_relat_1(B_1735)))
      | ~ v1_relat_1(B_1735)
      | ~ v1_relat_1(B_1735) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70832,c_68])).

tff(c_52,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(A_39,k1_zfmisc_1(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [B_33] : k2_zfmisc_1(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_419,plain,(
    ! [C_144,B_145,A_146] :
      ( v5_relat_1(C_144,B_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_469,plain,(
    ! [C_151,B_152] :
      ( v5_relat_1(C_151,B_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_419])).

tff(c_476,plain,(
    ! [A_39,B_152] :
      ( v5_relat_1(A_39,B_152)
      | ~ r1_tarski(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_469])).

tff(c_64,plain,(
    ! [B_50,A_49] :
      ( r1_tarski(k2_relat_1(B_50),A_49)
      | ~ v5_relat_1(B_50,A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_67429,plain,(
    ! [B_1513] :
      ( k9_relat_1(B_1513,k1_relat_1(B_1513)) = k2_relat_1(B_1513)
      | ~ v1_relat_1(B_1513)
      | ~ v1_relat_1(B_1513) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_70])).

tff(c_503,plain,(
    ! [C_158,A_159,B_160] :
      ( v4_relat_1(C_158,A_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_522,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_116,c_503])).

tff(c_534,plain,(
    ! [B_164,A_165] :
      ( k7_relat_1(B_164,A_165) = B_164
      | ~ v4_relat_1(B_164,A_165)
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_537,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_522,c_534])).

tff(c_543,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_537])).

tff(c_562,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_70])).

tff(c_566,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_562])).

tff(c_865,plain,(
    ! [B_193,A_194] :
      ( r1_tarski(k9_relat_1(B_193,A_194),k9_relat_1(B_193,k1_relat_1(B_193)))
      | ~ v1_relat_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_873,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k9_relat_1('#skF_4',k1_relat_1('#skF_4')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_865])).

tff(c_887,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k9_relat_1('#skF_4',k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_873])).

tff(c_906,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ r1_tarski(k9_relat_1('#skF_4',k1_relat_1('#skF_4')),k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_887,c_2])).

tff(c_67427,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k1_relat_1('#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_906])).

tff(c_67435,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_67429,c_67427])).

tff(c_67468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_295,c_6,c_67435])).

tff(c_67469,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_906])).

tff(c_67482,plain,(
    ! [A_53] :
      ( r1_tarski(k9_relat_1('#skF_4',A_53),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67469,c_68])).

tff(c_67502,plain,(
    ! [A_1517] : r1_tarski(k9_relat_1('#skF_4',A_1517),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_67482])).

tff(c_67698,plain,(
    ! [A_1534] :
      ( k9_relat_1('#skF_4',A_1534) = k2_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),k9_relat_1('#skF_4',A_1534)) ) ),
    inference(resolution,[status(thm)],[c_67502,c_2])).

tff(c_67708,plain,(
    ! [A_1534] :
      ( k9_relat_1('#skF_4',A_1534) = k2_relat_1('#skF_4')
      | ~ v5_relat_1('#skF_4',k9_relat_1('#skF_4',A_1534))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_67698])).

tff(c_67742,plain,(
    ! [A_1537] :
      ( k9_relat_1('#skF_4',A_1537) = k2_relat_1('#skF_4')
      | ~ v5_relat_1('#skF_4',k9_relat_1('#skF_4',A_1537)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_67708])).

tff(c_67762,plain,(
    ! [A_1537] :
      ( k9_relat_1('#skF_4',A_1537) = k2_relat_1('#skF_4')
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_476,c_67742])).

tff(c_67763,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_67762])).

tff(c_120,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_67488,plain,(
    ! [A_53] : r1_tarski(k9_relat_1('#skF_4',A_53),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_67482])).

tff(c_67798,plain,(
    ! [B_1546,A_1547] :
      ( k1_tarski(k1_funct_1(B_1546,A_1547)) = k2_relat_1(B_1546)
      | k1_tarski(A_1547) != k1_relat_1(B_1546)
      | ~ v1_funct_1(B_1546)
      | ~ v1_relat_1(B_1546) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_67764,plain,(
    ! [A_1538,B_1539,C_1540,D_1541] :
      ( k7_relset_1(A_1538,B_1539,C_1540,D_1541) = k9_relat_1(C_1540,D_1541)
      | ~ m1_subset_1(C_1540,k1_zfmisc_1(k2_zfmisc_1(A_1538,B_1539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_67778,plain,(
    ! [D_1541] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_1541) = k9_relat_1('#skF_4',D_1541) ),
    inference(resolution,[status(thm)],[c_116,c_67764])).

tff(c_112,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_67788,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67778,c_112])).

tff(c_67804,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_67798,c_67788])).

tff(c_67828,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_120,c_67488,c_67804])).

tff(c_60,plain,(
    ! [B_48,A_47] :
      ( r1_tarski(k1_relat_1(B_48),A_47)
      | ~ v4_relat_1(B_48,A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68274,plain,(
    ! [A_1600,B_1601,C_1602,D_1603] :
      ( k1_enumset1(A_1600,B_1601,C_1602) = D_1603
      | k2_tarski(A_1600,C_1602) = D_1603
      | k2_tarski(B_1601,C_1602) = D_1603
      | k2_tarski(A_1600,B_1601) = D_1603
      | k1_tarski(C_1602) = D_1603
      | k1_tarski(B_1601) = D_1603
      | k1_tarski(A_1600) = D_1603
      | k1_xboole_0 = D_1603
      | ~ r1_tarski(D_1603,k1_enumset1(A_1600,B_1601,C_1602)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68300,plain,(
    ! [A_5,B_6,D_1603] :
      ( k1_enumset1(A_5,A_5,B_6) = D_1603
      | k2_tarski(A_5,B_6) = D_1603
      | k2_tarski(A_5,B_6) = D_1603
      | k2_tarski(A_5,A_5) = D_1603
      | k1_tarski(B_6) = D_1603
      | k1_tarski(A_5) = D_1603
      | k1_tarski(A_5) = D_1603
      | k1_xboole_0 = D_1603
      | ~ r1_tarski(D_1603,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_68274])).

tff(c_75851,plain,(
    ! [A_1891,B_1892,D_1893] :
      ( k2_tarski(A_1891,B_1892) = D_1893
      | k2_tarski(A_1891,B_1892) = D_1893
      | k2_tarski(A_1891,B_1892) = D_1893
      | k1_tarski(A_1891) = D_1893
      | k1_tarski(B_1892) = D_1893
      | k1_tarski(A_1891) = D_1893
      | k1_tarski(A_1891) = D_1893
      | k1_xboole_0 = D_1893
      | ~ r1_tarski(D_1893,k2_tarski(A_1891,B_1892)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_68300])).

tff(c_75876,plain,(
    ! [A_4,D_1893] :
      ( k2_tarski(A_4,A_4) = D_1893
      | k2_tarski(A_4,A_4) = D_1893
      | k2_tarski(A_4,A_4) = D_1893
      | k1_tarski(A_4) = D_1893
      | k1_tarski(A_4) = D_1893
      | k1_tarski(A_4) = D_1893
      | k1_tarski(A_4) = D_1893
      | k1_xboole_0 = D_1893
      | ~ r1_tarski(D_1893,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75851])).

tff(c_140113,plain,(
    ! [A_2717,D_2718] :
      ( k1_tarski(A_2717) = D_2718
      | k1_tarski(A_2717) = D_2718
      | k1_tarski(A_2717) = D_2718
      | k1_tarski(A_2717) = D_2718
      | k1_tarski(A_2717) = D_2718
      | k1_tarski(A_2717) = D_2718
      | k1_tarski(A_2717) = D_2718
      | k1_xboole_0 = D_2718
      | ~ r1_tarski(D_2718,k1_tarski(A_2717)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_75876])).

tff(c_140531,plain,(
    ! [A_2725,B_2726] :
      ( k1_tarski(A_2725) = k1_relat_1(B_2726)
      | k1_relat_1(B_2726) = k1_xboole_0
      | ~ v4_relat_1(B_2726,k1_tarski(A_2725))
      | ~ v1_relat_1(B_2726) ) ),
    inference(resolution,[status(thm)],[c_60,c_140113])).

tff(c_140648,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_522,c_140531])).

tff(c_140692,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_140648])).

tff(c_140693,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_67828,c_140692])).

tff(c_67980,plain,(
    ! [B_1561,A_1562] :
      ( m1_subset_1(B_1561,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1561),A_1562)))
      | ~ r1_tarski(k2_relat_1(B_1561),A_1562)
      | ~ v1_funct_1(B_1561)
      | ~ v1_relat_1(B_1561) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_68011,plain,(
    ! [B_1561,A_1562] :
      ( r1_tarski(B_1561,k2_zfmisc_1(k1_relat_1(B_1561),A_1562))
      | ~ r1_tarski(k2_relat_1(B_1561),A_1562)
      | ~ v1_funct_1(B_1561)
      | ~ v1_relat_1(B_1561) ) ),
    inference(resolution,[status(thm)],[c_67980,c_50])).

tff(c_141014,plain,(
    ! [A_1562] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,A_1562))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1562)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140693,c_68011])).

tff(c_141285,plain,(
    ! [A_1562] :
      ( r1_tarski('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_120,c_28,c_141014])).

tff(c_142017,plain,(
    ! [A_2733] : ~ r1_tarski(k2_relat_1('#skF_4'),A_2733) ),
    inference(negUnitSimplification,[status(thm)],[c_67763,c_141285])).

tff(c_142049,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70883,c_142017])).

tff(c_142085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_142049])).

tff(c_142087,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_67762])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_238,plain,(
    ! [B_113,A_114] :
      ( B_113 = A_114
      | ~ r1_tarski(B_113,A_114)
      | ~ r1_tarski(A_114,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_238])).

tff(c_142133,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142087,c_264])).

tff(c_142164,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142133,c_8])).

tff(c_72,plain,(
    ! [A_57] : k9_relat_1(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_142162,plain,(
    ! [A_57] : k9_relat_1('#skF_4',A_57) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142133,c_142133,c_72])).

tff(c_142088,plain,(
    ! [A_2734,B_2735,C_2736,D_2737] :
      ( k7_relset_1(A_2734,B_2735,C_2736,D_2737) = k9_relat_1(C_2736,D_2737)
      | ~ m1_subset_1(C_2736,k1_zfmisc_1(k2_zfmisc_1(A_2734,B_2735))) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_142102,plain,(
    ! [D_2737] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_2737) = k9_relat_1('#skF_4',D_2737) ),
    inference(resolution,[status(thm)],[c_116,c_142088])).

tff(c_142327,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142102,c_112])).

tff(c_142562,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142162,c_142327])).

tff(c_142567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142164,c_142562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:07:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.27/27.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.27/27.57  
% 38.27/27.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.27/27.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 38.27/27.57  
% 38.27/27.57  %Foreground sorts:
% 38.27/27.57  
% 38.27/27.57  
% 38.27/27.57  %Background operators:
% 38.27/27.57  
% 38.27/27.57  
% 38.27/27.57  %Foreground operators:
% 38.27/27.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 38.27/27.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.27/27.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.27/27.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.27/27.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 38.27/27.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 38.27/27.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 38.27/27.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 38.27/27.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.27/27.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 38.27/27.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 38.27/27.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 38.27/27.57  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 38.27/27.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 38.27/27.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 38.27/27.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 38.27/27.57  tff('#skF_2', type, '#skF_2': $i).
% 38.27/27.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 38.27/27.57  tff('#skF_3', type, '#skF_3': $i).
% 38.27/27.57  tff('#skF_1', type, '#skF_1': $i).
% 38.27/27.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 38.27/27.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 38.27/27.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 38.27/27.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 38.27/27.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 38.27/27.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.27/27.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 38.27/27.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 38.27/27.57  tff('#skF_4', type, '#skF_4': $i).
% 38.27/27.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.27/27.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 38.27/27.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 38.27/27.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 38.27/27.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 38.27/27.57  
% 38.54/27.59  tff(f_113, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 38.54/27.59  tff(f_205, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 38.54/27.59  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 38.54/27.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 38.54/27.59  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 38.54/27.59  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 38.54/27.59  tff(f_121, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 38.54/27.59  tff(f_117, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 38.54/27.59  tff(f_86, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 38.54/27.59  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 38.54/27.59  tff(f_177, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 38.54/27.59  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 38.54/27.59  tff(f_158, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 38.54/27.59  tff(f_181, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 38.54/27.59  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 38.54/27.59  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 38.54/27.59  tff(f_80, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 38.54/27.59  tff(f_193, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 38.54/27.59  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 38.54/27.59  tff(f_123, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 38.54/27.59  tff(c_66, plain, (![A_51, B_52]: (v1_relat_1(k2_zfmisc_1(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 38.54/27.59  tff(c_116, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 38.54/27.59  tff(c_282, plain, (![B_116, A_117]: (v1_relat_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_99])).
% 38.54/27.59  tff(c_288, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_116, c_282])).
% 38.54/27.59  tff(c_295, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_288])).
% 38.54/27.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.54/27.59  tff(c_784, plain, (![B_188, A_189]: (v4_relat_1(B_188, A_189) | ~r1_tarski(k1_relat_1(B_188), A_189) | ~v1_relat_1(B_188))), inference(cnfTransformation, [status(thm)], [f_105])).
% 38.54/27.59  tff(c_799, plain, (![B_190]: (v4_relat_1(B_190, k1_relat_1(B_190)) | ~v1_relat_1(B_190))), inference(resolution, [status(thm)], [c_6, c_784])).
% 38.54/27.59  tff(c_74, plain, (![B_59, A_58]: (k7_relat_1(B_59, A_58)=B_59 | ~v4_relat_1(B_59, A_58) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_129])).
% 38.54/27.59  tff(c_809, plain, (![B_191]: (k7_relat_1(B_191, k1_relat_1(B_191))=B_191 | ~v1_relat_1(B_191))), inference(resolution, [status(thm)], [c_799, c_74])).
% 38.54/27.59  tff(c_70, plain, (![B_56, A_55]: (k2_relat_1(k7_relat_1(B_56, A_55))=k9_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_121])).
% 38.54/27.59  tff(c_819, plain, (![B_191]: (k9_relat_1(B_191, k1_relat_1(B_191))=k2_relat_1(B_191) | ~v1_relat_1(B_191) | ~v1_relat_1(B_191))), inference(superposition, [status(thm), theory('equality')], [c_809, c_70])).
% 38.54/27.59  tff(c_67559, plain, (![B_1520]: (k9_relat_1(B_1520, k1_relat_1(B_1520))=k2_relat_1(B_1520) | ~v1_relat_1(B_1520) | ~v1_relat_1(B_1520))), inference(superposition, [status(thm), theory('equality')], [c_809, c_70])).
% 38.54/27.59  tff(c_68, plain, (![B_54, A_53]: (r1_tarski(k9_relat_1(B_54, A_53), k9_relat_1(B_54, k1_relat_1(B_54))) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_117])).
% 38.54/27.59  tff(c_69198, plain, (![B_1662, A_1663]: (r1_tarski(k9_relat_1(B_1662, A_1663), k2_relat_1(B_1662)) | ~v1_relat_1(B_1662) | ~v1_relat_1(B_1662) | ~v1_relat_1(B_1662))), inference(superposition, [status(thm), theory('equality')], [c_67559, c_68])).
% 38.54/27.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.54/27.59  tff(c_70779, plain, (![B_1733, A_1734]: (k9_relat_1(B_1733, A_1734)=k2_relat_1(B_1733) | ~r1_tarski(k2_relat_1(B_1733), k9_relat_1(B_1733, A_1734)) | ~v1_relat_1(B_1733))), inference(resolution, [status(thm)], [c_69198, c_2])).
% 38.54/27.59  tff(c_70791, plain, (![B_191]: (k9_relat_1(B_191, k1_relat_1(B_191))=k2_relat_1(B_191) | ~r1_tarski(k2_relat_1(B_191), k2_relat_1(B_191)) | ~v1_relat_1(B_191) | ~v1_relat_1(B_191) | ~v1_relat_1(B_191))), inference(superposition, [status(thm), theory('equality')], [c_819, c_70779])).
% 38.54/27.59  tff(c_70832, plain, (![B_1735]: (k9_relat_1(B_1735, k1_relat_1(B_1735))=k2_relat_1(B_1735) | ~v1_relat_1(B_1735))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_70791])).
% 38.54/27.59  tff(c_70883, plain, (![B_1735]: (r1_tarski(k2_relat_1(B_1735), k9_relat_1(B_1735, k1_relat_1(B_1735))) | ~v1_relat_1(B_1735) | ~v1_relat_1(B_1735))), inference(superposition, [status(thm), theory('equality')], [c_70832, c_68])).
% 38.54/27.59  tff(c_52, plain, (![A_39, B_40]: (m1_subset_1(A_39, k1_zfmisc_1(B_40)) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_86])).
% 38.54/27.59  tff(c_28, plain, (![B_33]: (k2_zfmisc_1(k1_xboole_0, B_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 38.54/27.59  tff(c_419, plain, (![C_144, B_145, A_146]: (v5_relat_1(C_144, B_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 38.54/27.59  tff(c_469, plain, (![C_151, B_152]: (v5_relat_1(C_151, B_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_419])).
% 38.54/27.59  tff(c_476, plain, (![A_39, B_152]: (v5_relat_1(A_39, B_152) | ~r1_tarski(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_469])).
% 38.54/27.60  tff(c_64, plain, (![B_50, A_49]: (r1_tarski(k2_relat_1(B_50), A_49) | ~v5_relat_1(B_50, A_49) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_111])).
% 38.54/27.60  tff(c_67429, plain, (![B_1513]: (k9_relat_1(B_1513, k1_relat_1(B_1513))=k2_relat_1(B_1513) | ~v1_relat_1(B_1513) | ~v1_relat_1(B_1513))), inference(superposition, [status(thm), theory('equality')], [c_809, c_70])).
% 38.54/27.60  tff(c_503, plain, (![C_158, A_159, B_160]: (v4_relat_1(C_158, A_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 38.54/27.60  tff(c_522, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_116, c_503])).
% 38.54/27.60  tff(c_534, plain, (![B_164, A_165]: (k7_relat_1(B_164, A_165)=B_164 | ~v4_relat_1(B_164, A_165) | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_129])).
% 38.54/27.60  tff(c_537, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_522, c_534])).
% 38.54/27.60  tff(c_543, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_537])).
% 38.54/27.60  tff(c_562, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_543, c_70])).
% 38.54/27.60  tff(c_566, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_562])).
% 38.54/27.60  tff(c_865, plain, (![B_193, A_194]: (r1_tarski(k9_relat_1(B_193, A_194), k9_relat_1(B_193, k1_relat_1(B_193))) | ~v1_relat_1(B_193))), inference(cnfTransformation, [status(thm)], [f_117])).
% 38.54/27.60  tff(c_873, plain, (r1_tarski(k2_relat_1('#skF_4'), k9_relat_1('#skF_4', k1_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_566, c_865])).
% 38.54/27.60  tff(c_887, plain, (r1_tarski(k2_relat_1('#skF_4'), k9_relat_1('#skF_4', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_873])).
% 38.54/27.60  tff(c_906, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4') | ~r1_tarski(k9_relat_1('#skF_4', k1_relat_1('#skF_4')), k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_887, c_2])).
% 38.54/27.60  tff(c_67427, plain, (~r1_tarski(k9_relat_1('#skF_4', k1_relat_1('#skF_4')), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_906])).
% 38.54/27.60  tff(c_67435, plain, (~r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67429, c_67427])).
% 38.54/27.60  tff(c_67468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_295, c_6, c_67435])).
% 38.54/27.60  tff(c_67469, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_906])).
% 38.54/27.60  tff(c_67482, plain, (![A_53]: (r1_tarski(k9_relat_1('#skF_4', A_53), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67469, c_68])).
% 38.54/27.60  tff(c_67502, plain, (![A_1517]: (r1_tarski(k9_relat_1('#skF_4', A_1517), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_67482])).
% 38.54/27.60  tff(c_67698, plain, (![A_1534]: (k9_relat_1('#skF_4', A_1534)=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), k9_relat_1('#skF_4', A_1534)))), inference(resolution, [status(thm)], [c_67502, c_2])).
% 38.54/27.60  tff(c_67708, plain, (![A_1534]: (k9_relat_1('#skF_4', A_1534)=k2_relat_1('#skF_4') | ~v5_relat_1('#skF_4', k9_relat_1('#skF_4', A_1534)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_67698])).
% 38.54/27.60  tff(c_67742, plain, (![A_1537]: (k9_relat_1('#skF_4', A_1537)=k2_relat_1('#skF_4') | ~v5_relat_1('#skF_4', k9_relat_1('#skF_4', A_1537)))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_67708])).
% 38.54/27.60  tff(c_67762, plain, (![A_1537]: (k9_relat_1('#skF_4', A_1537)=k2_relat_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_476, c_67742])).
% 38.54/27.60  tff(c_67763, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_67762])).
% 38.54/27.60  tff(c_120, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 38.54/27.60  tff(c_67488, plain, (![A_53]: (r1_tarski(k9_relat_1('#skF_4', A_53), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_67482])).
% 38.54/27.60  tff(c_67798, plain, (![B_1546, A_1547]: (k1_tarski(k1_funct_1(B_1546, A_1547))=k2_relat_1(B_1546) | k1_tarski(A_1547)!=k1_relat_1(B_1546) | ~v1_funct_1(B_1546) | ~v1_relat_1(B_1546))), inference(cnfTransformation, [status(thm)], [f_158])).
% 38.54/27.60  tff(c_67764, plain, (![A_1538, B_1539, C_1540, D_1541]: (k7_relset_1(A_1538, B_1539, C_1540, D_1541)=k9_relat_1(C_1540, D_1541) | ~m1_subset_1(C_1540, k1_zfmisc_1(k2_zfmisc_1(A_1538, B_1539))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 38.54/27.60  tff(c_67778, plain, (![D_1541]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_1541)=k9_relat_1('#skF_4', D_1541))), inference(resolution, [status(thm)], [c_116, c_67764])).
% 38.54/27.60  tff(c_112, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 38.54/27.60  tff(c_67788, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67778, c_112])).
% 38.54/27.60  tff(c_67804, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67798, c_67788])).
% 38.54/27.60  tff(c_67828, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_120, c_67488, c_67804])).
% 38.54/27.60  tff(c_60, plain, (![B_48, A_47]: (r1_tarski(k1_relat_1(B_48), A_47) | ~v4_relat_1(B_48, A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_105])).
% 38.54/27.60  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 38.54/27.60  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.54/27.60  tff(c_68274, plain, (![A_1600, B_1601, C_1602, D_1603]: (k1_enumset1(A_1600, B_1601, C_1602)=D_1603 | k2_tarski(A_1600, C_1602)=D_1603 | k2_tarski(B_1601, C_1602)=D_1603 | k2_tarski(A_1600, B_1601)=D_1603 | k1_tarski(C_1602)=D_1603 | k1_tarski(B_1601)=D_1603 | k1_tarski(A_1600)=D_1603 | k1_xboole_0=D_1603 | ~r1_tarski(D_1603, k1_enumset1(A_1600, B_1601, C_1602)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 38.54/27.60  tff(c_68300, plain, (![A_5, B_6, D_1603]: (k1_enumset1(A_5, A_5, B_6)=D_1603 | k2_tarski(A_5, B_6)=D_1603 | k2_tarski(A_5, B_6)=D_1603 | k2_tarski(A_5, A_5)=D_1603 | k1_tarski(B_6)=D_1603 | k1_tarski(A_5)=D_1603 | k1_tarski(A_5)=D_1603 | k1_xboole_0=D_1603 | ~r1_tarski(D_1603, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_68274])).
% 38.54/27.60  tff(c_75851, plain, (![A_1891, B_1892, D_1893]: (k2_tarski(A_1891, B_1892)=D_1893 | k2_tarski(A_1891, B_1892)=D_1893 | k2_tarski(A_1891, B_1892)=D_1893 | k1_tarski(A_1891)=D_1893 | k1_tarski(B_1892)=D_1893 | k1_tarski(A_1891)=D_1893 | k1_tarski(A_1891)=D_1893 | k1_xboole_0=D_1893 | ~r1_tarski(D_1893, k2_tarski(A_1891, B_1892)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_68300])).
% 38.54/27.60  tff(c_75876, plain, (![A_4, D_1893]: (k2_tarski(A_4, A_4)=D_1893 | k2_tarski(A_4, A_4)=D_1893 | k2_tarski(A_4, A_4)=D_1893 | k1_tarski(A_4)=D_1893 | k1_tarski(A_4)=D_1893 | k1_tarski(A_4)=D_1893 | k1_tarski(A_4)=D_1893 | k1_xboole_0=D_1893 | ~r1_tarski(D_1893, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_75851])).
% 38.54/27.60  tff(c_140113, plain, (![A_2717, D_2718]: (k1_tarski(A_2717)=D_2718 | k1_tarski(A_2717)=D_2718 | k1_tarski(A_2717)=D_2718 | k1_tarski(A_2717)=D_2718 | k1_tarski(A_2717)=D_2718 | k1_tarski(A_2717)=D_2718 | k1_tarski(A_2717)=D_2718 | k1_xboole_0=D_2718 | ~r1_tarski(D_2718, k1_tarski(A_2717)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_75876])).
% 38.54/27.60  tff(c_140531, plain, (![A_2725, B_2726]: (k1_tarski(A_2725)=k1_relat_1(B_2726) | k1_relat_1(B_2726)=k1_xboole_0 | ~v4_relat_1(B_2726, k1_tarski(A_2725)) | ~v1_relat_1(B_2726))), inference(resolution, [status(thm)], [c_60, c_140113])).
% 38.54/27.60  tff(c_140648, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_522, c_140531])).
% 38.54/27.60  tff(c_140692, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_295, c_140648])).
% 38.54/27.60  tff(c_140693, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_67828, c_140692])).
% 38.54/27.60  tff(c_67980, plain, (![B_1561, A_1562]: (m1_subset_1(B_1561, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1561), A_1562))) | ~r1_tarski(k2_relat_1(B_1561), A_1562) | ~v1_funct_1(B_1561) | ~v1_relat_1(B_1561))), inference(cnfTransformation, [status(thm)], [f_193])).
% 38.54/27.60  tff(c_50, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 38.54/27.60  tff(c_68011, plain, (![B_1561, A_1562]: (r1_tarski(B_1561, k2_zfmisc_1(k1_relat_1(B_1561), A_1562)) | ~r1_tarski(k2_relat_1(B_1561), A_1562) | ~v1_funct_1(B_1561) | ~v1_relat_1(B_1561))), inference(resolution, [status(thm)], [c_67980, c_50])).
% 38.54/27.60  tff(c_141014, plain, (![A_1562]: (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, A_1562)) | ~r1_tarski(k2_relat_1('#skF_4'), A_1562) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_140693, c_68011])).
% 38.54/27.60  tff(c_141285, plain, (![A_1562]: (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski(k2_relat_1('#skF_4'), A_1562))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_120, c_28, c_141014])).
% 38.54/27.60  tff(c_142017, plain, (![A_2733]: (~r1_tarski(k2_relat_1('#skF_4'), A_2733))), inference(negUnitSimplification, [status(thm)], [c_67763, c_141285])).
% 38.54/27.60  tff(c_142049, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70883, c_142017])).
% 38.54/27.60  tff(c_142085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_142049])).
% 38.54/27.60  tff(c_142087, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_67762])).
% 38.54/27.60  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 38.54/27.60  tff(c_238, plain, (![B_113, A_114]: (B_113=A_114 | ~r1_tarski(B_113, A_114) | ~r1_tarski(A_114, B_113))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.54/27.60  tff(c_264, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_238])).
% 38.54/27.60  tff(c_142133, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_142087, c_264])).
% 38.54/27.60  tff(c_142164, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_142133, c_8])).
% 38.54/27.60  tff(c_72, plain, (![A_57]: (k9_relat_1(k1_xboole_0, A_57)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_123])).
% 38.54/27.60  tff(c_142162, plain, (![A_57]: (k9_relat_1('#skF_4', A_57)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142133, c_142133, c_72])).
% 38.54/27.60  tff(c_142088, plain, (![A_2734, B_2735, C_2736, D_2737]: (k7_relset_1(A_2734, B_2735, C_2736, D_2737)=k9_relat_1(C_2736, D_2737) | ~m1_subset_1(C_2736, k1_zfmisc_1(k2_zfmisc_1(A_2734, B_2735))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 38.54/27.60  tff(c_142102, plain, (![D_2737]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_2737)=k9_relat_1('#skF_4', D_2737))), inference(resolution, [status(thm)], [c_116, c_142088])).
% 38.54/27.60  tff(c_142327, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_142102, c_112])).
% 38.54/27.60  tff(c_142562, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_142162, c_142327])).
% 38.54/27.60  tff(c_142567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142164, c_142562])).
% 38.54/27.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.54/27.60  
% 38.54/27.60  Inference rules
% 38.54/27.60  ----------------------
% 38.54/27.60  #Ref     : 0
% 38.54/27.60  #Sup     : 31579
% 38.54/27.60  #Fact    : 0
% 38.54/27.60  #Define  : 0
% 38.54/27.60  #Split   : 52
% 38.54/27.60  #Chain   : 0
% 38.54/27.60  #Close   : 0
% 38.54/27.60  
% 38.54/27.60  Ordering : KBO
% 38.54/27.60  
% 38.54/27.60  Simplification rules
% 38.54/27.60  ----------------------
% 38.54/27.60  #Subsume      : 10570
% 38.54/27.60  #Demod        : 41398
% 38.54/27.60  #Tautology    : 7755
% 38.54/27.60  #SimpNegUnit  : 926
% 38.54/27.60  #BackRed      : 386
% 38.54/27.60  
% 38.54/27.60  #Partial instantiations: 0
% 38.54/27.60  #Strategies tried      : 1
% 38.54/27.60  
% 38.54/27.60  Timing (in seconds)
% 38.54/27.60  ----------------------
% 38.54/27.60  Preprocessing        : 0.39
% 38.54/27.60  Parsing              : 0.20
% 38.54/27.60  CNF conversion       : 0.03
% 38.54/27.60  Main loop            : 26.45
% 38.54/27.60  Inferencing          : 3.67
% 38.54/27.60  Reduction            : 10.48
% 38.54/27.60  Demodulation         : 8.62
% 38.54/27.60  BG Simplification    : 0.45
% 38.54/27.60  Subsumption          : 10.90
% 38.54/27.60  Abstraction          : 0.86
% 38.54/27.60  MUC search           : 0.00
% 38.54/27.60  Cooper               : 0.00
% 38.54/27.60  Total                : 26.88
% 38.54/27.60  Index Insertion      : 0.00
% 38.54/27.60  Index Deletion       : 0.00
% 38.54/27.60  Index Matching       : 0.00
% 38.54/27.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
