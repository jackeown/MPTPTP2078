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
% DateTime   : Thu Dec  3 10:12:00 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 250 expanded)
%              Number of leaves         :   38 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 ( 759 expanded)
%              Number of equality atoms :   63 ( 204 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_140,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
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

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_80,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_86])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_89,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_89])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_163,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_176,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_163])).

tff(c_242,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1(k2_relset_1(A_80,B_81,C_82),k1_zfmisc_1(B_81))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_262,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_242])).

tff(c_274,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_262])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_284,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_274,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_290,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_284,c_2])).

tff(c_1733,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_2871,plain,(
    ! [F_282,A_280,D_281,C_283,E_279,B_284] :
      ( k1_partfun1(A_280,B_284,C_283,D_281,E_279,F_282) = k5_relat_1(E_279,F_282)
      | ~ m1_subset_1(F_282,k1_zfmisc_1(k2_zfmisc_1(C_283,D_281)))
      | ~ v1_funct_1(F_282)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_280,B_284)))
      | ~ v1_funct_1(E_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2894,plain,(
    ! [A_280,B_284,E_279] :
      ( k1_partfun1(A_280,B_284,'#skF_2','#skF_3',E_279,'#skF_5') = k5_relat_1(E_279,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_280,B_284)))
      | ~ v1_funct_1(E_279) ) ),
    inference(resolution,[status(thm)],[c_52,c_2871])).

tff(c_3113,plain,(
    ! [A_287,B_288,E_289] :
      ( k1_partfun1(A_287,B_288,'#skF_2','#skF_3',E_289,'#skF_5') = k5_relat_1(E_289,'#skF_5')
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_1(E_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2894])).

tff(c_3146,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3113])).

tff(c_3161,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3146])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_663,plain,(
    ! [A_134,F_135,C_136,E_133,B_132,D_131] :
      ( k4_relset_1(A_134,B_132,C_136,D_131,E_133,F_135) = k5_relat_1(E_133,F_135)
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_136,D_131)))
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_991,plain,(
    ! [A_160,B_161,E_162] :
      ( k4_relset_1(A_160,B_161,'#skF_2','#skF_3',E_162,'#skF_5') = k5_relat_1(E_162,'#skF_5')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(resolution,[status(thm)],[c_52,c_663])).

tff(c_1021,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_991])).

tff(c_22,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( m1_subset_1(k4_relset_1(A_19,B_20,C_21,D_22,E_23,F_24),k1_zfmisc_1(k2_zfmisc_1(A_19,D_22)))
      | ~ m1_subset_1(F_24,k1_zfmisc_1(k2_zfmisc_1(C_21,D_22)))
      | ~ m1_subset_1(E_23,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1141,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_22])).

tff(c_1145,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1141])).

tff(c_1197,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1145,c_8])).

tff(c_1106,plain,(
    ! [F_166,E_163,D_165,C_167,A_164,B_168] :
      ( k1_partfun1(A_164,B_168,C_167,D_165,E_163,F_166) = k5_relat_1(E_163,F_166)
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(C_167,D_165)))
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_168)))
      | ~ v1_funct_1(E_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1125,plain,(
    ! [A_164,B_168,E_163] :
      ( k1_partfun1(A_164,B_168,'#skF_2','#skF_3',E_163,'#skF_5') = k5_relat_1(E_163,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_168)))
      | ~ v1_funct_1(E_163) ) ),
    inference(resolution,[status(thm)],[c_52,c_1106])).

tff(c_1648,plain,(
    ! [A_180,B_181,E_182] :
      ( k1_partfun1(A_180,B_181,'#skF_2','#skF_3',E_182,'#skF_5') = k5_relat_1(E_182,'#skF_5')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_1(E_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1125])).

tff(c_1678,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1648])).

tff(c_1692,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1678])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_268,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_242])).

tff(c_322,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_410,plain,(
    ~ r1_tarski(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_322])).

tff(c_1696,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_410])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1696])).

tff(c_1703,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_26,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1716,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1703,c_26])).

tff(c_1727,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1716])).

tff(c_3180,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_1727])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3216,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3180,c_16])).

tff(c_3238,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_96,c_3216])).

tff(c_3240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1733,c_3238])).

tff(c_3241,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_48,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_141,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_154,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_141])).

tff(c_3509,plain,(
    ! [B_324,A_325,C_326] :
      ( k1_xboole_0 = B_324
      | k1_relset_1(A_325,B_324,C_326) = A_325
      | ~ v1_funct_2(C_326,A_325,B_324)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3526,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3509])).

tff(c_3537,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_154,c_3526])).

tff(c_3538,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3537])).

tff(c_3768,plain,(
    ! [A_345,B_346] :
      ( r1_tarski(k1_relat_1(A_345),k2_relat_1(B_346))
      | ~ v2_funct_1(A_345)
      | k2_relat_1(k5_relat_1(B_346,A_345)) != k2_relat_1(A_345)
      | ~ v1_funct_1(B_346)
      | ~ v1_relat_1(B_346)
      | ~ v1_funct_1(A_345)
      | ~ v1_relat_1(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3783,plain,(
    ! [B_346] :
      ( r1_tarski('#skF_2',k2_relat_1(B_346))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_346,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_346)
      | ~ v1_relat_1(B_346)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3538,c_3768])).

tff(c_3808,plain,(
    ! [B_349] :
      ( r1_tarski('#skF_2',k2_relat_1(B_349))
      | k2_relat_1(k5_relat_1(B_349,'#skF_5')) != '#skF_3'
      | ~ v1_funct_1(B_349)
      | ~ v1_relat_1(B_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_56,c_3241,c_48,c_3783])).

tff(c_175,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_177,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_44])).

tff(c_265,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_242])).

tff(c_276,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_265])).

tff(c_299,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_276,c_8])).

tff(c_301,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_299,c_2])).

tff(c_307,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_301])).

tff(c_3815,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3808,c_307])).

tff(c_3832,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_3815])).

tff(c_4375,plain,(
    ! [C_386,A_383,E_382,D_384,F_385,B_387] :
      ( k1_partfun1(A_383,B_387,C_386,D_384,E_382,F_385) = k5_relat_1(E_382,F_385)
      | ~ m1_subset_1(F_385,k1_zfmisc_1(k2_zfmisc_1(C_386,D_384)))
      | ~ v1_funct_1(F_385)
      | ~ m1_subset_1(E_382,k1_zfmisc_1(k2_zfmisc_1(A_383,B_387)))
      | ~ v1_funct_1(E_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4398,plain,(
    ! [A_383,B_387,E_382] :
      ( k1_partfun1(A_383,B_387,'#skF_2','#skF_3',E_382,'#skF_5') = k5_relat_1(E_382,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_382,k1_zfmisc_1(k2_zfmisc_1(A_383,B_387)))
      | ~ v1_funct_1(E_382) ) ),
    inference(resolution,[status(thm)],[c_52,c_4375])).

tff(c_4605,plain,(
    ! [A_390,B_391,E_392] :
      ( k1_partfun1(A_390,B_391,'#skF_2','#skF_3',E_392,'#skF_5') = k5_relat_1(E_392,'#skF_5')
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391)))
      | ~ v1_funct_1(E_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4398])).

tff(c_4638,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_4605])).

tff(c_4653,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4638])).

tff(c_4671,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4653,c_1727])).

tff(c_4677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3832,c_4671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.28  
% 6.45/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.28  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.45/2.28  
% 6.45/2.28  %Foreground sorts:
% 6.45/2.28  
% 6.45/2.28  
% 6.45/2.28  %Background operators:
% 6.45/2.28  
% 6.45/2.28  
% 6.45/2.28  %Foreground operators:
% 6.45/2.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.45/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.45/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.45/2.28  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.45/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.45/2.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.45/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.45/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.45/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.45/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.45/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.45/2.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.45/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.45/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.45/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.45/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.45/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.28  
% 6.79/2.31  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.79/2.31  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 6.79/2.31  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.79/2.31  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.79/2.31  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.79/2.31  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.79/2.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.79/2.31  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.79/2.31  tff(f_90, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 6.79/2.31  tff(f_76, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 6.79/2.31  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 6.79/2.31  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.79/2.31  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.79/2.31  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_1)).
% 6.79/2.31  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.79/2.31  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_80, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.79/2.31  tff(c_86, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_80])).
% 6.79/2.31  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_86])).
% 6.79/2.31  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_89, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_80])).
% 6.79/2.31  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_89])).
% 6.79/2.31  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_163, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.79/2.31  tff(c_176, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_163])).
% 6.79/2.31  tff(c_242, plain, (![A_80, B_81, C_82]: (m1_subset_1(k2_relset_1(A_80, B_81, C_82), k1_zfmisc_1(B_81)) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.79/2.31  tff(c_262, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_176, c_242])).
% 6.79/2.31  tff(c_274, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_262])).
% 6.79/2.31  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.79/2.31  tff(c_284, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_274, c_8])).
% 6.79/2.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.79/2.31  tff(c_290, plain, (k2_relat_1('#skF_5')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_284, c_2])).
% 6.79/2.31  tff(c_1733, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_290])).
% 6.79/2.31  tff(c_2871, plain, (![F_282, A_280, D_281, C_283, E_279, B_284]: (k1_partfun1(A_280, B_284, C_283, D_281, E_279, F_282)=k5_relat_1(E_279, F_282) | ~m1_subset_1(F_282, k1_zfmisc_1(k2_zfmisc_1(C_283, D_281))) | ~v1_funct_1(F_282) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_280, B_284))) | ~v1_funct_1(E_279))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.79/2.31  tff(c_2894, plain, (![A_280, B_284, E_279]: (k1_partfun1(A_280, B_284, '#skF_2', '#skF_3', E_279, '#skF_5')=k5_relat_1(E_279, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_280, B_284))) | ~v1_funct_1(E_279))), inference(resolution, [status(thm)], [c_52, c_2871])).
% 6.79/2.31  tff(c_3113, plain, (![A_287, B_288, E_289]: (k1_partfun1(A_287, B_288, '#skF_2', '#skF_3', E_289, '#skF_5')=k5_relat_1(E_289, '#skF_5') | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_1(E_289))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2894])).
% 6.79/2.31  tff(c_3146, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3113])).
% 6.79/2.31  tff(c_3161, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3146])).
% 6.79/2.31  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_663, plain, (![A_134, F_135, C_136, E_133, B_132, D_131]: (k4_relset_1(A_134, B_132, C_136, D_131, E_133, F_135)=k5_relat_1(E_133, F_135) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_136, D_131))) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.79/2.31  tff(c_991, plain, (![A_160, B_161, E_162]: (k4_relset_1(A_160, B_161, '#skF_2', '#skF_3', E_162, '#skF_5')=k5_relat_1(E_162, '#skF_5') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(resolution, [status(thm)], [c_52, c_663])).
% 6.79/2.31  tff(c_1021, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_991])).
% 6.79/2.31  tff(c_22, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (m1_subset_1(k4_relset_1(A_19, B_20, C_21, D_22, E_23, F_24), k1_zfmisc_1(k2_zfmisc_1(A_19, D_22))) | ~m1_subset_1(F_24, k1_zfmisc_1(k2_zfmisc_1(C_21, D_22))) | ~m1_subset_1(E_23, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.79/2.31  tff(c_1141, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1021, c_22])).
% 6.79/2.31  tff(c_1145, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_1141])).
% 6.79/2.31  tff(c_1197, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1145, c_8])).
% 6.79/2.31  tff(c_1106, plain, (![F_166, E_163, D_165, C_167, A_164, B_168]: (k1_partfun1(A_164, B_168, C_167, D_165, E_163, F_166)=k5_relat_1(E_163, F_166) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(C_167, D_165))) | ~v1_funct_1(F_166) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_168))) | ~v1_funct_1(E_163))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.79/2.31  tff(c_1125, plain, (![A_164, B_168, E_163]: (k1_partfun1(A_164, B_168, '#skF_2', '#skF_3', E_163, '#skF_5')=k5_relat_1(E_163, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_168))) | ~v1_funct_1(E_163))), inference(resolution, [status(thm)], [c_52, c_1106])).
% 6.79/2.31  tff(c_1648, plain, (![A_180, B_181, E_182]: (k1_partfun1(A_180, B_181, '#skF_2', '#skF_3', E_182, '#skF_5')=k5_relat_1(E_182, '#skF_5') | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_1(E_182))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1125])).
% 6.79/2.31  tff(c_1678, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1648])).
% 6.79/2.31  tff(c_1692, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1678])).
% 6.79/2.31  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.79/2.31  tff(c_268, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_242])).
% 6.79/2.31  tff(c_322, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_268])).
% 6.79/2.31  tff(c_410, plain, (~r1_tarski(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_322])).
% 6.79/2.31  tff(c_1696, plain, (~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_410])).
% 6.79/2.31  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1696])).
% 6.79/2.31  tff(c_1703, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_268])).
% 6.79/2.31  tff(c_26, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.79/2.31  tff(c_1716, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1703, c_26])).
% 6.79/2.31  tff(c_1727, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1716])).
% 6.79/2.31  tff(c_3180, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_1727])).
% 6.79/2.31  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.79/2.31  tff(c_3216, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3180, c_16])).
% 6.79/2.31  tff(c_3238, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_96, c_3216])).
% 6.79/2.31  tff(c_3240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1733, c_3238])).
% 6.79/2.31  tff(c_3241, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_290])).
% 6.79/2.31  tff(c_48, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_141, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.79/2.31  tff(c_154, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_141])).
% 6.79/2.31  tff(c_3509, plain, (![B_324, A_325, C_326]: (k1_xboole_0=B_324 | k1_relset_1(A_325, B_324, C_326)=A_325 | ~v1_funct_2(C_326, A_325, B_324) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_325, B_324))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.79/2.31  tff(c_3526, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_3509])).
% 6.79/2.31  tff(c_3537, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_154, c_3526])).
% 6.79/2.31  tff(c_3538, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_3537])).
% 6.79/2.31  tff(c_3768, plain, (![A_345, B_346]: (r1_tarski(k1_relat_1(A_345), k2_relat_1(B_346)) | ~v2_funct_1(A_345) | k2_relat_1(k5_relat_1(B_346, A_345))!=k2_relat_1(A_345) | ~v1_funct_1(B_346) | ~v1_relat_1(B_346) | ~v1_funct_1(A_345) | ~v1_relat_1(A_345))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.79/2.31  tff(c_3783, plain, (![B_346]: (r1_tarski('#skF_2', k2_relat_1(B_346)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_346, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_346) | ~v1_relat_1(B_346) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3538, c_3768])).
% 6.79/2.31  tff(c_3808, plain, (![B_349]: (r1_tarski('#skF_2', k2_relat_1(B_349)) | k2_relat_1(k5_relat_1(B_349, '#skF_5'))!='#skF_3' | ~v1_funct_1(B_349) | ~v1_relat_1(B_349))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_56, c_3241, c_48, c_3783])).
% 6.79/2.31  tff(c_175, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_163])).
% 6.79/2.31  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.79/2.31  tff(c_177, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_44])).
% 6.79/2.31  tff(c_265, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_175, c_242])).
% 6.79/2.31  tff(c_276, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_265])).
% 6.79/2.31  tff(c_299, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_276, c_8])).
% 6.79/2.31  tff(c_301, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_299, c_2])).
% 6.79/2.31  tff(c_307, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_177, c_301])).
% 6.79/2.31  tff(c_3815, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3808, c_307])).
% 6.79/2.31  tff(c_3832, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_3815])).
% 6.79/2.31  tff(c_4375, plain, (![C_386, A_383, E_382, D_384, F_385, B_387]: (k1_partfun1(A_383, B_387, C_386, D_384, E_382, F_385)=k5_relat_1(E_382, F_385) | ~m1_subset_1(F_385, k1_zfmisc_1(k2_zfmisc_1(C_386, D_384))) | ~v1_funct_1(F_385) | ~m1_subset_1(E_382, k1_zfmisc_1(k2_zfmisc_1(A_383, B_387))) | ~v1_funct_1(E_382))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.79/2.31  tff(c_4398, plain, (![A_383, B_387, E_382]: (k1_partfun1(A_383, B_387, '#skF_2', '#skF_3', E_382, '#skF_5')=k5_relat_1(E_382, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_382, k1_zfmisc_1(k2_zfmisc_1(A_383, B_387))) | ~v1_funct_1(E_382))), inference(resolution, [status(thm)], [c_52, c_4375])).
% 6.79/2.31  tff(c_4605, plain, (![A_390, B_391, E_392]: (k1_partfun1(A_390, B_391, '#skF_2', '#skF_3', E_392, '#skF_5')=k5_relat_1(E_392, '#skF_5') | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))) | ~v1_funct_1(E_392))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4398])).
% 6.79/2.31  tff(c_4638, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_4605])).
% 6.79/2.31  tff(c_4653, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4638])).
% 6.79/2.31  tff(c_4671, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4653, c_1727])).
% 6.79/2.31  tff(c_4677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3832, c_4671])).
% 6.79/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.31  
% 6.79/2.31  Inference rules
% 6.79/2.31  ----------------------
% 6.79/2.31  #Ref     : 0
% 6.79/2.31  #Sup     : 1012
% 6.79/2.31  #Fact    : 0
% 6.79/2.31  #Define  : 0
% 6.79/2.31  #Split   : 23
% 6.79/2.31  #Chain   : 0
% 6.79/2.31  #Close   : 0
% 6.79/2.31  
% 6.79/2.31  Ordering : KBO
% 6.79/2.31  
% 6.79/2.31  Simplification rules
% 6.79/2.31  ----------------------
% 6.79/2.31  #Subsume      : 104
% 6.79/2.31  #Demod        : 431
% 6.79/2.31  #Tautology    : 229
% 6.79/2.31  #SimpNegUnit  : 64
% 6.79/2.31  #BackRed      : 43
% 6.79/2.31  
% 6.79/2.31  #Partial instantiations: 0
% 6.79/2.31  #Strategies tried      : 1
% 6.79/2.31  
% 6.79/2.31  Timing (in seconds)
% 6.79/2.31  ----------------------
% 6.79/2.31  Preprocessing        : 0.36
% 6.79/2.31  Parsing              : 0.19
% 6.79/2.31  CNF conversion       : 0.03
% 6.79/2.31  Main loop            : 1.16
% 6.79/2.31  Inferencing          : 0.41
% 6.79/2.31  Reduction            : 0.39
% 6.79/2.31  Demodulation         : 0.28
% 6.79/2.31  BG Simplification    : 0.05
% 6.79/2.31  Subsumption          : 0.21
% 6.79/2.31  Abstraction          : 0.07
% 6.79/2.31  MUC search           : 0.00
% 6.79/2.31  Cooper               : 0.00
% 6.79/2.31  Total                : 1.57
% 6.79/2.31  Index Insertion      : 0.00
% 6.79/2.31  Index Deletion       : 0.00
% 6.79/2.31  Index Matching       : 0.00
% 6.79/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
