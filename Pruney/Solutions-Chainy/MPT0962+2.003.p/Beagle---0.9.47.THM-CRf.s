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
% DateTime   : Thu Dec  3 10:10:51 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :  200 (5009 expanded)
%              Number of leaves         :   33 (1660 expanded)
%              Depth                    :   18
%              Number of atoms          :  385 (12582 expanded)
%              Number of equality atoms :  165 (3473 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_72,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_7408,plain,(
    ! [C_2554,A_2555,B_2556] :
      ( m1_subset_1(C_2554,k1_zfmisc_1(k2_zfmisc_1(A_2555,B_2556)))
      | ~ r1_tarski(k2_relat_1(C_2554),B_2556)
      | ~ r1_tarski(k1_relat_1(C_2554),A_2555)
      | ~ v1_relat_1(C_2554) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_70,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66])).

tff(c_81,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_107,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_107])).

tff(c_123,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_24,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,k2_zfmisc_1(k1_relat_1(A_14),k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_97,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) != k1_xboole_0
      | k1_xboole_0 = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_105,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_97])).

tff(c_106,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_18,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_10,B_11] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_10,B_11)),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_538,plain,(
    ! [C_136,A_137,B_138] :
      ( m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ r1_tarski(k2_relat_1(C_136),B_138)
      | ~ r1_tarski(k1_relat_1(C_136),A_137)
      | ~ v1_relat_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_693,plain,(
    ! [C_158,A_159,B_160] :
      ( r1_tarski(C_158,k2_zfmisc_1(A_159,B_160))
      | ~ r1_tarski(k2_relat_1(C_158),B_160)
      | ~ r1_tarski(k1_relat_1(C_158),A_159)
      | ~ v1_relat_1(C_158) ) ),
    inference(resolution,[status(thm)],[c_538,c_14])).

tff(c_814,plain,(
    ! [C_166,A_167] :
      ( r1_tarski(C_166,k2_zfmisc_1(A_167,k2_relat_1(C_166)))
      | ~ r1_tarski(k1_relat_1(C_166),A_167)
      | ~ v1_relat_1(C_166) ) ),
    inference(resolution,[status(thm)],[c_8,c_693])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r1_tarski(k2_zfmisc_1(A_3,B_4),k2_zfmisc_1(A_3,C_5))
      | r1_tarski(B_4,C_5)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_848,plain,(
    ! [B_4,A_167] :
      ( r1_tarski(B_4,k2_relat_1(k2_zfmisc_1(A_167,B_4)))
      | k1_xboole_0 = A_167
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(A_167,B_4)),A_167)
      | ~ v1_relat_1(k2_zfmisc_1(A_167,B_4)) ) ),
    inference(resolution,[status(thm)],[c_814,c_10])).

tff(c_881,plain,(
    ! [B_168,A_169] :
      ( r1_tarski(B_168,k2_relat_1(k2_zfmisc_1(A_169,B_168)))
      | k1_xboole_0 = A_169 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_848])).

tff(c_22,plain,(
    ! [A_12,B_13] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_12,B_13)),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,(
    ! [A_12,B_13] :
      ( k2_relat_1(k2_zfmisc_1(A_12,B_13)) = B_13
      | ~ r1_tarski(B_13,k2_relat_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(resolution,[status(thm)],[c_22,c_107])).

tff(c_924,plain,(
    ! [A_170,B_171] :
      ( k2_relat_1(k2_zfmisc_1(A_170,B_171)) = B_171
      | k1_xboole_0 = A_170 ) ),
    inference(resolution,[status(thm)],[c_881,c_117])).

tff(c_82,plain,(
    ! [A_46] :
      ( k2_relat_1(A_46) != k1_xboole_0
      | k1_xboole_0 = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_89,plain,(
    ! [A_8,B_9] :
      ( k2_relat_1(k2_zfmisc_1(A_8,B_9)) != k1_xboole_0
      | k2_zfmisc_1(A_8,B_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_1016,plain,(
    ! [B_172,A_173] :
      ( k1_xboole_0 != B_172
      | k2_zfmisc_1(A_173,B_172) = k1_xboole_0
      | k1_xboole_0 = A_173 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_89])).

tff(c_706,plain,(
    ! [A_159] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_159,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_159)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_693])).

tff(c_723,plain,(
    ! [A_161] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_161,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_706])).

tff(c_740,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_723])).

tff(c_1041,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | k1_xboole_0 != '#skF_1'
    | k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_740])).

tff(c_1211,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1041])).

tff(c_1264,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1211])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_270,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_279,plain,(
    ! [A_93,B_94,A_6] :
      ( k1_relset_1(A_93,B_94,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_93,B_94)) ) ),
    inference(resolution,[status(thm)],[c_16,c_270])).

tff(c_756,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_740,c_279])).

tff(c_676,plain,(
    ! [B_151,C_152,A_153] :
      ( k1_xboole_0 = B_151
      | v1_funct_2(C_152,A_153,B_151)
      | k1_relset_1(A_153,B_151,C_152) != A_153
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1774,plain,(
    ! [B_750,A_751,A_752] :
      ( k1_xboole_0 = B_750
      | v1_funct_2(A_751,A_752,B_750)
      | k1_relset_1(A_752,B_750,A_751) != A_752
      | ~ r1_tarski(A_751,k2_zfmisc_1(A_752,B_750)) ) ),
    inference(resolution,[status(thm)],[c_16,c_676])).

tff(c_1793,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_740,c_1774])).

tff(c_1819,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_1793])).

tff(c_1821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1264,c_1819])).

tff(c_1823,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1211])).

tff(c_134,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) = k1_xboole_0
      | k2_relat_1(A_53) != k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_141,plain,(
    ! [A_8,B_9] :
      ( k1_relat_1(k2_zfmisc_1(A_8,B_9)) = k1_xboole_0
      | k2_relat_1(k2_zfmisc_1(A_8,B_9)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_963,plain,(
    ! [A_170,B_171] :
      ( k1_relat_1(k2_zfmisc_1(A_170,B_171)) = k1_xboole_0
      | k1_xboole_0 != B_171
      | k1_xboole_0 = A_170 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_141])).

tff(c_2667,plain,(
    ! [A_1255,B_1256] :
      ( k1_relat_1(k2_zfmisc_1(A_1255,B_1256)) = '#skF_1'
      | B_1256 != '#skF_1'
      | A_1255 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_1823,c_963])).

tff(c_124,plain,(
    ! [A_52] :
      ( k2_relat_1(A_52) = k1_xboole_0
      | k1_relat_1(A_52) != k1_xboole_0
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_151,plain,(
    ! [A_60,B_61] :
      ( k2_relat_1(k2_zfmisc_1(A_60,B_61)) = k1_xboole_0
      | k1_relat_1(k2_zfmisc_1(A_60,B_61)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_124])).

tff(c_166,plain,(
    ! [B_61,A_60] :
      ( r1_tarski(k1_xboole_0,B_61)
      | k1_relat_1(k2_zfmisc_1(A_60,B_61)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_22])).

tff(c_1847,plain,(
    ! [B_61,A_60] :
      ( r1_tarski('#skF_1',B_61)
      | k1_relat_1(k2_zfmisc_1(A_60,B_61)) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_166])).

tff(c_2737,plain,(
    ! [B_1256,A_1255] :
      ( r1_tarski('#skF_1',B_1256)
      | B_1256 != '#skF_1'
      | A_1255 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2667,c_1847])).

tff(c_2802,plain,(
    ! [A_1259] : A_1259 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2737])).

tff(c_1205,plain,(
    ! [B_172,A_173] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != B_172
      | k1_xboole_0 = A_173 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_18])).

tff(c_1870,plain,(
    ! [B_172,A_173] :
      ( v1_relat_1('#skF_1')
      | B_172 != '#skF_1'
      | A_173 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_1823,c_1205])).

tff(c_1871,plain,(
    ! [B_172] : B_172 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1870])).

tff(c_1914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1871,c_1823])).

tff(c_1915,plain,(
    ! [A_173] :
      ( v1_relat_1('#skF_1')
      | A_173 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_1870])).

tff(c_1916,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1915])).

tff(c_36,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) = k1_xboole_0
      | k1_relat_1(A_19) != k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2511,plain,(
    ! [A_1245] :
      ( k2_relat_1(A_1245) = '#skF_1'
      | k1_relat_1(A_1245) != '#skF_1'
      | ~ v1_relat_1(A_1245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_36])).

tff(c_2521,plain,
    ( k2_relat_1('#skF_1') = '#skF_1'
    | k1_relat_1('#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1916,c_2511])).

tff(c_2560,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2521])).

tff(c_34,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) = k1_xboole_0
      | k2_relat_1(A_19) != k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2642,plain,(
    ! [A_1252] :
      ( k1_relat_1(A_1252) = '#skF_1'
      | k2_relat_1(A_1252) != '#skF_1'
      | ~ v1_relat_1(A_1252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_34])).

tff(c_2645,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | k2_relat_1('#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1916,c_2642])).

tff(c_2654,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2560,c_2645])).

tff(c_3044,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2802,c_2654])).

tff(c_3047,plain,(
    ! [B_1788] :
      ( r1_tarski('#skF_1',B_1788)
      | B_1788 != '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_2737])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_758,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_740,c_4])).

tff(c_813,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_758])).

tff(c_1032,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_2')
    | k1_xboole_0 != '#skF_1'
    | k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_813])).

tff(c_1210,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_2')
    | k1_xboole_0 != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1032])).

tff(c_1867,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_1210])).

tff(c_3076,plain,(
    '#skF_2' != '#skF_1' ),
    inference(resolution,[status(thm)],[c_3047,c_1867])).

tff(c_2728,plain,(
    ! [A_1255,B_1256] :
      ( r1_tarski('#skF_1',A_1255)
      | B_1256 != '#skF_1'
      | A_1255 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2667,c_20])).

tff(c_3103,plain,(
    ! [B_1256] : B_1256 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2728])).

tff(c_3119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3103,c_1823])).

tff(c_3121,plain,(
    ! [A_1790] :
      ( r1_tarski('#skF_1',A_1790)
      | A_1790 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_2728])).

tff(c_3124,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3121,c_1867])).

tff(c_3153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3076,c_3124])).

tff(c_3154,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2521])).

tff(c_1203,plain,(
    ! [B_172,A_173] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),B_172)
      | k1_xboole_0 != B_172
      | k1_xboole_0 = A_173 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_22])).

tff(c_2113,plain,(
    ! [B_172,A_173] :
      ( r1_tarski(k2_relat_1('#skF_1'),B_172)
      | B_172 != '#skF_1'
      | A_173 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_1823,c_1203])).

tff(c_2122,plain,(
    ! [A_767] : A_767 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2113])).

tff(c_2129,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2122,c_1867])).

tff(c_2343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2129])).

tff(c_2344,plain,(
    ! [B_172] :
      ( r1_tarski(k2_relat_1('#skF_1'),B_172)
      | B_172 != '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_2113])).

tff(c_3361,plain,(
    ! [B_1795] :
      ( r1_tarski('#skF_1',B_1795)
      | B_1795 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3154,c_2344])).

tff(c_3395,plain,(
    '#skF_2' != '#skF_1' ),
    inference(resolution,[status(thm)],[c_3361,c_1867])).

tff(c_3155,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2521])).

tff(c_1200,plain,(
    ! [A_173,B_172] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_173)
      | k1_xboole_0 != B_172
      | k1_xboole_0 = A_173 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_20])).

tff(c_2037,plain,(
    ! [A_173,B_172] :
      ( r1_tarski(k1_relat_1('#skF_1'),A_173)
      | B_172 != '#skF_1'
      | A_173 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1823,c_1823,c_1200])).

tff(c_2038,plain,(
    ! [B_172] : B_172 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2037])).

tff(c_2045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2038,c_1823])).

tff(c_2046,plain,(
    ! [A_173] :
      ( r1_tarski(k1_relat_1('#skF_1'),A_173)
      | A_173 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_2037])).

tff(c_3404,plain,(
    ! [A_1796] :
      ( r1_tarski('#skF_1',A_1796)
      | A_1796 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3155,c_2046])).

tff(c_3411,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3404,c_1867])).

tff(c_3441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3395,c_3411])).

tff(c_3444,plain,(
    ! [A_1797] : A_1797 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1915])).

tff(c_3447,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3444,c_1867])).

tff(c_3661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3447])).

tff(c_3662,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_758])).

tff(c_3708,plain,(
    ! [C_5] :
      ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),C_5))
      | r1_tarski('#skF_1',C_5)
      | k1_relat_1('#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3662,c_10])).

tff(c_3827,plain,(
    ! [C_2257] :
      ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),C_2257))
      | r1_tarski('#skF_1',C_2257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3708])).

tff(c_3838,plain,
    ( r1_tarski('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3827])).

tff(c_3846,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3838])).

tff(c_3848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_3846])).

tff(c_3849,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_3893,plain,(
    ! [A_2261] :
      ( v1_funct_2(A_2261,k1_relat_1(A_2261),k2_relat_1(A_2261))
      | ~ v1_funct_1(A_2261)
      | ~ v1_relat_1(A_2261) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3896,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3849,c_3893])).

tff(c_3898,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3896])).

tff(c_3900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_3898])).

tff(c_3901,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_90,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_82])).

tff(c_91,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_3904,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3901,c_91])).

tff(c_3902,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_3911,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3901,c_3902])).

tff(c_3939,plain,(
    ! [A_2264] :
      ( k2_relat_1(A_2264) = '#skF_2'
      | k1_relat_1(A_2264) != '#skF_2'
      | ~ v1_relat_1(A_2264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3901,c_3901,c_36])).

tff(c_3945,plain,
    ( k2_relat_1('#skF_2') = '#skF_2'
    | k1_relat_1('#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_3939])).

tff(c_3949,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3911,c_3945])).

tff(c_3951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3904,c_3949])).

tff(c_3952,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_3953,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_3965,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3952,c_3953])).

tff(c_3995,plain,(
    ! [A_2269] :
      ( k1_relat_1(A_2269) = '#skF_2'
      | k2_relat_1(A_2269) != '#skF_2'
      | ~ v1_relat_1(A_2269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3952,c_3952,c_34])).

tff(c_4001,plain,
    ( k1_relat_1('#skF_2') = '#skF_2'
    | k2_relat_1('#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_3995])).

tff(c_4005,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_4001])).

tff(c_4006,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4005,c_81])).

tff(c_3966,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_68])).

tff(c_5664,plain,(
    ! [C_2424,A_2425,B_2426] :
      ( m1_subset_1(C_2424,k1_zfmisc_1(k2_zfmisc_1(A_2425,B_2426)))
      | ~ r1_tarski(k2_relat_1(C_2424),B_2426)
      | ~ r1_tarski(k1_relat_1(C_2424),A_2425)
      | ~ v1_relat_1(C_2424) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6005,plain,(
    ! [C_2456,A_2457,B_2458] :
      ( r1_tarski(C_2456,k2_zfmisc_1(A_2457,B_2458))
      | ~ r1_tarski(k2_relat_1(C_2456),B_2458)
      | ~ r1_tarski(k1_relat_1(C_2456),A_2457)
      | ~ v1_relat_1(C_2456) ) ),
    inference(resolution,[status(thm)],[c_5664,c_14])).

tff(c_6018,plain,(
    ! [A_2457,B_2458] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_2457,B_2458))
      | ~ r1_tarski('#skF_2',B_2458)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_2457)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3965,c_6005])).

tff(c_6037,plain,(
    ! [A_2459,B_2460] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_2459,B_2460))
      | ~ r1_tarski('#skF_2',B_2460)
      | ~ r1_tarski('#skF_2',A_2459) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4005,c_6018])).

tff(c_4867,plain,(
    ! [A_2373,B_2374] :
      ( r1_tarski(k1_relat_1(A_2373),k1_relat_1(B_2374))
      | ~ r1_tarski(A_2373,B_2374)
      | ~ v1_relat_1(B_2374)
      | ~ v1_relat_1(A_2373) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4876,plain,(
    ! [B_2374] :
      ( r1_tarski('#skF_2',k1_relat_1(B_2374))
      | ~ r1_tarski('#skF_2',B_2374)
      | ~ v1_relat_1(B_2374)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4005,c_4867])).

tff(c_4888,plain,(
    ! [B_2375] :
      ( r1_tarski('#skF_2',k1_relat_1(B_2375))
      | ~ r1_tarski('#skF_2',B_2375)
      | ~ v1_relat_1(B_2375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4876])).

tff(c_4023,plain,(
    ! [B_2271,A_2272] :
      ( B_2271 = A_2272
      | ~ r1_tarski(B_2271,A_2272)
      | ~ r1_tarski(A_2272,B_2271) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4033,plain,(
    ! [A_10,B_11] :
      ( k1_relat_1(k2_zfmisc_1(A_10,B_11)) = A_10
      | ~ r1_tarski(A_10,k1_relat_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(resolution,[status(thm)],[c_20,c_4023])).

tff(c_4894,plain,(
    ! [B_11] :
      ( k1_relat_1(k2_zfmisc_1('#skF_2',B_11)) = '#skF_2'
      | ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_2',B_11))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_2',B_11)) ) ),
    inference(resolution,[status(thm)],[c_4888,c_4033])).

tff(c_4903,plain,(
    ! [B_11] :
      ( k1_relat_1(k2_zfmisc_1('#skF_2',B_11)) = '#skF_2'
      | ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_2',B_11)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4894])).

tff(c_6060,plain,(
    ! [B_2460] :
      ( k1_relat_1(k2_zfmisc_1('#skF_2',B_2460)) = '#skF_2'
      | ~ r1_tarski('#skF_2',B_2460)
      | ~ r1_tarski('#skF_2','#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6037,c_4903])).

tff(c_6637,plain,(
    ! [B_2466] :
      ( k1_relat_1(k2_zfmisc_1('#skF_2',B_2466)) = '#skF_2'
      | ~ r1_tarski('#skF_2',B_2466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6060])).

tff(c_32,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3972,plain,(
    ! [A_2267] :
      ( k1_relat_1(A_2267) != '#skF_2'
      | A_2267 = '#skF_2'
      | ~ v1_relat_1(A_2267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3952,c_3952,c_32])).

tff(c_3979,plain,(
    ! [A_8,B_9] :
      ( k1_relat_1(k2_zfmisc_1(A_8,B_9)) != '#skF_2'
      | k2_zfmisc_1(A_8,B_9) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_18,c_3972])).

tff(c_6797,plain,(
    ! [B_2467] :
      ( k2_zfmisc_1('#skF_2',B_2467) = '#skF_2'
      | ~ r1_tarski('#skF_2',B_2467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6637,c_3979])).

tff(c_6824,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3966,c_6797])).

tff(c_4527,plain,(
    ! [A_2329,B_2330,C_2331] :
      ( k1_relset_1(A_2329,B_2330,C_2331) = k1_relat_1(C_2331)
      | ~ m1_subset_1(C_2331,k1_zfmisc_1(k2_zfmisc_1(A_2329,B_2330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4674,plain,(
    ! [A_2357,B_2358,A_2359] :
      ( k1_relset_1(A_2357,B_2358,A_2359) = k1_relat_1(A_2359)
      | ~ r1_tarski(A_2359,k2_zfmisc_1(A_2357,B_2358)) ) ),
    inference(resolution,[status(thm)],[c_16,c_4527])).

tff(c_4696,plain,(
    ! [A_2357,B_2358] : k1_relset_1(A_2357,B_2358,k2_zfmisc_1(A_2357,B_2358)) = k1_relat_1(k2_zfmisc_1(A_2357,B_2358)) ),
    inference(resolution,[status(thm)],[c_8,c_4674])).

tff(c_52,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5349,plain,(
    ! [C_2399,B_2400] :
      ( v1_funct_2(C_2399,'#skF_2',B_2400)
      | k1_relset_1('#skF_2',B_2400,C_2399) != '#skF_2'
      | ~ m1_subset_1(C_2399,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_2400))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3952,c_3952,c_3952,c_3952,c_52])).

tff(c_5379,plain,(
    ! [A_2403,B_2404] :
      ( v1_funct_2(A_2403,'#skF_2',B_2404)
      | k1_relset_1('#skF_2',B_2404,A_2403) != '#skF_2'
      | ~ r1_tarski(A_2403,k2_zfmisc_1('#skF_2',B_2404)) ) ),
    inference(resolution,[status(thm)],[c_16,c_5349])).

tff(c_5394,plain,(
    ! [B_2404] :
      ( v1_funct_2(k2_zfmisc_1('#skF_2',B_2404),'#skF_2',B_2404)
      | k1_relset_1('#skF_2',B_2404,k2_zfmisc_1('#skF_2',B_2404)) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_8,c_5379])).

tff(c_5398,plain,(
    ! [B_2404] :
      ( v1_funct_2(k2_zfmisc_1('#skF_2',B_2404),'#skF_2',B_2404)
      | k1_relat_1(k2_zfmisc_1('#skF_2',B_2404)) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4696,c_5394])).

tff(c_6872,plain,
    ( v1_funct_2('#skF_2','#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6824,c_5398])).

tff(c_6975,plain,(
    v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4005,c_6824,c_6872])).

tff(c_6977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4006,c_6975])).

tff(c_6978,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_7439,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7408,c_6978])).

tff(c_7451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8,c_68,c_7439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.30  
% 6.64/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.30  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.64/2.30  
% 6.64/2.30  %Foreground sorts:
% 6.64/2.30  
% 6.64/2.30  
% 6.64/2.30  %Background operators:
% 6.64/2.30  
% 6.64/2.30  
% 6.64/2.30  %Foreground operators:
% 6.64/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.64/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.64/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.64/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.64/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.64/2.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.64/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.64/2.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.64/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.64/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.64/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.64/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.64/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.64/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.64/2.30  
% 6.64/2.33  tff(f_152, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.64/2.33  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.64/2.33  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.64/2.33  tff(f_57, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 6.64/2.33  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.64/2.33  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.64/2.33  tff(f_51, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 6.64/2.33  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.64/2.33  tff(f_43, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 6.64/2.33  tff(f_53, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 6.64/2.33  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.64/2.33  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.64/2.33  tff(f_82, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 6.64/2.33  tff(f_139, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.64/2.33  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 6.64/2.33  tff(c_72, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.64/2.33  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.33  tff(c_68, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.64/2.33  tff(c_7408, plain, (![C_2554, A_2555, B_2556]: (m1_subset_1(C_2554, k1_zfmisc_1(k2_zfmisc_1(A_2555, B_2556))) | ~r1_tarski(k2_relat_1(C_2554), B_2556) | ~r1_tarski(k1_relat_1(C_2554), A_2555) | ~v1_relat_1(C_2554))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.64/2.33  tff(c_70, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.64/2.33  tff(c_66, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.64/2.33  tff(c_74, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66])).
% 6.64/2.33  tff(c_81, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_74])).
% 6.64/2.33  tff(c_107, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.33  tff(c_118, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_107])).
% 6.64/2.33  tff(c_123, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 6.64/2.33  tff(c_24, plain, (![A_14]: (r1_tarski(A_14, k2_zfmisc_1(k1_relat_1(A_14), k2_relat_1(A_14))) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.33  tff(c_97, plain, (![A_49]: (k1_relat_1(A_49)!=k1_xboole_0 | k1_xboole_0=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.64/2.33  tff(c_105, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_72, c_97])).
% 6.64/2.33  tff(c_106, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_105])).
% 6.64/2.33  tff(c_18, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.64/2.33  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_10, B_11)), A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.64/2.33  tff(c_538, plain, (![C_136, A_137, B_138]: (m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~r1_tarski(k2_relat_1(C_136), B_138) | ~r1_tarski(k1_relat_1(C_136), A_137) | ~v1_relat_1(C_136))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.64/2.33  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.64/2.33  tff(c_693, plain, (![C_158, A_159, B_160]: (r1_tarski(C_158, k2_zfmisc_1(A_159, B_160)) | ~r1_tarski(k2_relat_1(C_158), B_160) | ~r1_tarski(k1_relat_1(C_158), A_159) | ~v1_relat_1(C_158))), inference(resolution, [status(thm)], [c_538, c_14])).
% 6.64/2.33  tff(c_814, plain, (![C_166, A_167]: (r1_tarski(C_166, k2_zfmisc_1(A_167, k2_relat_1(C_166))) | ~r1_tarski(k1_relat_1(C_166), A_167) | ~v1_relat_1(C_166))), inference(resolution, [status(thm)], [c_8, c_693])).
% 6.64/2.33  tff(c_10, plain, (![A_3, B_4, C_5]: (~r1_tarski(k2_zfmisc_1(A_3, B_4), k2_zfmisc_1(A_3, C_5)) | r1_tarski(B_4, C_5) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.64/2.33  tff(c_848, plain, (![B_4, A_167]: (r1_tarski(B_4, k2_relat_1(k2_zfmisc_1(A_167, B_4))) | k1_xboole_0=A_167 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(A_167, B_4)), A_167) | ~v1_relat_1(k2_zfmisc_1(A_167, B_4)))), inference(resolution, [status(thm)], [c_814, c_10])).
% 6.64/2.33  tff(c_881, plain, (![B_168, A_169]: (r1_tarski(B_168, k2_relat_1(k2_zfmisc_1(A_169, B_168))) | k1_xboole_0=A_169)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_848])).
% 6.64/2.33  tff(c_22, plain, (![A_12, B_13]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_12, B_13)), B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.64/2.33  tff(c_117, plain, (![A_12, B_13]: (k2_relat_1(k2_zfmisc_1(A_12, B_13))=B_13 | ~r1_tarski(B_13, k2_relat_1(k2_zfmisc_1(A_12, B_13))))), inference(resolution, [status(thm)], [c_22, c_107])).
% 6.64/2.33  tff(c_924, plain, (![A_170, B_171]: (k2_relat_1(k2_zfmisc_1(A_170, B_171))=B_171 | k1_xboole_0=A_170)), inference(resolution, [status(thm)], [c_881, c_117])).
% 6.64/2.33  tff(c_82, plain, (![A_46]: (k2_relat_1(A_46)!=k1_xboole_0 | k1_xboole_0=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.64/2.33  tff(c_89, plain, (![A_8, B_9]: (k2_relat_1(k2_zfmisc_1(A_8, B_9))!=k1_xboole_0 | k2_zfmisc_1(A_8, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_82])).
% 6.64/2.33  tff(c_1016, plain, (![B_172, A_173]: (k1_xboole_0!=B_172 | k2_zfmisc_1(A_173, B_172)=k1_xboole_0 | k1_xboole_0=A_173)), inference(superposition, [status(thm), theory('equality')], [c_924, c_89])).
% 6.64/2.33  tff(c_706, plain, (![A_159]: (r1_tarski('#skF_2', k2_zfmisc_1(A_159, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_159) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_693])).
% 6.64/2.33  tff(c_723, plain, (![A_161]: (r1_tarski('#skF_2', k2_zfmisc_1(A_161, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_161))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_706])).
% 6.64/2.33  tff(c_740, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_723])).
% 6.64/2.33  tff(c_1041, plain, (r1_tarski('#skF_2', k1_xboole_0) | k1_xboole_0!='#skF_1' | k1_relat_1('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1016, c_740])).
% 6.64/2.33  tff(c_1211, plain, (r1_tarski('#skF_2', k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_106, c_1041])).
% 6.64/2.33  tff(c_1264, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_1211])).
% 6.64/2.33  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.64/2.33  tff(c_270, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.64/2.33  tff(c_279, plain, (![A_93, B_94, A_6]: (k1_relset_1(A_93, B_94, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_93, B_94)))), inference(resolution, [status(thm)], [c_16, c_270])).
% 6.64/2.33  tff(c_756, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_740, c_279])).
% 6.64/2.33  tff(c_676, plain, (![B_151, C_152, A_153]: (k1_xboole_0=B_151 | v1_funct_2(C_152, A_153, B_151) | k1_relset_1(A_153, B_151, C_152)!=A_153 | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_151))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.64/2.33  tff(c_1774, plain, (![B_750, A_751, A_752]: (k1_xboole_0=B_750 | v1_funct_2(A_751, A_752, B_750) | k1_relset_1(A_752, B_750, A_751)!=A_752 | ~r1_tarski(A_751, k2_zfmisc_1(A_752, B_750)))), inference(resolution, [status(thm)], [c_16, c_676])).
% 6.64/2.33  tff(c_1793, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_740, c_1774])).
% 6.64/2.33  tff(c_1819, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_756, c_1793])).
% 6.64/2.33  tff(c_1821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_1264, c_1819])).
% 6.64/2.33  tff(c_1823, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1211])).
% 6.64/2.33  tff(c_134, plain, (![A_53]: (k1_relat_1(A_53)=k1_xboole_0 | k2_relat_1(A_53)!=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.64/2.33  tff(c_141, plain, (![A_8, B_9]: (k1_relat_1(k2_zfmisc_1(A_8, B_9))=k1_xboole_0 | k2_relat_1(k2_zfmisc_1(A_8, B_9))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_134])).
% 6.64/2.33  tff(c_963, plain, (![A_170, B_171]: (k1_relat_1(k2_zfmisc_1(A_170, B_171))=k1_xboole_0 | k1_xboole_0!=B_171 | k1_xboole_0=A_170)), inference(superposition, [status(thm), theory('equality')], [c_924, c_141])).
% 6.64/2.33  tff(c_2667, plain, (![A_1255, B_1256]: (k1_relat_1(k2_zfmisc_1(A_1255, B_1256))='#skF_1' | B_1256!='#skF_1' | A_1255='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_1823, c_963])).
% 6.64/2.33  tff(c_124, plain, (![A_52]: (k2_relat_1(A_52)=k1_xboole_0 | k1_relat_1(A_52)!=k1_xboole_0 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.64/2.33  tff(c_151, plain, (![A_60, B_61]: (k2_relat_1(k2_zfmisc_1(A_60, B_61))=k1_xboole_0 | k1_relat_1(k2_zfmisc_1(A_60, B_61))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_124])).
% 6.64/2.33  tff(c_166, plain, (![B_61, A_60]: (r1_tarski(k1_xboole_0, B_61) | k1_relat_1(k2_zfmisc_1(A_60, B_61))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_151, c_22])).
% 6.64/2.33  tff(c_1847, plain, (![B_61, A_60]: (r1_tarski('#skF_1', B_61) | k1_relat_1(k2_zfmisc_1(A_60, B_61))!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_166])).
% 6.64/2.33  tff(c_2737, plain, (![B_1256, A_1255]: (r1_tarski('#skF_1', B_1256) | B_1256!='#skF_1' | A_1255='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2667, c_1847])).
% 6.64/2.33  tff(c_2802, plain, (![A_1259]: (A_1259='#skF_1')), inference(splitLeft, [status(thm)], [c_2737])).
% 6.64/2.33  tff(c_1205, plain, (![B_172, A_173]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=B_172 | k1_xboole_0=A_173)), inference(superposition, [status(thm), theory('equality')], [c_1016, c_18])).
% 6.64/2.33  tff(c_1870, plain, (![B_172, A_173]: (v1_relat_1('#skF_1') | B_172!='#skF_1' | A_173='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_1823, c_1205])).
% 6.64/2.33  tff(c_1871, plain, (![B_172]: (B_172!='#skF_1')), inference(splitLeft, [status(thm)], [c_1870])).
% 6.64/2.33  tff(c_1914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1871, c_1823])).
% 6.64/2.33  tff(c_1915, plain, (![A_173]: (v1_relat_1('#skF_1') | A_173='#skF_1')), inference(splitRight, [status(thm)], [c_1870])).
% 6.64/2.33  tff(c_1916, plain, (v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1915])).
% 6.64/2.33  tff(c_36, plain, (![A_19]: (k2_relat_1(A_19)=k1_xboole_0 | k1_relat_1(A_19)!=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.64/2.33  tff(c_2511, plain, (![A_1245]: (k2_relat_1(A_1245)='#skF_1' | k1_relat_1(A_1245)!='#skF_1' | ~v1_relat_1(A_1245))), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_36])).
% 6.64/2.33  tff(c_2521, plain, (k2_relat_1('#skF_1')='#skF_1' | k1_relat_1('#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_1916, c_2511])).
% 6.64/2.33  tff(c_2560, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2521])).
% 6.64/2.33  tff(c_34, plain, (![A_19]: (k1_relat_1(A_19)=k1_xboole_0 | k2_relat_1(A_19)!=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.64/2.33  tff(c_2642, plain, (![A_1252]: (k1_relat_1(A_1252)='#skF_1' | k2_relat_1(A_1252)!='#skF_1' | ~v1_relat_1(A_1252))), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_34])).
% 6.64/2.33  tff(c_2645, plain, (k1_relat_1('#skF_1')='#skF_1' | k2_relat_1('#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_1916, c_2642])).
% 6.64/2.33  tff(c_2654, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2560, c_2645])).
% 6.64/2.33  tff(c_3044, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2802, c_2654])).
% 6.64/2.33  tff(c_3047, plain, (![B_1788]: (r1_tarski('#skF_1', B_1788) | B_1788!='#skF_1')), inference(splitRight, [status(thm)], [c_2737])).
% 6.64/2.33  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.33  tff(c_758, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_740, c_4])).
% 6.64/2.33  tff(c_813, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_758])).
% 6.64/2.33  tff(c_1032, plain, (~r1_tarski(k1_xboole_0, '#skF_2') | k1_xboole_0!='#skF_1' | k1_relat_1('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1016, c_813])).
% 6.64/2.33  tff(c_1210, plain, (~r1_tarski(k1_xboole_0, '#skF_2') | k1_xboole_0!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_106, c_1032])).
% 6.64/2.33  tff(c_1867, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_1210])).
% 6.64/2.33  tff(c_3076, plain, ('#skF_2'!='#skF_1'), inference(resolution, [status(thm)], [c_3047, c_1867])).
% 6.64/2.33  tff(c_2728, plain, (![A_1255, B_1256]: (r1_tarski('#skF_1', A_1255) | B_1256!='#skF_1' | A_1255='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2667, c_20])).
% 6.64/2.33  tff(c_3103, plain, (![B_1256]: (B_1256!='#skF_1')), inference(splitLeft, [status(thm)], [c_2728])).
% 6.64/2.33  tff(c_3119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3103, c_1823])).
% 6.64/2.33  tff(c_3121, plain, (![A_1790]: (r1_tarski('#skF_1', A_1790) | A_1790='#skF_1')), inference(splitRight, [status(thm)], [c_2728])).
% 6.64/2.33  tff(c_3124, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_3121, c_1867])).
% 6.64/2.33  tff(c_3153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3076, c_3124])).
% 6.64/2.33  tff(c_3154, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2521])).
% 6.64/2.33  tff(c_1203, plain, (![B_172, A_173]: (r1_tarski(k2_relat_1(k1_xboole_0), B_172) | k1_xboole_0!=B_172 | k1_xboole_0=A_173)), inference(superposition, [status(thm), theory('equality')], [c_1016, c_22])).
% 6.64/2.33  tff(c_2113, plain, (![B_172, A_173]: (r1_tarski(k2_relat_1('#skF_1'), B_172) | B_172!='#skF_1' | A_173='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_1823, c_1203])).
% 6.64/2.33  tff(c_2122, plain, (![A_767]: (A_767='#skF_1')), inference(splitLeft, [status(thm)], [c_2113])).
% 6.64/2.33  tff(c_2129, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2122, c_1867])).
% 6.64/2.33  tff(c_2343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2129])).
% 6.64/2.33  tff(c_2344, plain, (![B_172]: (r1_tarski(k2_relat_1('#skF_1'), B_172) | B_172!='#skF_1')), inference(splitRight, [status(thm)], [c_2113])).
% 6.64/2.33  tff(c_3361, plain, (![B_1795]: (r1_tarski('#skF_1', B_1795) | B_1795!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3154, c_2344])).
% 6.64/2.33  tff(c_3395, plain, ('#skF_2'!='#skF_1'), inference(resolution, [status(thm)], [c_3361, c_1867])).
% 6.64/2.33  tff(c_3155, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2521])).
% 6.64/2.33  tff(c_1200, plain, (![A_173, B_172]: (r1_tarski(k1_relat_1(k1_xboole_0), A_173) | k1_xboole_0!=B_172 | k1_xboole_0=A_173)), inference(superposition, [status(thm), theory('equality')], [c_1016, c_20])).
% 6.64/2.33  tff(c_2037, plain, (![A_173, B_172]: (r1_tarski(k1_relat_1('#skF_1'), A_173) | B_172!='#skF_1' | A_173='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1823, c_1823, c_1200])).
% 6.64/2.33  tff(c_2038, plain, (![B_172]: (B_172!='#skF_1')), inference(splitLeft, [status(thm)], [c_2037])).
% 6.64/2.33  tff(c_2045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2038, c_1823])).
% 6.64/2.33  tff(c_2046, plain, (![A_173]: (r1_tarski(k1_relat_1('#skF_1'), A_173) | A_173='#skF_1')), inference(splitRight, [status(thm)], [c_2037])).
% 6.64/2.33  tff(c_3404, plain, (![A_1796]: (r1_tarski('#skF_1', A_1796) | A_1796='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3155, c_2046])).
% 6.64/2.33  tff(c_3411, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_3404, c_1867])).
% 6.64/2.33  tff(c_3441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3395, c_3411])).
% 6.64/2.33  tff(c_3444, plain, (![A_1797]: (A_1797='#skF_1')), inference(splitRight, [status(thm)], [c_1915])).
% 6.64/2.33  tff(c_3447, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3444, c_1867])).
% 6.64/2.33  tff(c_3661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_3447])).
% 6.64/2.33  tff(c_3662, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_758])).
% 6.64/2.33  tff(c_3708, plain, (![C_5]: (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), C_5)) | r1_tarski('#skF_1', C_5) | k1_relat_1('#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3662, c_10])).
% 6.64/2.33  tff(c_3827, plain, (![C_2257]: (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), C_2257)) | r1_tarski('#skF_1', C_2257))), inference(negUnitSimplification, [status(thm)], [c_106, c_3708])).
% 6.64/2.33  tff(c_3838, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3827])).
% 6.64/2.33  tff(c_3846, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3838])).
% 6.64/2.33  tff(c_3848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_3846])).
% 6.64/2.33  tff(c_3849, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_118])).
% 6.64/2.33  tff(c_3893, plain, (![A_2261]: (v1_funct_2(A_2261, k1_relat_1(A_2261), k2_relat_1(A_2261)) | ~v1_funct_1(A_2261) | ~v1_relat_1(A_2261))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.64/2.33  tff(c_3896, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3849, c_3893])).
% 6.64/2.33  tff(c_3898, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3896])).
% 6.64/2.33  tff(c_3900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_3898])).
% 6.64/2.33  tff(c_3901, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_105])).
% 6.64/2.33  tff(c_90, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_72, c_82])).
% 6.64/2.33  tff(c_91, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 6.64/2.33  tff(c_3904, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3901, c_91])).
% 6.64/2.33  tff(c_3902, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_105])).
% 6.64/2.33  tff(c_3911, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3901, c_3902])).
% 6.64/2.33  tff(c_3939, plain, (![A_2264]: (k2_relat_1(A_2264)='#skF_2' | k1_relat_1(A_2264)!='#skF_2' | ~v1_relat_1(A_2264))), inference(demodulation, [status(thm), theory('equality')], [c_3901, c_3901, c_36])).
% 6.64/2.33  tff(c_3945, plain, (k2_relat_1('#skF_2')='#skF_2' | k1_relat_1('#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_72, c_3939])).
% 6.64/2.33  tff(c_3949, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3911, c_3945])).
% 6.64/2.33  tff(c_3951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3904, c_3949])).
% 6.64/2.33  tff(c_3952, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_90])).
% 6.64/2.33  tff(c_3953, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_90])).
% 6.64/2.33  tff(c_3965, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3952, c_3953])).
% 6.64/2.33  tff(c_3995, plain, (![A_2269]: (k1_relat_1(A_2269)='#skF_2' | k2_relat_1(A_2269)!='#skF_2' | ~v1_relat_1(A_2269))), inference(demodulation, [status(thm), theory('equality')], [c_3952, c_3952, c_34])).
% 6.64/2.33  tff(c_4001, plain, (k1_relat_1('#skF_2')='#skF_2' | k2_relat_1('#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_72, c_3995])).
% 6.64/2.33  tff(c_4005, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_4001])).
% 6.64/2.33  tff(c_4006, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4005, c_81])).
% 6.64/2.33  tff(c_3966, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_68])).
% 6.64/2.33  tff(c_5664, plain, (![C_2424, A_2425, B_2426]: (m1_subset_1(C_2424, k1_zfmisc_1(k2_zfmisc_1(A_2425, B_2426))) | ~r1_tarski(k2_relat_1(C_2424), B_2426) | ~r1_tarski(k1_relat_1(C_2424), A_2425) | ~v1_relat_1(C_2424))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.64/2.33  tff(c_6005, plain, (![C_2456, A_2457, B_2458]: (r1_tarski(C_2456, k2_zfmisc_1(A_2457, B_2458)) | ~r1_tarski(k2_relat_1(C_2456), B_2458) | ~r1_tarski(k1_relat_1(C_2456), A_2457) | ~v1_relat_1(C_2456))), inference(resolution, [status(thm)], [c_5664, c_14])).
% 6.64/2.33  tff(c_6018, plain, (![A_2457, B_2458]: (r1_tarski('#skF_2', k2_zfmisc_1(A_2457, B_2458)) | ~r1_tarski('#skF_2', B_2458) | ~r1_tarski(k1_relat_1('#skF_2'), A_2457) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3965, c_6005])).
% 6.64/2.33  tff(c_6037, plain, (![A_2459, B_2460]: (r1_tarski('#skF_2', k2_zfmisc_1(A_2459, B_2460)) | ~r1_tarski('#skF_2', B_2460) | ~r1_tarski('#skF_2', A_2459))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4005, c_6018])).
% 6.64/2.33  tff(c_4867, plain, (![A_2373, B_2374]: (r1_tarski(k1_relat_1(A_2373), k1_relat_1(B_2374)) | ~r1_tarski(A_2373, B_2374) | ~v1_relat_1(B_2374) | ~v1_relat_1(A_2373))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.64/2.33  tff(c_4876, plain, (![B_2374]: (r1_tarski('#skF_2', k1_relat_1(B_2374)) | ~r1_tarski('#skF_2', B_2374) | ~v1_relat_1(B_2374) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4005, c_4867])).
% 6.64/2.33  tff(c_4888, plain, (![B_2375]: (r1_tarski('#skF_2', k1_relat_1(B_2375)) | ~r1_tarski('#skF_2', B_2375) | ~v1_relat_1(B_2375))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4876])).
% 6.64/2.33  tff(c_4023, plain, (![B_2271, A_2272]: (B_2271=A_2272 | ~r1_tarski(B_2271, A_2272) | ~r1_tarski(A_2272, B_2271))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.33  tff(c_4033, plain, (![A_10, B_11]: (k1_relat_1(k2_zfmisc_1(A_10, B_11))=A_10 | ~r1_tarski(A_10, k1_relat_1(k2_zfmisc_1(A_10, B_11))))), inference(resolution, [status(thm)], [c_20, c_4023])).
% 6.64/2.33  tff(c_4894, plain, (![B_11]: (k1_relat_1(k2_zfmisc_1('#skF_2', B_11))='#skF_2' | ~r1_tarski('#skF_2', k2_zfmisc_1('#skF_2', B_11)) | ~v1_relat_1(k2_zfmisc_1('#skF_2', B_11)))), inference(resolution, [status(thm)], [c_4888, c_4033])).
% 6.64/2.33  tff(c_4903, plain, (![B_11]: (k1_relat_1(k2_zfmisc_1('#skF_2', B_11))='#skF_2' | ~r1_tarski('#skF_2', k2_zfmisc_1('#skF_2', B_11)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4894])).
% 6.64/2.33  tff(c_6060, plain, (![B_2460]: (k1_relat_1(k2_zfmisc_1('#skF_2', B_2460))='#skF_2' | ~r1_tarski('#skF_2', B_2460) | ~r1_tarski('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_6037, c_4903])).
% 6.64/2.33  tff(c_6637, plain, (![B_2466]: (k1_relat_1(k2_zfmisc_1('#skF_2', B_2466))='#skF_2' | ~r1_tarski('#skF_2', B_2466))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6060])).
% 6.64/2.33  tff(c_32, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.64/2.33  tff(c_3972, plain, (![A_2267]: (k1_relat_1(A_2267)!='#skF_2' | A_2267='#skF_2' | ~v1_relat_1(A_2267))), inference(demodulation, [status(thm), theory('equality')], [c_3952, c_3952, c_32])).
% 6.64/2.33  tff(c_3979, plain, (![A_8, B_9]: (k1_relat_1(k2_zfmisc_1(A_8, B_9))!='#skF_2' | k2_zfmisc_1(A_8, B_9)='#skF_2')), inference(resolution, [status(thm)], [c_18, c_3972])).
% 6.64/2.33  tff(c_6797, plain, (![B_2467]: (k2_zfmisc_1('#skF_2', B_2467)='#skF_2' | ~r1_tarski('#skF_2', B_2467))), inference(superposition, [status(thm), theory('equality')], [c_6637, c_3979])).
% 6.64/2.33  tff(c_6824, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_3966, c_6797])).
% 6.64/2.33  tff(c_4527, plain, (![A_2329, B_2330, C_2331]: (k1_relset_1(A_2329, B_2330, C_2331)=k1_relat_1(C_2331) | ~m1_subset_1(C_2331, k1_zfmisc_1(k2_zfmisc_1(A_2329, B_2330))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.64/2.33  tff(c_4674, plain, (![A_2357, B_2358, A_2359]: (k1_relset_1(A_2357, B_2358, A_2359)=k1_relat_1(A_2359) | ~r1_tarski(A_2359, k2_zfmisc_1(A_2357, B_2358)))), inference(resolution, [status(thm)], [c_16, c_4527])).
% 6.64/2.33  tff(c_4696, plain, (![A_2357, B_2358]: (k1_relset_1(A_2357, B_2358, k2_zfmisc_1(A_2357, B_2358))=k1_relat_1(k2_zfmisc_1(A_2357, B_2358)))), inference(resolution, [status(thm)], [c_8, c_4674])).
% 6.64/2.33  tff(c_52, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.64/2.33  tff(c_5349, plain, (![C_2399, B_2400]: (v1_funct_2(C_2399, '#skF_2', B_2400) | k1_relset_1('#skF_2', B_2400, C_2399)!='#skF_2' | ~m1_subset_1(C_2399, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_2400))))), inference(demodulation, [status(thm), theory('equality')], [c_3952, c_3952, c_3952, c_3952, c_52])).
% 6.64/2.33  tff(c_5379, plain, (![A_2403, B_2404]: (v1_funct_2(A_2403, '#skF_2', B_2404) | k1_relset_1('#skF_2', B_2404, A_2403)!='#skF_2' | ~r1_tarski(A_2403, k2_zfmisc_1('#skF_2', B_2404)))), inference(resolution, [status(thm)], [c_16, c_5349])).
% 6.64/2.33  tff(c_5394, plain, (![B_2404]: (v1_funct_2(k2_zfmisc_1('#skF_2', B_2404), '#skF_2', B_2404) | k1_relset_1('#skF_2', B_2404, k2_zfmisc_1('#skF_2', B_2404))!='#skF_2')), inference(resolution, [status(thm)], [c_8, c_5379])).
% 6.64/2.33  tff(c_5398, plain, (![B_2404]: (v1_funct_2(k2_zfmisc_1('#skF_2', B_2404), '#skF_2', B_2404) | k1_relat_1(k2_zfmisc_1('#skF_2', B_2404))!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4696, c_5394])).
% 6.64/2.33  tff(c_6872, plain, (v1_funct_2('#skF_2', '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6824, c_5398])).
% 6.64/2.33  tff(c_6975, plain, (v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4005, c_6824, c_6872])).
% 6.64/2.33  tff(c_6977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4006, c_6975])).
% 6.64/2.33  tff(c_6978, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_74])).
% 6.64/2.33  tff(c_7439, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_7408, c_6978])).
% 6.64/2.33  tff(c_7451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_8, c_68, c_7439])).
% 6.64/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.33  
% 6.64/2.33  Inference rules
% 6.64/2.33  ----------------------
% 6.64/2.33  #Ref     : 2
% 6.64/2.33  #Sup     : 1768
% 6.64/2.33  #Fact    : 0
% 6.64/2.33  #Define  : 0
% 6.64/2.33  #Split   : 27
% 6.64/2.33  #Chain   : 0
% 6.64/2.33  #Close   : 0
% 6.64/2.33  
% 6.64/2.33  Ordering : KBO
% 6.64/2.33  
% 6.64/2.33  Simplification rules
% 6.64/2.33  ----------------------
% 6.64/2.33  #Subsume      : 287
% 6.64/2.33  #Demod        : 1397
% 6.64/2.33  #Tautology    : 356
% 6.64/2.33  #SimpNegUnit  : 116
% 6.64/2.33  #BackRed      : 188
% 6.64/2.33  
% 6.64/2.33  #Partial instantiations: 134
% 6.64/2.33  #Strategies tried      : 1
% 6.64/2.33  
% 6.64/2.33  Timing (in seconds)
% 6.64/2.33  ----------------------
% 6.64/2.34  Preprocessing        : 0.34
% 6.64/2.34  Parsing              : 0.18
% 6.64/2.34  CNF conversion       : 0.02
% 6.64/2.34  Main loop            : 1.20
% 6.64/2.34  Inferencing          : 0.45
% 6.64/2.34  Reduction            : 0.36
% 6.64/2.34  Demodulation         : 0.25
% 6.64/2.34  BG Simplification    : 0.05
% 6.64/2.34  Subsumption          : 0.24
% 6.64/2.34  Abstraction          : 0.06
% 6.64/2.34  MUC search           : 0.00
% 6.64/2.34  Cooper               : 0.00
% 6.64/2.34  Total                : 1.60
% 6.64/2.34  Index Insertion      : 0.00
% 6.64/2.34  Index Deletion       : 0.00
% 6.64/2.34  Index Matching       : 0.00
% 6.64/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
