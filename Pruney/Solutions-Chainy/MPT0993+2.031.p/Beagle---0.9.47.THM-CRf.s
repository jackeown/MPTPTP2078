%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 9.81s
% Output     : CNFRefutation 10.02s
% Verified   : 
% Statistics : Number of formulae       :  253 (3530 expanded)
%              Number of leaves         :   38 (1092 expanded)
%              Depth                    :   23
%              Number of atoms          :  471 (8024 expanded)
%              Number of equality atoms :  124 (2870 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_112,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_125,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_112])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4529,plain,(
    ! [B_311,A_312] :
      ( v4_relat_1(B_311,A_312)
      | ~ r1_tarski(k1_relat_1(B_311),A_312)
      | ~ v1_relat_1(B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4544,plain,(
    ! [B_315] :
      ( v4_relat_1(B_315,k1_relat_1(B_315))
      | ~ v1_relat_1(B_315) ) ),
    inference(resolution,[status(thm)],[c_6,c_4529])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4548,plain,(
    ! [B_315] :
      ( k7_relat_1(B_315,k1_relat_1(B_315)) = B_315
      | ~ v1_relat_1(B_315) ) ),
    inference(resolution,[status(thm)],[c_4544,c_26])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_361,plain,(
    ! [B_80,A_81] :
      ( v4_relat_1(B_80,A_81)
      | ~ r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_408,plain,(
    ! [B_84] :
      ( v4_relat_1(B_84,k1_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_361])).

tff(c_412,plain,(
    ! [B_84] :
      ( k7_relat_1(B_84,k1_relat_1(B_84)) = B_84
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_408,c_26])).

tff(c_92,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_258,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_323,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_76,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_258])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,(
    ! [A_9,A_51,B_52] :
      ( v1_relat_1(A_9)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_51,B_52)) ) ),
    inference(resolution,[status(thm)],[c_20,c_112])).

tff(c_334,plain,(
    ! [A_77] :
      ( v1_relat_1(A_77)
      | ~ r1_tarski(A_77,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_323,c_124])).

tff(c_342,plain,(
    ! [A_15] :
      ( v1_relat_1(k7_relat_1('#skF_5',A_15))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_334])).

tff(c_354,plain,(
    ! [A_15] : v1_relat_1(k7_relat_1('#skF_5',A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_342])).

tff(c_618,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_633,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_618])).

tff(c_272,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_68,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_258])).

tff(c_735,plain,(
    ! [A_123,B_124,A_125] :
      ( k1_relset_1(A_123,B_124,A_125) = k1_relat_1(A_125)
      | ~ r1_tarski(A_125,k2_zfmisc_1(A_123,B_124)) ) ),
    inference(resolution,[status(thm)],[c_20,c_618])).

tff(c_797,plain,(
    ! [A_130] :
      ( k1_relset_1('#skF_2','#skF_3',A_130) = k1_relat_1(A_130)
      | ~ r1_tarski(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_272,c_735])).

tff(c_809,plain,(
    ! [A_15] :
      ( k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5',A_15)) = k1_relat_1(k7_relat_1('#skF_5',A_15))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_797])).

tff(c_844,plain,(
    ! [A_133] : k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5',A_133)) = k1_relat_1(k7_relat_1('#skF_5',A_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_809])).

tff(c_854,plain,
    ( k1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) = k1_relset_1('#skF_2','#skF_3','#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_844])).

tff(c_858,plain,(
    k1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_633,c_854])).

tff(c_375,plain,(
    ! [B_80] :
      ( v4_relat_1(B_80,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_361])).

tff(c_871,plain,
    ( v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),k1_relat_1('#skF_5'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_375])).

tff(c_899,plain,(
    v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_871])).

tff(c_919,plain,
    ( v4_relat_1('#skF_5',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_899])).

tff(c_924,plain,(
    v4_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_919])).

tff(c_927,plain,
    ( k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_924,c_26])).

tff(c_930,plain,(
    k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_927])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_886,plain,(
    ! [A_11] :
      ( r1_tarski(k1_relat_1('#skF_5'),A_11)
      | ~ v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),A_11)
      | ~ v1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_24])).

tff(c_909,plain,(
    ! [A_11] :
      ( r1_tarski(k1_relat_1('#skF_5'),A_11)
      | ~ v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_886])).

tff(c_1047,plain,(
    ! [A_144] :
      ( r1_tarski(k1_relat_1('#skF_5'),A_144)
      | ~ v4_relat_1('#skF_5',A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_909])).

tff(c_54,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_276,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,'#skF_4')
      | ~ r1_tarski(A_68,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_258])).

tff(c_1118,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1047,c_276])).

tff(c_1125,plain,(
    ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1118])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1206,plain,(
    ! [B_149,A_150,C_151] :
      ( k1_xboole_0 = B_149
      | k1_relset_1(A_150,B_149,C_151) = A_150
      | ~ v1_funct_2(C_151,A_150,B_149)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1213,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1206])).

tff(c_1223,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_633,c_1213])).

tff(c_1225,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_1230,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_924])).

tff(c_1233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1125,c_1230])).

tff(c_1234,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1263,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_10])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1261,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1234,c_14])).

tff(c_126,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_126])).

tff(c_248,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_1330,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_248])).

tff(c_1337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1330])).

tff(c_1339,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1118])).

tff(c_299,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,'#skF_4')
      | ~ r1_tarski(A_75,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_258])).

tff(c_397,plain,(
    ! [B_83] :
      ( r1_tarski(k1_relat_1(B_83),'#skF_4')
      | ~ v4_relat_1(B_83,'#skF_2')
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_24,c_299])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( v4_relat_1(B_12,A_11)
      | ~ r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_405,plain,(
    ! [B_83] :
      ( v4_relat_1(B_83,'#skF_4')
      | ~ v4_relat_1(B_83,'#skF_2')
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_397,c_22])).

tff(c_1361,plain,
    ( v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1339,c_405])).

tff(c_1367,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_1361])).

tff(c_1373,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1367,c_26])).

tff(c_1376,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_1373])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_931,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k2_partfun1(A_134,B_135,C_136,D_137) = k7_relat_1(C_136,D_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_936,plain,(
    ! [D_137] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_137) = k7_relat_1('#skF_5',D_137)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_931])).

tff(c_944,plain,(
    ! [D_137] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_137) = k7_relat_1('#skF_5',D_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_936])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_986,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_52])).

tff(c_1484,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_986])).

tff(c_48,plain,(
    ! [D_36,A_30,B_31,C_32] :
      ( k1_funct_1(D_36,'#skF_1'(A_30,B_31,C_32,D_36)) != k1_funct_1(C_32,'#skF_1'(A_30,B_31,C_32,D_36))
      | r2_relset_1(A_30,B_31,C_32,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(D_36,A_30,B_31)
      | ~ v1_funct_1(D_36)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4372,plain,(
    ! [A_293,B_294,C_295] :
      ( r2_relset_1(A_293,B_294,C_295,C_295)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ v1_funct_2(C_295,A_293,B_294)
      | ~ v1_funct_1(C_295)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ v1_funct_2(C_295,A_293,B_294)
      | ~ v1_funct_1(C_295) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_48])).

tff(c_4377,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_4372])).

tff(c_4385,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_4377])).

tff(c_4387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1484,c_4385])).

tff(c_4388,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_4420,plain,(
    ! [A_298] :
      ( v1_relat_1(A_298)
      | ~ r1_tarski(A_298,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_124])).

tff(c_4428,plain,(
    ! [A_15] :
      ( v1_relat_1(k7_relat_1('#skF_5',A_15))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_4420])).

tff(c_4440,plain,(
    ! [A_15] : v1_relat_1(k7_relat_1('#skF_5',A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_4428])).

tff(c_4398,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4388,c_56])).

tff(c_4761,plain,(
    ! [A_337,B_338,C_339] :
      ( k1_relset_1(A_337,B_338,C_339) = k1_relat_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4871,plain,(
    ! [C_352] :
      ( k1_relset_1('#skF_2','#skF_3',C_352) = k1_relat_1(C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_4761])).

tff(c_4879,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4398,c_4871])).

tff(c_4885,plain,(
    ! [A_353] :
      ( k1_relset_1('#skF_2','#skF_3',A_353) = k1_relat_1(A_353)
      | ~ r1_tarski(A_353,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_4871])).

tff(c_4897,plain,(
    ! [A_15] :
      ( k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5',A_15)) = k1_relat_1(k7_relat_1('#skF_5',A_15))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_4885])).

tff(c_4918,plain,(
    ! [A_354] : k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5',A_354)) = k1_relat_1(k7_relat_1('#skF_5',A_354)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_4897])).

tff(c_4928,plain,
    ( k1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) = k1_relset_1('#skF_2','#skF_3','#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4548,c_4918])).

tff(c_4932,plain,(
    k1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_4879,c_4928])).

tff(c_4542,plain,(
    ! [B_311] :
      ( v4_relat_1(B_311,k1_relat_1(B_311))
      | ~ v1_relat_1(B_311) ) ),
    inference(resolution,[status(thm)],[c_6,c_4529])).

tff(c_4948,plain,
    ( v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),k1_relat_1('#skF_5'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4932,c_4542])).

tff(c_4978,plain,(
    v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4440,c_4948])).

tff(c_5008,plain,
    ( v4_relat_1('#skF_5',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4548,c_4978])).

tff(c_5013,plain,(
    v4_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_5008])).

tff(c_5017,plain,
    ( k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5013,c_26])).

tff(c_5020,plain,(
    k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_5017])).

tff(c_4458,plain,(
    ! [A_301,C_302,B_303] :
      ( r1_tarski(A_301,C_302)
      | ~ r1_tarski(B_303,C_302)
      | ~ r1_tarski(A_301,B_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4495,plain,(
    ! [A_306] :
      ( r1_tarski(A_306,'#skF_4')
      | ~ r1_tarski(A_306,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_4458])).

tff(c_4512,plain,(
    ! [B_12] :
      ( r1_tarski(k1_relat_1(B_12),'#skF_4')
      | ~ v4_relat_1(B_12,'#skF_2')
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_24,c_4495])).

tff(c_4960,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | ~ v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4932,c_4512])).

tff(c_4986,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | ~ v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4440,c_4960])).

tff(c_5014,plain,(
    ~ v4_relat_1(k7_relat_1('#skF_5',k1_relat_1('#skF_5')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4986])).

tff(c_5062,plain,(
    ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5020,c_5014])).

tff(c_5541,plain,(
    ! [B_400,C_401,A_402] :
      ( k1_xboole_0 = B_400
      | v1_funct_2(C_401,A_402,B_400)
      | k1_relset_1(A_402,B_400,C_401) != A_402
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_400))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5544,plain,(
    ! [C_401] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_401,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_401) != '#skF_2'
      | ~ m1_subset_1(C_401,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_5541])).

tff(c_5709,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5544])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4409,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_12])).

tff(c_4446,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4409])).

tff(c_5732,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5709,c_4446])).

tff(c_5739,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5709,c_5709,c_14])).

tff(c_5869,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_4388])).

tff(c_5871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5732,c_5869])).

tff(c_5873,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5544])).

tff(c_5380,plain,(
    ! [B_382,A_383,C_384] :
      ( k1_xboole_0 = B_382
      | k1_relset_1(A_383,B_382,C_384) = A_383
      | ~ v1_funct_2(C_384,A_383,B_382)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_383,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5383,plain,(
    ! [C_384] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_384) = '#skF_2'
      | ~ v1_funct_2(C_384,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_384,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_5380])).

tff(c_6046,plain,(
    ! [C_431] :
      ( k1_relset_1('#skF_2','#skF_3',C_431) = '#skF_2'
      | ~ v1_funct_2(C_431,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_431,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5873,c_5383])).

tff(c_6049,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_4398,c_6046])).

tff(c_6056,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4879,c_6049])).

tff(c_6065,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6056,c_5013])).

tff(c_6068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5062,c_6065])).

tff(c_6069,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4986])).

tff(c_6073,plain,
    ( v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6069,c_22])).

tff(c_6080,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_6073])).

tff(c_6085,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6080,c_26])).

tff(c_6088,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_6085])).

tff(c_6252,plain,(
    ! [A_437,B_438,C_439,D_440] :
      ( k2_partfun1(A_437,B_438,C_439,D_440) = k7_relat_1(C_439,D_440)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438)))
      | ~ v1_funct_1(C_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6266,plain,(
    ! [C_441,D_442] :
      ( k2_partfun1('#skF_2','#skF_3',C_441,D_442) = k7_relat_1(C_441,D_442)
      | ~ m1_subset_1(C_441,k1_zfmisc_1('#skF_5'))
      | ~ v1_funct_1(C_441) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_6252])).

tff(c_6268,plain,(
    ! [D_442] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_442) = k7_relat_1('#skF_5',D_442)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4398,c_6266])).

tff(c_6274,plain,(
    ! [D_442] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_442) = k7_relat_1('#skF_5',D_442) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6268])).

tff(c_6288,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_52])).

tff(c_6289,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6088,c_6288])).

tff(c_8531,plain,(
    ! [A_600,B_601,C_602] :
      ( r2_relset_1(A_600,B_601,C_602,C_602)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601)))
      | ~ v1_funct_2(C_602,A_600,B_601)
      | ~ v1_funct_1(C_602)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601)))
      | ~ v1_funct_2(C_602,A_600,B_601)
      | ~ v1_funct_1(C_602) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_48])).

tff(c_14445,plain,(
    ! [A_928,B_929,A_930] :
      ( r2_relset_1(A_928,B_929,A_930,A_930)
      | ~ m1_subset_1(A_930,k1_zfmisc_1(k2_zfmisc_1(A_928,B_929)))
      | ~ v1_funct_2(A_930,A_928,B_929)
      | ~ v1_funct_1(A_930)
      | ~ r1_tarski(A_930,k2_zfmisc_1(A_928,B_929)) ) ),
    inference(resolution,[status(thm)],[c_20,c_8531])).

tff(c_14447,plain,(
    ! [A_930] :
      ( r2_relset_1('#skF_2','#skF_3',A_930,A_930)
      | ~ m1_subset_1(A_930,k1_zfmisc_1('#skF_5'))
      | ~ v1_funct_2(A_930,'#skF_2','#skF_3')
      | ~ v1_funct_1(A_930)
      | ~ r1_tarski(A_930,k2_zfmisc_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_14445])).

tff(c_14512,plain,(
    ! [A_934] :
      ( r2_relset_1('#skF_2','#skF_3',A_934,A_934)
      | ~ m1_subset_1(A_934,k1_zfmisc_1('#skF_5'))
      | ~ v1_funct_2(A_934,'#skF_2','#skF_3')
      | ~ v1_funct_1(A_934)
      | ~ r1_tarski(A_934,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4388,c_14447])).

tff(c_14514,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_4398,c_14512])).

tff(c_14520,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_60,c_58,c_14514])).

tff(c_14522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6289,c_14520])).

tff(c_14524,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4409])).

tff(c_14523,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4409])).

tff(c_14569,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14524,c_14524,c_14523])).

tff(c_14570,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14569])).

tff(c_14579,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14570,c_58])).

tff(c_14580,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14570,c_60])).

tff(c_14533,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14524,c_10])).

tff(c_14572,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14570,c_14533])).

tff(c_16677,plain,(
    ! [A_1143,B_1144,C_1145] :
      ( r2_relset_1(A_1143,B_1144,C_1145,C_1145)
      | ~ m1_subset_1(C_1145,k1_zfmisc_1(k2_zfmisc_1(A_1143,B_1144)))
      | ~ v1_funct_2(C_1145,A_1143,B_1144)
      | ~ v1_funct_1(C_1145)
      | ~ m1_subset_1(C_1145,k1_zfmisc_1(k2_zfmisc_1(A_1143,B_1144)))
      | ~ v1_funct_2(C_1145,A_1143,B_1144)
      | ~ v1_funct_1(C_1145) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_48])).

tff(c_18138,plain,(
    ! [A_1284,B_1285,A_1286] :
      ( r2_relset_1(A_1284,B_1285,A_1286,A_1286)
      | ~ m1_subset_1(A_1286,k1_zfmisc_1(k2_zfmisc_1(A_1284,B_1285)))
      | ~ v1_funct_2(A_1286,A_1284,B_1285)
      | ~ v1_funct_1(A_1286)
      | ~ r1_tarski(A_1286,k2_zfmisc_1(A_1284,B_1285)) ) ),
    inference(resolution,[status(thm)],[c_20,c_16677])).

tff(c_18173,plain,(
    ! [A_1291,B_1292,A_1293] :
      ( r2_relset_1(A_1291,B_1292,A_1293,A_1293)
      | ~ v1_funct_2(A_1293,A_1291,B_1292)
      | ~ v1_funct_1(A_1293)
      | ~ r1_tarski(A_1293,k2_zfmisc_1(A_1291,B_1292)) ) ),
    inference(resolution,[status(thm)],[c_20,c_18138])).

tff(c_18209,plain,(
    ! [A_1291,B_1292] :
      ( r2_relset_1(A_1291,B_1292,'#skF_3','#skF_3')
      | ~ v1_funct_2('#skF_3',A_1291,B_1292)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14572,c_18173])).

tff(c_18240,plain,(
    ! [A_1294,B_1295] :
      ( r2_relset_1(A_1294,B_1295,'#skF_3','#skF_3')
      | ~ v1_funct_2('#skF_3',A_1294,B_1295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14580,c_18209])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [C_56] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_112])).

tff(c_170,plain,(
    ! [A_57] :
      ( v1_relat_1(A_57)
      | ~ r1_tarski(A_57,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_184,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_145,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_158,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_202,plain,(
    ! [A_15] : k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_158])).

tff(c_14525,plain,(
    ! [A_15] : k7_relat_1('#skF_5',A_15) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14524,c_14524,c_202])).

tff(c_14571,plain,(
    ! [A_15] : k7_relat_1('#skF_3',A_15) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14570,c_14570,c_14525])).

tff(c_14575,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14570,c_14570,c_4398])).

tff(c_14531,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14524,c_14524,c_14])).

tff(c_14615,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14570,c_14570,c_14531])).

tff(c_15422,plain,(
    ! [A_1027,B_1028,C_1029,D_1030] :
      ( k2_partfun1(A_1027,B_1028,C_1029,D_1030) = k7_relat_1(C_1029,D_1030)
      | ~ m1_subset_1(C_1029,k1_zfmisc_1(k2_zfmisc_1(A_1027,B_1028)))
      | ~ v1_funct_1(C_1029) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16357,plain,(
    ! [A_1114,C_1115,D_1116] :
      ( k2_partfun1(A_1114,'#skF_3',C_1115,D_1116) = k7_relat_1(C_1115,D_1116)
      | ~ m1_subset_1(C_1115,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_1(C_1115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14615,c_15422])).

tff(c_16359,plain,(
    ! [A_1114,D_1116] :
      ( k2_partfun1(A_1114,'#skF_3','#skF_3',D_1116) = k7_relat_1('#skF_3',D_1116)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14575,c_16357])).

tff(c_16365,plain,(
    ! [A_1114,D_1116] : k2_partfun1(A_1114,'#skF_3','#skF_3',D_1116) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14580,c_14571,c_16359])).

tff(c_14578,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14570,c_14570,c_52])).

tff(c_16367,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16365,c_14578])).

tff(c_18243,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18240,c_16367])).

tff(c_18247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14579,c_18243])).

tff(c_18248,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14569])).

tff(c_18263,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_14533])).

tff(c_18550,plain,(
    ! [A_1322,B_1323,C_1324] :
      ( k1_relset_1(A_1322,B_1323,C_1324) = k1_relat_1(C_1324)
      | ~ m1_subset_1(C_1324,k1_zfmisc_1(k2_zfmisc_1(A_1322,B_1323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18742,plain,(
    ! [A_1350,B_1351,A_1352] :
      ( k1_relset_1(A_1350,B_1351,A_1352) = k1_relat_1(A_1352)
      | ~ r1_tarski(A_1352,k2_zfmisc_1(A_1350,B_1351)) ) ),
    inference(resolution,[status(thm)],[c_20,c_18550])).

tff(c_18770,plain,(
    ! [A_1350,B_1351] : k1_relset_1(A_1350,B_1351,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18263,c_18742])).

tff(c_18266,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_18248,c_4398])).

tff(c_18264,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_14524])).

tff(c_38,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_18803,plain,(
    ! [C_1357,B_1358] :
      ( v1_funct_2(C_1357,'#skF_2',B_1358)
      | k1_relset_1('#skF_2',B_1358,C_1357) != '#skF_2'
      | ~ m1_subset_1(C_1357,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18264,c_18264,c_18264,c_18264,c_61])).

tff(c_18805,plain,(
    ! [B_1358] :
      ( v1_funct_2('#skF_2','#skF_2',B_1358)
      | k1_relset_1('#skF_2',B_1358,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_18266,c_18803])).

tff(c_18810,plain,(
    ! [B_1358] :
      ( v1_funct_2('#skF_2','#skF_2',B_1358)
      | k1_relat_1('#skF_2') != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18770,c_18805])).

tff(c_18812,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18810])).

tff(c_18270,plain,(
    v1_funct_2('#skF_2','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_58])).

tff(c_42,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_18926,plain,(
    ! [B_1375,C_1376] :
      ( k1_relset_1('#skF_2',B_1375,C_1376) = '#skF_2'
      | ~ v1_funct_2(C_1376,'#skF_2',B_1375)
      | ~ m1_subset_1(C_1376,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18264,c_18264,c_18264,c_18264,c_62])).

tff(c_18933,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18270,c_18926])).

tff(c_18942,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18266,c_18770,c_18933])).

tff(c_18944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18812,c_18942])).

tff(c_18945,plain,(
    ! [B_1358] : v1_funct_2('#skF_2','#skF_2',B_1358) ),
    inference(splitRight,[status(thm)],[c_18810])).

tff(c_18271,plain,(
    v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_60])).

tff(c_20235,plain,(
    ! [A_1493,B_1494,C_1495] :
      ( r2_relset_1(A_1493,B_1494,C_1495,C_1495)
      | ~ m1_subset_1(C_1495,k1_zfmisc_1(k2_zfmisc_1(A_1493,B_1494)))
      | ~ v1_funct_2(C_1495,A_1493,B_1494)
      | ~ v1_funct_1(C_1495)
      | ~ m1_subset_1(C_1495,k1_zfmisc_1(k2_zfmisc_1(A_1493,B_1494)))
      | ~ v1_funct_2(C_1495,A_1493,B_1494)
      | ~ v1_funct_1(C_1495) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_48])).

tff(c_22386,plain,(
    ! [A_1671,B_1672,A_1673] :
      ( r2_relset_1(A_1671,B_1672,A_1673,A_1673)
      | ~ m1_subset_1(A_1673,k1_zfmisc_1(k2_zfmisc_1(A_1671,B_1672)))
      | ~ v1_funct_2(A_1673,A_1671,B_1672)
      | ~ v1_funct_1(A_1673)
      | ~ r1_tarski(A_1673,k2_zfmisc_1(A_1671,B_1672)) ) ),
    inference(resolution,[status(thm)],[c_20,c_20235])).

tff(c_22397,plain,(
    ! [A_1674,B_1675,A_1676] :
      ( r2_relset_1(A_1674,B_1675,A_1676,A_1676)
      | ~ v1_funct_2(A_1676,A_1674,B_1675)
      | ~ v1_funct_1(A_1676)
      | ~ r1_tarski(A_1676,k2_zfmisc_1(A_1674,B_1675)) ) ),
    inference(resolution,[status(thm)],[c_20,c_22386])).

tff(c_22430,plain,(
    ! [A_1674,B_1675] :
      ( r2_relset_1(A_1674,B_1675,'#skF_2','#skF_2')
      | ~ v1_funct_2('#skF_2',A_1674,B_1675)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18263,c_22397])).

tff(c_22460,plain,(
    ! [A_1677,B_1678] :
      ( r2_relset_1(A_1677,B_1678,'#skF_2','#skF_2')
      | ~ v1_funct_2('#skF_2',A_1677,B_1678) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18271,c_22430])).

tff(c_18262,plain,(
    ! [A_15] : k7_relat_1('#skF_2',A_15) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_18248,c_14525])).

tff(c_19097,plain,(
    ! [A_1385,B_1386,C_1387,D_1388] :
      ( k2_partfun1(A_1385,B_1386,C_1387,D_1388) = k7_relat_1(C_1387,D_1388)
      | ~ m1_subset_1(C_1387,k1_zfmisc_1(k2_zfmisc_1(A_1385,B_1386)))
      | ~ v1_funct_1(C_1387) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_19953,plain,(
    ! [A_1461,B_1462,A_1463,D_1464] :
      ( k2_partfun1(A_1461,B_1462,A_1463,D_1464) = k7_relat_1(A_1463,D_1464)
      | ~ v1_funct_1(A_1463)
      | ~ r1_tarski(A_1463,k2_zfmisc_1(A_1461,B_1462)) ) ),
    inference(resolution,[status(thm)],[c_20,c_19097])).

tff(c_19971,plain,(
    ! [A_1461,B_1462,D_1464] :
      ( k2_partfun1(A_1461,B_1462,'#skF_2',D_1464) = k7_relat_1('#skF_2',D_1464)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18263,c_19953])).

tff(c_19989,plain,(
    ! [A_1461,B_1462,D_1464] : k2_partfun1(A_1461,B_1462,'#skF_2',D_1464) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18271,c_18262,c_19971])).

tff(c_18269,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18248,c_18248,c_52])).

tff(c_19995,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19989,c_18269])).

tff(c_22463,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22460,c_19995])).

tff(c_22467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18945,c_22463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.81/3.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.93/3.82  
% 9.93/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.93/3.83  %$ r2_relset_1 > v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.93/3.83  
% 9.93/3.83  %Foreground sorts:
% 9.93/3.83  
% 9.93/3.83  
% 9.93/3.83  %Background operators:
% 9.93/3.83  
% 9.93/3.83  
% 9.93/3.83  %Foreground operators:
% 9.93/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.93/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.93/3.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.93/3.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.93/3.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.93/3.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.93/3.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.93/3.83  tff('#skF_5', type, '#skF_5': $i).
% 9.93/3.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.93/3.83  tff('#skF_2', type, '#skF_2': $i).
% 9.93/3.83  tff('#skF_3', type, '#skF_3': $i).
% 9.93/3.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.93/3.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.93/3.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.93/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.93/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.93/3.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.93/3.83  tff('#skF_4', type, '#skF_4': $i).
% 9.93/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.93/3.83  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.93/3.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.93/3.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.93/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.93/3.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.93/3.83  
% 10.02/3.86  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 10.02/3.86  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.02/3.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.02/3.86  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 10.02/3.86  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 10.02/3.86  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 10.02/3.86  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.02/3.86  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.02/3.86  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.02/3.86  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.02/3.86  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.02/3.86  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.02/3.86  tff(f_97, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 10.02/3.86  tff(f_117, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 10.02/3.86  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.02/3.86  tff(c_112, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.02/3.86  tff(c_125, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_112])).
% 10.02/3.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.02/3.86  tff(c_4529, plain, (![B_311, A_312]: (v4_relat_1(B_311, A_312) | ~r1_tarski(k1_relat_1(B_311), A_312) | ~v1_relat_1(B_311))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.02/3.86  tff(c_4544, plain, (![B_315]: (v4_relat_1(B_315, k1_relat_1(B_315)) | ~v1_relat_1(B_315))), inference(resolution, [status(thm)], [c_6, c_4529])).
% 10.02/3.86  tff(c_26, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.02/3.86  tff(c_4548, plain, (![B_315]: (k7_relat_1(B_315, k1_relat_1(B_315))=B_315 | ~v1_relat_1(B_315))), inference(resolution, [status(thm)], [c_4544, c_26])).
% 10.02/3.86  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.02/3.86  tff(c_361, plain, (![B_80, A_81]: (v4_relat_1(B_80, A_81) | ~r1_tarski(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.02/3.86  tff(c_408, plain, (![B_84]: (v4_relat_1(B_84, k1_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_6, c_361])).
% 10.02/3.86  tff(c_412, plain, (![B_84]: (k7_relat_1(B_84, k1_relat_1(B_84))=B_84 | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_408, c_26])).
% 10.02/3.86  tff(c_92, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.02/3.86  tff(c_100, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_92])).
% 10.02/3.86  tff(c_258, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.02/3.86  tff(c_323, plain, (![A_76]: (r1_tarski(A_76, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_76, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_258])).
% 10.02/3.86  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.02/3.86  tff(c_124, plain, (![A_9, A_51, B_52]: (v1_relat_1(A_9) | ~r1_tarski(A_9, k2_zfmisc_1(A_51, B_52)))), inference(resolution, [status(thm)], [c_20, c_112])).
% 10.02/3.86  tff(c_334, plain, (![A_77]: (v1_relat_1(A_77) | ~r1_tarski(A_77, '#skF_5'))), inference(resolution, [status(thm)], [c_323, c_124])).
% 10.02/3.86  tff(c_342, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_5', A_15)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_334])).
% 10.02/3.86  tff(c_354, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_5', A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_342])).
% 10.02/3.86  tff(c_618, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.02/3.86  tff(c_633, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_618])).
% 10.02/3.86  tff(c_272, plain, (![A_68]: (r1_tarski(A_68, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_68, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_258])).
% 10.02/3.86  tff(c_735, plain, (![A_123, B_124, A_125]: (k1_relset_1(A_123, B_124, A_125)=k1_relat_1(A_125) | ~r1_tarski(A_125, k2_zfmisc_1(A_123, B_124)))), inference(resolution, [status(thm)], [c_20, c_618])).
% 10.02/3.86  tff(c_797, plain, (![A_130]: (k1_relset_1('#skF_2', '#skF_3', A_130)=k1_relat_1(A_130) | ~r1_tarski(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_272, c_735])).
% 10.02/3.86  tff(c_809, plain, (![A_15]: (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', A_15))=k1_relat_1(k7_relat_1('#skF_5', A_15)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_797])).
% 10.02/3.86  tff(c_844, plain, (![A_133]: (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', A_133))=k1_relat_1(k7_relat_1('#skF_5', A_133)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_809])).
% 10.02/3.86  tff(c_854, plain, (k1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')))=k1_relset_1('#skF_2', '#skF_3', '#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_412, c_844])).
% 10.02/3.86  tff(c_858, plain, (k1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')))=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_633, c_854])).
% 10.02/3.86  tff(c_375, plain, (![B_80]: (v4_relat_1(B_80, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_6, c_361])).
% 10.02/3.86  tff(c_871, plain, (v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), k1_relat_1('#skF_5')) | ~v1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_858, c_375])).
% 10.02/3.86  tff(c_899, plain, (v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_871])).
% 10.02/3.86  tff(c_919, plain, (v4_relat_1('#skF_5', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_412, c_899])).
% 10.02/3.86  tff(c_924, plain, (v4_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_919])).
% 10.02/3.86  tff(c_927, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_924, c_26])).
% 10.02/3.86  tff(c_930, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_927])).
% 10.02/3.86  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.02/3.86  tff(c_886, plain, (![A_11]: (r1_tarski(k1_relat_1('#skF_5'), A_11) | ~v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), A_11) | ~v1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_858, c_24])).
% 10.02/3.86  tff(c_909, plain, (![A_11]: (r1_tarski(k1_relat_1('#skF_5'), A_11) | ~v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_886])).
% 10.02/3.86  tff(c_1047, plain, (![A_144]: (r1_tarski(k1_relat_1('#skF_5'), A_144) | ~v4_relat_1('#skF_5', A_144))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_909])).
% 10.02/3.86  tff(c_54, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.02/3.86  tff(c_276, plain, (![A_68]: (r1_tarski(A_68, '#skF_4') | ~r1_tarski(A_68, '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_258])).
% 10.02/3.86  tff(c_1118, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | ~v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1047, c_276])).
% 10.02/3.86  tff(c_1125, plain, (~v4_relat_1('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_1118])).
% 10.02/3.86  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.02/3.86  tff(c_1206, plain, (![B_149, A_150, C_151]: (k1_xboole_0=B_149 | k1_relset_1(A_150, B_149, C_151)=A_150 | ~v1_funct_2(C_151, A_150, B_149) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.02/3.86  tff(c_1213, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_1206])).
% 10.02/3.86  tff(c_1223, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_633, c_1213])).
% 10.02/3.86  tff(c_1225, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_1223])).
% 10.02/3.86  tff(c_1230, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_924])).
% 10.02/3.86  tff(c_1233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1125, c_1230])).
% 10.02/3.86  tff(c_1234, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1223])).
% 10.02/3.86  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.02/3.86  tff(c_1263, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_10])).
% 10.02/3.86  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.02/3.86  tff(c_1261, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1234, c_14])).
% 10.02/3.86  tff(c_126, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.02/3.86  tff(c_137, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_100, c_126])).
% 10.02/3.86  tff(c_248, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_137])).
% 10.02/3.86  tff(c_1330, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_248])).
% 10.02/3.86  tff(c_1337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1330])).
% 10.02/3.86  tff(c_1339, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_1118])).
% 10.02/3.86  tff(c_299, plain, (![A_75]: (r1_tarski(A_75, '#skF_4') | ~r1_tarski(A_75, '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_258])).
% 10.02/3.86  tff(c_397, plain, (![B_83]: (r1_tarski(k1_relat_1(B_83), '#skF_4') | ~v4_relat_1(B_83, '#skF_2') | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_24, c_299])).
% 10.02/3.86  tff(c_22, plain, (![B_12, A_11]: (v4_relat_1(B_12, A_11) | ~r1_tarski(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.02/3.86  tff(c_405, plain, (![B_83]: (v4_relat_1(B_83, '#skF_4') | ~v4_relat_1(B_83, '#skF_2') | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_397, c_22])).
% 10.02/3.86  tff(c_1361, plain, (v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1339, c_405])).
% 10.02/3.86  tff(c_1367, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_1361])).
% 10.02/3.86  tff(c_1373, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1367, c_26])).
% 10.02/3.86  tff(c_1376, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_1373])).
% 10.02/3.86  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.02/3.86  tff(c_931, plain, (![A_134, B_135, C_136, D_137]: (k2_partfun1(A_134, B_135, C_136, D_137)=k7_relat_1(C_136, D_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.02/3.86  tff(c_936, plain, (![D_137]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_137)=k7_relat_1('#skF_5', D_137) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_931])).
% 10.02/3.86  tff(c_944, plain, (![D_137]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_137)=k7_relat_1('#skF_5', D_137))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_936])).
% 10.02/3.86  tff(c_52, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.02/3.86  tff(c_986, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_944, c_52])).
% 10.02/3.86  tff(c_1484, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_986])).
% 10.02/3.86  tff(c_48, plain, (![D_36, A_30, B_31, C_32]: (k1_funct_1(D_36, '#skF_1'(A_30, B_31, C_32, D_36))!=k1_funct_1(C_32, '#skF_1'(A_30, B_31, C_32, D_36)) | r2_relset_1(A_30, B_31, C_32, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(D_36, A_30, B_31) | ~v1_funct_1(D_36) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.02/3.86  tff(c_4372, plain, (![A_293, B_294, C_295]: (r2_relset_1(A_293, B_294, C_295, C_295) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~v1_funct_2(C_295, A_293, B_294) | ~v1_funct_1(C_295) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~v1_funct_2(C_295, A_293, B_294) | ~v1_funct_1(C_295))), inference(reflexivity, [status(thm), theory('equality')], [c_48])).
% 10.02/3.86  tff(c_4377, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_4372])).
% 10.02/3.86  tff(c_4385, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_4377])).
% 10.02/3.86  tff(c_4387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1484, c_4385])).
% 10.02/3.86  tff(c_4388, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_137])).
% 10.02/3.86  tff(c_4420, plain, (![A_298]: (v1_relat_1(A_298) | ~r1_tarski(A_298, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_124])).
% 10.02/3.86  tff(c_4428, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_5', A_15)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_4420])).
% 10.02/3.86  tff(c_4440, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_5', A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_4428])).
% 10.02/3.86  tff(c_4398, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4388, c_56])).
% 10.02/3.86  tff(c_4761, plain, (![A_337, B_338, C_339]: (k1_relset_1(A_337, B_338, C_339)=k1_relat_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.02/3.86  tff(c_4871, plain, (![C_352]: (k1_relset_1('#skF_2', '#skF_3', C_352)=k1_relat_1(C_352) | ~m1_subset_1(C_352, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_4761])).
% 10.02/3.86  tff(c_4879, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4398, c_4871])).
% 10.02/3.86  tff(c_4885, plain, (![A_353]: (k1_relset_1('#skF_2', '#skF_3', A_353)=k1_relat_1(A_353) | ~r1_tarski(A_353, '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_4871])).
% 10.02/3.86  tff(c_4897, plain, (![A_15]: (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', A_15))=k1_relat_1(k7_relat_1('#skF_5', A_15)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_4885])).
% 10.02/3.86  tff(c_4918, plain, (![A_354]: (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', A_354))=k1_relat_1(k7_relat_1('#skF_5', A_354)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_4897])).
% 10.02/3.86  tff(c_4928, plain, (k1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')))=k1_relset_1('#skF_2', '#skF_3', '#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4548, c_4918])).
% 10.02/3.86  tff(c_4932, plain, (k1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')))=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_4879, c_4928])).
% 10.02/3.86  tff(c_4542, plain, (![B_311]: (v4_relat_1(B_311, k1_relat_1(B_311)) | ~v1_relat_1(B_311))), inference(resolution, [status(thm)], [c_6, c_4529])).
% 10.02/3.86  tff(c_4948, plain, (v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), k1_relat_1('#skF_5')) | ~v1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4932, c_4542])).
% 10.02/3.86  tff(c_4978, plain, (v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4440, c_4948])).
% 10.02/3.86  tff(c_5008, plain, (v4_relat_1('#skF_5', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4548, c_4978])).
% 10.02/3.86  tff(c_5013, plain, (v4_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_5008])).
% 10.02/3.86  tff(c_5017, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5013, c_26])).
% 10.02/3.86  tff(c_5020, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_5017])).
% 10.02/3.86  tff(c_4458, plain, (![A_301, C_302, B_303]: (r1_tarski(A_301, C_302) | ~r1_tarski(B_303, C_302) | ~r1_tarski(A_301, B_303))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.02/3.86  tff(c_4495, plain, (![A_306]: (r1_tarski(A_306, '#skF_4') | ~r1_tarski(A_306, '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_4458])).
% 10.02/3.86  tff(c_4512, plain, (![B_12]: (r1_tarski(k1_relat_1(B_12), '#skF_4') | ~v4_relat_1(B_12, '#skF_2') | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_24, c_4495])).
% 10.02/3.86  tff(c_4960, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | ~v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4932, c_4512])).
% 10.02/3.86  tff(c_4986, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | ~v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4440, c_4960])).
% 10.02/3.86  tff(c_5014, plain, (~v4_relat_1(k7_relat_1('#skF_5', k1_relat_1('#skF_5')), '#skF_2')), inference(splitLeft, [status(thm)], [c_4986])).
% 10.02/3.86  tff(c_5062, plain, (~v4_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5020, c_5014])).
% 10.02/3.86  tff(c_5541, plain, (![B_400, C_401, A_402]: (k1_xboole_0=B_400 | v1_funct_2(C_401, A_402, B_400) | k1_relset_1(A_402, B_400, C_401)!=A_402 | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_402, B_400))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.02/3.86  tff(c_5544, plain, (![C_401]: (k1_xboole_0='#skF_3' | v1_funct_2(C_401, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_401)!='#skF_2' | ~m1_subset_1(C_401, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_5541])).
% 10.02/3.86  tff(c_5709, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5544])).
% 10.02/3.86  tff(c_12, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.02/3.86  tff(c_4409, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4388, c_12])).
% 10.02/3.86  tff(c_4446, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_4409])).
% 10.02/3.86  tff(c_5732, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5709, c_4446])).
% 10.02/3.86  tff(c_5739, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5709, c_5709, c_14])).
% 10.02/3.86  tff(c_5869, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5739, c_4388])).
% 10.02/3.86  tff(c_5871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5732, c_5869])).
% 10.02/3.86  tff(c_5873, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5544])).
% 10.02/3.86  tff(c_5380, plain, (![B_382, A_383, C_384]: (k1_xboole_0=B_382 | k1_relset_1(A_383, B_382, C_384)=A_383 | ~v1_funct_2(C_384, A_383, B_382) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_383, B_382))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.02/3.86  tff(c_5383, plain, (![C_384]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_384)='#skF_2' | ~v1_funct_2(C_384, '#skF_2', '#skF_3') | ~m1_subset_1(C_384, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_5380])).
% 10.02/3.86  tff(c_6046, plain, (![C_431]: (k1_relset_1('#skF_2', '#skF_3', C_431)='#skF_2' | ~v1_funct_2(C_431, '#skF_2', '#skF_3') | ~m1_subset_1(C_431, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_5873, c_5383])).
% 10.02/3.86  tff(c_6049, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_4398, c_6046])).
% 10.02/3.86  tff(c_6056, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4879, c_6049])).
% 10.02/3.86  tff(c_6065, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6056, c_5013])).
% 10.02/3.86  tff(c_6068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5062, c_6065])).
% 10.02/3.86  tff(c_6069, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_4986])).
% 10.02/3.86  tff(c_6073, plain, (v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6069, c_22])).
% 10.02/3.86  tff(c_6080, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_6073])).
% 10.02/3.86  tff(c_6085, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6080, c_26])).
% 10.02/3.86  tff(c_6088, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_6085])).
% 10.02/3.86  tff(c_6252, plain, (![A_437, B_438, C_439, D_440]: (k2_partfun1(A_437, B_438, C_439, D_440)=k7_relat_1(C_439, D_440) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))) | ~v1_funct_1(C_439))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.02/3.86  tff(c_6266, plain, (![C_441, D_442]: (k2_partfun1('#skF_2', '#skF_3', C_441, D_442)=k7_relat_1(C_441, D_442) | ~m1_subset_1(C_441, k1_zfmisc_1('#skF_5')) | ~v1_funct_1(C_441))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_6252])).
% 10.02/3.86  tff(c_6268, plain, (![D_442]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_442)=k7_relat_1('#skF_5', D_442) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_4398, c_6266])).
% 10.02/3.86  tff(c_6274, plain, (![D_442]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_442)=k7_relat_1('#skF_5', D_442))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6268])).
% 10.02/3.86  tff(c_6288, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_52])).
% 10.02/3.86  tff(c_6289, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6088, c_6288])).
% 10.02/3.86  tff(c_8531, plain, (![A_600, B_601, C_602]: (r2_relset_1(A_600, B_601, C_602, C_602) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))) | ~v1_funct_2(C_602, A_600, B_601) | ~v1_funct_1(C_602) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))) | ~v1_funct_2(C_602, A_600, B_601) | ~v1_funct_1(C_602))), inference(reflexivity, [status(thm), theory('equality')], [c_48])).
% 10.02/3.86  tff(c_14445, plain, (![A_928, B_929, A_930]: (r2_relset_1(A_928, B_929, A_930, A_930) | ~m1_subset_1(A_930, k1_zfmisc_1(k2_zfmisc_1(A_928, B_929))) | ~v1_funct_2(A_930, A_928, B_929) | ~v1_funct_1(A_930) | ~r1_tarski(A_930, k2_zfmisc_1(A_928, B_929)))), inference(resolution, [status(thm)], [c_20, c_8531])).
% 10.02/3.86  tff(c_14447, plain, (![A_930]: (r2_relset_1('#skF_2', '#skF_3', A_930, A_930) | ~m1_subset_1(A_930, k1_zfmisc_1('#skF_5')) | ~v1_funct_2(A_930, '#skF_2', '#skF_3') | ~v1_funct_1(A_930) | ~r1_tarski(A_930, k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_14445])).
% 10.02/3.86  tff(c_14512, plain, (![A_934]: (r2_relset_1('#skF_2', '#skF_3', A_934, A_934) | ~m1_subset_1(A_934, k1_zfmisc_1('#skF_5')) | ~v1_funct_2(A_934, '#skF_2', '#skF_3') | ~v1_funct_1(A_934) | ~r1_tarski(A_934, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4388, c_14447])).
% 10.02/3.86  tff(c_14514, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_4398, c_14512])).
% 10.02/3.86  tff(c_14520, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_60, c_58, c_14514])).
% 10.02/3.86  tff(c_14522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6289, c_14520])).
% 10.02/3.86  tff(c_14524, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4409])).
% 10.02/3.86  tff(c_14523, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4409])).
% 10.02/3.86  tff(c_14569, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14524, c_14524, c_14523])).
% 10.02/3.86  tff(c_14570, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_14569])).
% 10.02/3.86  tff(c_14579, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14570, c_58])).
% 10.02/3.86  tff(c_14580, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14570, c_60])).
% 10.02/3.86  tff(c_14533, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_14524, c_10])).
% 10.02/3.86  tff(c_14572, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_14570, c_14533])).
% 10.02/3.86  tff(c_16677, plain, (![A_1143, B_1144, C_1145]: (r2_relset_1(A_1143, B_1144, C_1145, C_1145) | ~m1_subset_1(C_1145, k1_zfmisc_1(k2_zfmisc_1(A_1143, B_1144))) | ~v1_funct_2(C_1145, A_1143, B_1144) | ~v1_funct_1(C_1145) | ~m1_subset_1(C_1145, k1_zfmisc_1(k2_zfmisc_1(A_1143, B_1144))) | ~v1_funct_2(C_1145, A_1143, B_1144) | ~v1_funct_1(C_1145))), inference(reflexivity, [status(thm), theory('equality')], [c_48])).
% 10.02/3.86  tff(c_18138, plain, (![A_1284, B_1285, A_1286]: (r2_relset_1(A_1284, B_1285, A_1286, A_1286) | ~m1_subset_1(A_1286, k1_zfmisc_1(k2_zfmisc_1(A_1284, B_1285))) | ~v1_funct_2(A_1286, A_1284, B_1285) | ~v1_funct_1(A_1286) | ~r1_tarski(A_1286, k2_zfmisc_1(A_1284, B_1285)))), inference(resolution, [status(thm)], [c_20, c_16677])).
% 10.02/3.86  tff(c_18173, plain, (![A_1291, B_1292, A_1293]: (r2_relset_1(A_1291, B_1292, A_1293, A_1293) | ~v1_funct_2(A_1293, A_1291, B_1292) | ~v1_funct_1(A_1293) | ~r1_tarski(A_1293, k2_zfmisc_1(A_1291, B_1292)))), inference(resolution, [status(thm)], [c_20, c_18138])).
% 10.02/3.86  tff(c_18209, plain, (![A_1291, B_1292]: (r2_relset_1(A_1291, B_1292, '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', A_1291, B_1292) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14572, c_18173])).
% 10.02/3.86  tff(c_18240, plain, (![A_1294, B_1295]: (r2_relset_1(A_1294, B_1295, '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', A_1294, B_1295))), inference(demodulation, [status(thm), theory('equality')], [c_14580, c_18209])).
% 10.02/3.86  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.02/3.86  tff(c_164, plain, (![C_56]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_112])).
% 10.02/3.86  tff(c_170, plain, (![A_57]: (v1_relat_1(A_57) | ~r1_tarski(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_164])).
% 10.02/3.86  tff(c_184, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_170])).
% 10.02/3.86  tff(c_145, plain, (![A_55]: (k1_xboole_0=A_55 | ~r1_tarski(A_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_126])).
% 10.02/3.86  tff(c_158, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_145])).
% 10.02/3.86  tff(c_202, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_184, c_158])).
% 10.02/3.86  tff(c_14525, plain, (![A_15]: (k7_relat_1('#skF_5', A_15)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14524, c_14524, c_202])).
% 10.02/3.86  tff(c_14571, plain, (![A_15]: (k7_relat_1('#skF_3', A_15)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14570, c_14570, c_14525])).
% 10.02/3.86  tff(c_14575, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14570, c_14570, c_4398])).
% 10.02/3.86  tff(c_14531, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14524, c_14524, c_14])).
% 10.02/3.86  tff(c_14615, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14570, c_14570, c_14531])).
% 10.02/3.86  tff(c_15422, plain, (![A_1027, B_1028, C_1029, D_1030]: (k2_partfun1(A_1027, B_1028, C_1029, D_1030)=k7_relat_1(C_1029, D_1030) | ~m1_subset_1(C_1029, k1_zfmisc_1(k2_zfmisc_1(A_1027, B_1028))) | ~v1_funct_1(C_1029))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.02/3.86  tff(c_16357, plain, (![A_1114, C_1115, D_1116]: (k2_partfun1(A_1114, '#skF_3', C_1115, D_1116)=k7_relat_1(C_1115, D_1116) | ~m1_subset_1(C_1115, k1_zfmisc_1('#skF_3')) | ~v1_funct_1(C_1115))), inference(superposition, [status(thm), theory('equality')], [c_14615, c_15422])).
% 10.02/3.86  tff(c_16359, plain, (![A_1114, D_1116]: (k2_partfun1(A_1114, '#skF_3', '#skF_3', D_1116)=k7_relat_1('#skF_3', D_1116) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14575, c_16357])).
% 10.02/3.86  tff(c_16365, plain, (![A_1114, D_1116]: (k2_partfun1(A_1114, '#skF_3', '#skF_3', D_1116)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14580, c_14571, c_16359])).
% 10.02/3.86  tff(c_14578, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14570, c_14570, c_52])).
% 10.02/3.86  tff(c_16367, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16365, c_14578])).
% 10.02/3.86  tff(c_18243, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18240, c_16367])).
% 10.02/3.86  tff(c_18247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14579, c_18243])).
% 10.02/3.86  tff(c_18248, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_14569])).
% 10.02/3.86  tff(c_18263, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_18248, c_14533])).
% 10.02/3.86  tff(c_18550, plain, (![A_1322, B_1323, C_1324]: (k1_relset_1(A_1322, B_1323, C_1324)=k1_relat_1(C_1324) | ~m1_subset_1(C_1324, k1_zfmisc_1(k2_zfmisc_1(A_1322, B_1323))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.02/3.86  tff(c_18742, plain, (![A_1350, B_1351, A_1352]: (k1_relset_1(A_1350, B_1351, A_1352)=k1_relat_1(A_1352) | ~r1_tarski(A_1352, k2_zfmisc_1(A_1350, B_1351)))), inference(resolution, [status(thm)], [c_20, c_18550])).
% 10.02/3.86  tff(c_18770, plain, (![A_1350, B_1351]: (k1_relset_1(A_1350, B_1351, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_18263, c_18742])).
% 10.02/3.86  tff(c_18266, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18248, c_18248, c_4398])).
% 10.02/3.86  tff(c_18264, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18248, c_14524])).
% 10.02/3.86  tff(c_38, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.02/3.86  tff(c_61, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 10.02/3.86  tff(c_18803, plain, (![C_1357, B_1358]: (v1_funct_2(C_1357, '#skF_2', B_1358) | k1_relset_1('#skF_2', B_1358, C_1357)!='#skF_2' | ~m1_subset_1(C_1357, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18264, c_18264, c_18264, c_18264, c_61])).
% 10.02/3.86  tff(c_18805, plain, (![B_1358]: (v1_funct_2('#skF_2', '#skF_2', B_1358) | k1_relset_1('#skF_2', B_1358, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_18266, c_18803])).
% 10.02/3.86  tff(c_18810, plain, (![B_1358]: (v1_funct_2('#skF_2', '#skF_2', B_1358) | k1_relat_1('#skF_2')!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18770, c_18805])).
% 10.02/3.86  tff(c_18812, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(splitLeft, [status(thm)], [c_18810])).
% 10.02/3.86  tff(c_18270, plain, (v1_funct_2('#skF_2', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18248, c_58])).
% 10.02/3.86  tff(c_42, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.02/3.86  tff(c_62, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_42])).
% 10.02/3.86  tff(c_18926, plain, (![B_1375, C_1376]: (k1_relset_1('#skF_2', B_1375, C_1376)='#skF_2' | ~v1_funct_2(C_1376, '#skF_2', B_1375) | ~m1_subset_1(C_1376, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18264, c_18264, c_18264, c_18264, c_62])).
% 10.02/3.86  tff(c_18933, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_18270, c_18926])).
% 10.02/3.86  tff(c_18942, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18266, c_18770, c_18933])).
% 10.02/3.86  tff(c_18944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18812, c_18942])).
% 10.02/3.86  tff(c_18945, plain, (![B_1358]: (v1_funct_2('#skF_2', '#skF_2', B_1358))), inference(splitRight, [status(thm)], [c_18810])).
% 10.02/3.86  tff(c_18271, plain, (v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18248, c_60])).
% 10.02/3.86  tff(c_20235, plain, (![A_1493, B_1494, C_1495]: (r2_relset_1(A_1493, B_1494, C_1495, C_1495) | ~m1_subset_1(C_1495, k1_zfmisc_1(k2_zfmisc_1(A_1493, B_1494))) | ~v1_funct_2(C_1495, A_1493, B_1494) | ~v1_funct_1(C_1495) | ~m1_subset_1(C_1495, k1_zfmisc_1(k2_zfmisc_1(A_1493, B_1494))) | ~v1_funct_2(C_1495, A_1493, B_1494) | ~v1_funct_1(C_1495))), inference(reflexivity, [status(thm), theory('equality')], [c_48])).
% 10.02/3.86  tff(c_22386, plain, (![A_1671, B_1672, A_1673]: (r2_relset_1(A_1671, B_1672, A_1673, A_1673) | ~m1_subset_1(A_1673, k1_zfmisc_1(k2_zfmisc_1(A_1671, B_1672))) | ~v1_funct_2(A_1673, A_1671, B_1672) | ~v1_funct_1(A_1673) | ~r1_tarski(A_1673, k2_zfmisc_1(A_1671, B_1672)))), inference(resolution, [status(thm)], [c_20, c_20235])).
% 10.02/3.86  tff(c_22397, plain, (![A_1674, B_1675, A_1676]: (r2_relset_1(A_1674, B_1675, A_1676, A_1676) | ~v1_funct_2(A_1676, A_1674, B_1675) | ~v1_funct_1(A_1676) | ~r1_tarski(A_1676, k2_zfmisc_1(A_1674, B_1675)))), inference(resolution, [status(thm)], [c_20, c_22386])).
% 10.02/3.86  tff(c_22430, plain, (![A_1674, B_1675]: (r2_relset_1(A_1674, B_1675, '#skF_2', '#skF_2') | ~v1_funct_2('#skF_2', A_1674, B_1675) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_18263, c_22397])).
% 10.02/3.86  tff(c_22460, plain, (![A_1677, B_1678]: (r2_relset_1(A_1677, B_1678, '#skF_2', '#skF_2') | ~v1_funct_2('#skF_2', A_1677, B_1678))), inference(demodulation, [status(thm), theory('equality')], [c_18271, c_22430])).
% 10.02/3.86  tff(c_18262, plain, (![A_15]: (k7_relat_1('#skF_2', A_15)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18248, c_18248, c_14525])).
% 10.02/3.86  tff(c_19097, plain, (![A_1385, B_1386, C_1387, D_1388]: (k2_partfun1(A_1385, B_1386, C_1387, D_1388)=k7_relat_1(C_1387, D_1388) | ~m1_subset_1(C_1387, k1_zfmisc_1(k2_zfmisc_1(A_1385, B_1386))) | ~v1_funct_1(C_1387))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.02/3.86  tff(c_19953, plain, (![A_1461, B_1462, A_1463, D_1464]: (k2_partfun1(A_1461, B_1462, A_1463, D_1464)=k7_relat_1(A_1463, D_1464) | ~v1_funct_1(A_1463) | ~r1_tarski(A_1463, k2_zfmisc_1(A_1461, B_1462)))), inference(resolution, [status(thm)], [c_20, c_19097])).
% 10.02/3.86  tff(c_19971, plain, (![A_1461, B_1462, D_1464]: (k2_partfun1(A_1461, B_1462, '#skF_2', D_1464)=k7_relat_1('#skF_2', D_1464) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_18263, c_19953])).
% 10.02/3.86  tff(c_19989, plain, (![A_1461, B_1462, D_1464]: (k2_partfun1(A_1461, B_1462, '#skF_2', D_1464)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18271, c_18262, c_19971])).
% 10.02/3.86  tff(c_18269, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18248, c_18248, c_52])).
% 10.02/3.86  tff(c_19995, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19989, c_18269])).
% 10.02/3.86  tff(c_22463, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22460, c_19995])).
% 10.02/3.86  tff(c_22467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18945, c_22463])).
% 10.02/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.02/3.86  
% 10.02/3.86  Inference rules
% 10.02/3.86  ----------------------
% 10.02/3.86  #Ref     : 4
% 10.02/3.86  #Sup     : 4651
% 10.02/3.86  #Fact    : 0
% 10.02/3.86  #Define  : 0
% 10.02/3.86  #Split   : 53
% 10.02/3.86  #Chain   : 0
% 10.02/3.86  #Close   : 0
% 10.02/3.86  
% 10.02/3.86  Ordering : KBO
% 10.02/3.86  
% 10.02/3.86  Simplification rules
% 10.02/3.86  ----------------------
% 10.02/3.86  #Subsume      : 1548
% 10.02/3.86  #Demod        : 5158
% 10.02/3.86  #Tautology    : 1634
% 10.02/3.86  #SimpNegUnit  : 96
% 10.02/3.86  #BackRed      : 237
% 10.02/3.86  
% 10.02/3.86  #Partial instantiations: 0
% 10.02/3.86  #Strategies tried      : 1
% 10.02/3.86  
% 10.02/3.86  Timing (in seconds)
% 10.02/3.86  ----------------------
% 10.02/3.86  Preprocessing        : 0.36
% 10.02/3.86  Parsing              : 0.19
% 10.02/3.86  CNF conversion       : 0.02
% 10.02/3.86  Main loop            : 2.68
% 10.02/3.86  Inferencing          : 0.79
% 10.02/3.86  Reduction            : 1.00
% 10.02/3.86  Demodulation         : 0.72
% 10.02/3.86  BG Simplification    : 0.09
% 10.02/3.86  Subsumption          : 0.62
% 10.02/3.86  Abstraction          : 0.12
% 10.02/3.86  MUC search           : 0.00
% 10.02/3.86  Cooper               : 0.00
% 10.02/3.86  Total                : 3.12
% 10.02/3.86  Index Insertion      : 0.00
% 10.02/3.86  Index Deletion       : 0.00
% 10.02/3.86  Index Matching       : 0.00
% 10.02/3.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
