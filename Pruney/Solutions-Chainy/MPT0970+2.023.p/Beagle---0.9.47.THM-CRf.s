%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:22 EST 2020

% Result     : Theorem 12.78s
% Output     : CNFRefutation 13.17s
% Verified   : 
% Statistics : Number of formulae       :  352 (5887 expanded)
%              Number of leaves         :   37 (2018 expanded)
%              Depth                    :   17
%              Number of atoms          :  653 (18895 expanded)
%              Number of equality atoms :  223 (7348 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_164,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_173,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_164])).

tff(c_62,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_184,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_62])).

tff(c_245,plain,(
    ! [A_123,B_124,C_125] :
      ( m1_subset_1(k2_relset_1(A_123,B_124,C_125),k1_zfmisc_1(B_124))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_266,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_245])).

tff(c_272,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_266])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_276,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_272,c_14])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_280,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_276,c_8])).

tff(c_284,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_280])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_83,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,B_76)
      | ~ m1_subset_1(A_75,k1_zfmisc_1(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_83])).

tff(c_72,plain,(
    ! [D_72] :
      ( r2_hidden('#skF_9'(D_72),'#skF_6')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_144,plain,(
    ! [C_95,B_96,A_97] :
      ( r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [D_98,B_99] :
      ( r2_hidden('#skF_9'(D_98),B_99)
      | ~ r1_tarski('#skF_6',B_99)
      | ~ r2_hidden(D_98,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_144])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_193,plain,(
    ! [D_109,B_110,B_111] :
      ( r2_hidden('#skF_9'(D_109),B_110)
      | ~ r1_tarski(B_111,B_110)
      | ~ r1_tarski('#skF_6',B_111)
      | ~ r2_hidden(D_109,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_198,plain,(
    ! [D_109] :
      ( r2_hidden('#skF_9'(D_109),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski('#skF_6','#skF_8')
      | ~ r2_hidden(D_109,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_87,c_193])).

tff(c_285,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_174,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_183,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_174])).

tff(c_8490,plain,(
    ! [B_985,A_986,C_987] :
      ( k1_xboole_0 = B_985
      | k1_relset_1(A_986,B_985,C_987) = A_986
      | ~ v1_funct_2(C_987,A_986,B_985)
      | ~ m1_subset_1(C_987,k1_zfmisc_1(k2_zfmisc_1(A_986,B_985))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8501,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_8490])).

tff(c_8506,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_183,c_8501])).

tff(c_8521,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8506])).

tff(c_150,plain,(
    ! [D_72,B_96] :
      ( r2_hidden('#skF_9'(D_72),B_96)
      | ~ r1_tarski('#skF_6',B_96)
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_144])).

tff(c_104,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_113,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_104])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_70,plain,(
    ! [D_72] :
      ( k1_funct_1('#skF_8','#skF_9'(D_72)) = D_72
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_301,plain,(
    ! [A_130,D_131] :
      ( r2_hidden(k1_funct_1(A_130,D_131),k2_relat_1(A_130))
      | ~ r2_hidden(D_131,k1_relat_1(A_130))
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_306,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_301])).

tff(c_369,plain,(
    ! [D_140] :
      ( r2_hidden(D_140,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_140),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_140,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_68,c_306])).

tff(c_374,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_150,c_369])).

tff(c_375,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_8523,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8521,c_375])).

tff(c_8528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8523])).

tff(c_8529,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8506])).

tff(c_7479,plain,(
    ! [B_909,A_910,C_911] :
      ( k1_xboole_0 = B_909
      | k1_relset_1(A_910,B_909,C_911) = A_910
      | ~ v1_funct_2(C_911,A_910,B_909)
      | ~ m1_subset_1(C_911,k1_zfmisc_1(k2_zfmisc_1(A_910,B_909))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7494,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_7479])).

tff(c_7500,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_183,c_7494])).

tff(c_7501,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7500])).

tff(c_7503,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7501,c_375])).

tff(c_7508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7503])).

tff(c_7510,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7500])).

tff(c_7509,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7500])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3658,plain,(
    ! [C_550,A_551] :
      ( k1_xboole_0 = C_550
      | ~ v1_funct_2(C_550,A_551,k1_xboole_0)
      | k1_xboole_0 = A_551
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_551,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3668,plain,(
    ! [A_8,A_551] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_551,k1_xboole_0)
      | k1_xboole_0 = A_551
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_551,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3658])).

tff(c_7713,plain,(
    ! [A_940,A_941] :
      ( A_940 = '#skF_7'
      | ~ v1_funct_2(A_940,A_941,'#skF_7')
      | A_941 = '#skF_7'
      | ~ r1_tarski(A_940,k2_zfmisc_1(A_941,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7509,c_7509,c_7509,c_7509,c_3668])).

tff(c_7731,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_7713])).

tff(c_7742,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_7731])).

tff(c_7744,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7742])).

tff(c_7800,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7744,c_66])).

tff(c_7791,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7744,c_183])).

tff(c_7798,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7744,c_87])).

tff(c_3832,plain,(
    ! [B_572,C_573] :
      ( k1_relset_1(k1_xboole_0,B_572,C_573) = k1_xboole_0
      | ~ v1_funct_2(C_573,k1_xboole_0,B_572)
      | ~ m1_subset_1(C_573,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_572))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3842,plain,(
    ! [B_572,A_8] :
      ( k1_relset_1(k1_xboole_0,B_572,A_8) = k1_xboole_0
      | ~ v1_funct_2(A_8,k1_xboole_0,B_572)
      | ~ r1_tarski(A_8,k2_zfmisc_1(k1_xboole_0,B_572)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3832])).

tff(c_7520,plain,(
    ! [B_572,A_8] :
      ( k1_relset_1('#skF_7',B_572,A_8) = '#skF_7'
      | ~ v1_funct_2(A_8,'#skF_7',B_572)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_7',B_572)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7509,c_7509,c_7509,c_7509,c_3842])).

tff(c_8187,plain,(
    ! [B_976,A_977] :
      ( k1_relset_1('#skF_6',B_976,A_977) = '#skF_6'
      | ~ v1_funct_2(A_977,'#skF_6',B_976)
      | ~ r1_tarski(A_977,k2_zfmisc_1('#skF_6',B_976)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7744,c_7744,c_7744,c_7744,c_7520])).

tff(c_8193,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_7798,c_8187])).

tff(c_8213,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7800,c_7791,c_8193])).

tff(c_8215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7510,c_8213])).

tff(c_8216,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_7742])).

tff(c_2751,plain,(
    ! [B_461,A_462,C_463] :
      ( k1_xboole_0 = B_461
      | k1_relset_1(A_462,B_461,C_463) = A_462
      | ~ v1_funct_2(C_463,A_462,B_461)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(k2_zfmisc_1(A_462,B_461))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2766,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_2751])).

tff(c_2773,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_183,c_2766])).

tff(c_2774,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2773])).

tff(c_2775,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_375])).

tff(c_2780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2775])).

tff(c_2782,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2773])).

tff(c_2781,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2773])).

tff(c_2079,plain,(
    ! [C_358,A_359] :
      ( k1_xboole_0 = C_358
      | ~ v1_funct_2(C_358,A_359,k1_xboole_0)
      | k1_xboole_0 = A_359
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2089,plain,(
    ! [A_8,A_359] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_359,k1_xboole_0)
      | k1_xboole_0 = A_359
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_359,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2079])).

tff(c_3009,plain,(
    ! [A_494,A_495] :
      ( A_494 = '#skF_7'
      | ~ v1_funct_2(A_494,A_495,'#skF_7')
      | A_495 = '#skF_7'
      | ~ r1_tarski(A_494,k2_zfmisc_1(A_495,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2781,c_2781,c_2781,c_2781,c_2089])).

tff(c_3027,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_3009])).

tff(c_3038,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3027])).

tff(c_3040,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3038])).

tff(c_3105,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3040,c_66])).

tff(c_3096,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3040,c_183])).

tff(c_3103,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3040,c_87])).

tff(c_2123,plain,(
    ! [B_367,C_368] :
      ( k1_relset_1(k1_xboole_0,B_367,C_368) = k1_xboole_0
      | ~ v1_funct_2(C_368,k1_xboole_0,B_367)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2133,plain,(
    ! [B_367,A_8] :
      ( k1_relset_1(k1_xboole_0,B_367,A_8) = k1_xboole_0
      | ~ v1_funct_2(A_8,k1_xboole_0,B_367)
      | ~ r1_tarski(A_8,k2_zfmisc_1(k1_xboole_0,B_367)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2123])).

tff(c_2787,plain,(
    ! [B_367,A_8] :
      ( k1_relset_1('#skF_7',B_367,A_8) = '#skF_7'
      | ~ v1_funct_2(A_8,'#skF_7',B_367)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_7',B_367)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2781,c_2781,c_2781,c_2781,c_2133])).

tff(c_3563,plain,(
    ! [B_542,A_543] :
      ( k1_relset_1('#skF_6',B_542,A_543) = '#skF_6'
      | ~ v1_funct_2(A_543,'#skF_6',B_542)
      | ~ r1_tarski(A_543,k2_zfmisc_1('#skF_6',B_542)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3040,c_3040,c_3040,c_3040,c_2787])).

tff(c_3569,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_3103,c_3563])).

tff(c_3589,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3105,c_3096,c_3569])).

tff(c_3591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2782,c_3589])).

tff(c_3592,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3038])).

tff(c_1133,plain,(
    ! [B_260,A_261,C_262] :
      ( k1_xboole_0 = B_260
      | k1_relset_1(A_261,B_260,C_262) = A_261
      | ~ v1_funct_2(C_262,A_261,B_260)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_261,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1148,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_1133])).

tff(c_1155,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_183,c_1148])).

tff(c_1156,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1155])).

tff(c_1157,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_375])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1157])).

tff(c_1164,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1155])).

tff(c_1163,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1155])).

tff(c_378,plain,(
    ! [C_143,A_144] :
      ( k1_xboole_0 = C_143
      | ~ v1_funct_2(C_143,A_144,k1_xboole_0)
      | k1_xboole_0 = A_144
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_388,plain,(
    ! [A_8,A_144] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_144,k1_xboole_0)
      | k1_xboole_0 = A_144
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_144,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_378])).

tff(c_1318,plain,(
    ! [A_288,A_289] :
      ( A_288 = '#skF_7'
      | ~ v1_funct_2(A_288,A_289,'#skF_7')
      | A_289 = '#skF_7'
      | ~ r1_tarski(A_288,k2_zfmisc_1(A_289,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_1163,c_1163,c_1163,c_388])).

tff(c_1336,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_1318])).

tff(c_1347,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1336])).

tff(c_1349,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1347])).

tff(c_1398,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_66])).

tff(c_1389,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_183])).

tff(c_1396,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_87])).

tff(c_477,plain,(
    ! [B_165,C_166] :
      ( k1_relset_1(k1_xboole_0,B_165,C_166) = k1_xboole_0
      | ~ v1_funct_2(C_166,k1_xboole_0,B_165)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_487,plain,(
    ! [B_165,A_8] :
      ( k1_relset_1(k1_xboole_0,B_165,A_8) = k1_xboole_0
      | ~ v1_funct_2(A_8,k1_xboole_0,B_165)
      | ~ r1_tarski(A_8,k2_zfmisc_1(k1_xboole_0,B_165)) ) ),
    inference(resolution,[status(thm)],[c_16,c_477])).

tff(c_1167,plain,(
    ! [B_165,A_8] :
      ( k1_relset_1('#skF_7',B_165,A_8) = '#skF_7'
      | ~ v1_funct_2(A_8,'#skF_7',B_165)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_7',B_165)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_1163,c_1163,c_1163,c_487])).

tff(c_1977,plain,(
    ! [B_351,A_352] :
      ( k1_relset_1('#skF_6',B_351,A_352) = '#skF_6'
      | ~ v1_funct_2(A_352,'#skF_6',B_351)
      | ~ r1_tarski(A_352,k2_zfmisc_1('#skF_6',B_351)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_1349,c_1349,c_1349,c_1167])).

tff(c_1983,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1396,c_1977])).

tff(c_2003,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1389,c_1983])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1164,c_2003])).

tff(c_2006,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1347])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_309,plain,(
    ! [D_131] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_131),k1_xboole_0)
      | ~ r2_hidden(D_131,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_301])).

tff(c_313,plain,(
    ! [D_131] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_131),k1_xboole_0)
      | ~ r2_hidden(D_131,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_309])).

tff(c_377,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_1175,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_377])).

tff(c_2034,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2006,c_1175])).

tff(c_2074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2034])).

tff(c_2075,plain,(
    ! [D_131] :
      ( ~ v1_funct_1(k1_xboole_0)
      | r2_hidden(k1_funct_1(k1_xboole_0,D_131),k1_xboole_0)
      | ~ r2_hidden(D_131,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_2077,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2075])).

tff(c_2793,plain,(
    ~ v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2781,c_2077])).

tff(c_3605,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3592,c_2793])).

tff(c_3646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3605])).

tff(c_3649,plain,(
    ! [D_544] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_544),k1_xboole_0)
      | ~ r2_hidden(D_544,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_2075])).

tff(c_3654,plain,(
    ! [D_548,B_549] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_548),B_549)
      | ~ r1_tarski(k1_xboole_0,B_549)
      | ~ r2_hidden(D_548,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3649,c_2])).

tff(c_7250,plain,(
    ! [D_872,B_873,B_874] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_872),B_873)
      | ~ r1_tarski(B_874,B_873)
      | ~ r1_tarski(k1_xboole_0,B_874)
      | ~ r2_hidden(D_872,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3654,c_2])).

tff(c_7273,plain,(
    ! [D_872] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_872),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski(k1_xboole_0,'#skF_8')
      | ~ r2_hidden(D_872,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_87,c_7250])).

tff(c_7275,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_7273])).

tff(c_7514,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7509,c_7275])).

tff(c_8233,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8216,c_7514])).

tff(c_8275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8233])).

tff(c_8277,plain,(
    r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_7273])).

tff(c_8538,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8529,c_8277])).

tff(c_155,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(A_100,B_102)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_3686,plain,(
    ! [A_555,B_556,B_557,B_558] :
      ( r2_hidden('#skF_1'(A_555,B_556),B_557)
      | ~ r1_tarski(B_558,B_557)
      | ~ r1_tarski(A_555,B_558)
      | r1_tarski(A_555,B_556) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_3749,plain,(
    ! [A_565,B_566] :
      ( r2_hidden('#skF_1'(A_565,B_566),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski(A_565,'#skF_8')
      | r1_tarski(A_565,B_566) ) ),
    inference(resolution,[status(thm)],[c_87,c_3686])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3757,plain,(
    ! [A_565] :
      ( ~ r1_tarski(A_565,'#skF_8')
      | r1_tarski(A_565,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_3749,c_4])).

tff(c_240,plain,(
    ! [A_122] :
      ( v1_funct_2(k1_xboole_0,A_122,k1_xboole_0)
      | k1_xboole_0 = A_122
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_122,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_244,plain,(
    ! [A_122] :
      ( v1_funct_2(k1_xboole_0,A_122,k1_xboole_0)
      | k1_xboole_0 = A_122
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_122,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_240])).

tff(c_8832,plain,(
    ! [A_1005] :
      ( v1_funct_2('#skF_7',A_1005,'#skF_7')
      | A_1005 = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_1005,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8529,c_8529,c_8529,c_8529,c_8529,c_244])).

tff(c_8839,plain,
    ( v1_funct_2('#skF_7','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_3757,c_8832])).

tff(c_8843,plain,
    ( v1_funct_2('#skF_7','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8538,c_8839])).

tff(c_8844,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8843])).

tff(c_154,plain,(
    ! [D_98,B_2,B_99] :
      ( r2_hidden('#skF_9'(D_98),B_2)
      | ~ r1_tarski(B_99,B_2)
      | ~ r1_tarski('#skF_6',B_99)
      | ~ r2_hidden(D_98,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_8305,plain,(
    ! [D_98] :
      ( r2_hidden('#skF_9'(D_98),'#skF_8')
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_98,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8277,c_154])).

tff(c_8634,plain,(
    ! [D_98] :
      ( r2_hidden('#skF_9'(D_98),'#skF_8')
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ r2_hidden(D_98,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8529,c_8305])).

tff(c_8635,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_8634])).

tff(c_8858,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8844,c_8635])).

tff(c_8900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8858])).

tff(c_8902,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8843])).

tff(c_9410,plain,(
    ! [A_1057,A_1058] :
      ( A_1057 = '#skF_7'
      | ~ v1_funct_2(A_1057,A_1058,'#skF_7')
      | A_1058 = '#skF_7'
      | ~ r1_tarski(A_1057,k2_zfmisc_1(A_1058,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8529,c_8529,c_8529,c_8529,c_3668])).

tff(c_9430,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_9410])).

tff(c_9450,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9430])).

tff(c_9451,plain,(
    '#skF_7' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_8902,c_9450])).

tff(c_8306,plain,
    ( k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8277,c_8])).

tff(c_8307,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8306])).

tff(c_8536,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8529,c_8307])).

tff(c_9497,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9451,c_8536])).

tff(c_9542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9497])).

tff(c_9544,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_8634])).

tff(c_162,plain,(
    ! [A_100,B_101,B_2,B_102] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_2)
      | ~ r1_tarski(B_102,B_2)
      | ~ r1_tarski(A_100,B_102)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_9914,plain,(
    ! [A_1094,B_1095] :
      ( r2_hidden('#skF_1'(A_1094,B_1095),'#skF_8')
      | ~ r1_tarski(A_1094,'#skF_7')
      | r1_tarski(A_1094,B_1095) ) ),
    inference(resolution,[status(thm)],[c_8538,c_162])).

tff(c_9923,plain,(
    ! [A_1096] :
      ( ~ r1_tarski(A_1096,'#skF_7')
      | r1_tarski(A_1096,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9914,c_4])).

tff(c_9926,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_9544,c_9923])).

tff(c_9951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_9926])).

tff(c_9952,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8306])).

tff(c_9974,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9952,c_9952,c_18])).

tff(c_9996,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9974,c_184])).

tff(c_9975,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9952,c_9952,c_20])).

tff(c_10019,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9975,c_183])).

tff(c_58,plain,(
    ! [B_63,A_62,C_64] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_62,B_63,C_64) = A_62
      | ~ v1_funct_2(C_64,A_62,B_63)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10139,plain,(
    ! [B_1107,A_1108,C_1109] :
      ( B_1107 = '#skF_8'
      | k1_relset_1(A_1108,B_1107,C_1109) = A_1108
      | ~ v1_funct_2(C_1109,A_1108,B_1107)
      | ~ m1_subset_1(C_1109,k1_zfmisc_1(k2_zfmisc_1(A_1108,B_1107))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9952,c_58])).

tff(c_10150,plain,
    ( '#skF_7' = '#skF_8'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_10139])).

tff(c_10155,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10019,c_10150])).

tff(c_10156,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_9996,c_10155])).

tff(c_10171,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10156,c_285])).

tff(c_10181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10171])).

tff(c_10192,plain,(
    ! [D_1110] :
      ( r2_hidden(D_1110,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1110,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_10207,plain,(
    ! [A_1115] :
      ( r1_tarski(A_1115,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_1115,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10192,c_4])).

tff(c_10215,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_10207])).

tff(c_10220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_284,c_10215])).

tff(c_10222,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_21326,plain,(
    ! [B_1954,A_1955,C_1956] :
      ( k1_xboole_0 = B_1954
      | k1_relset_1(A_1955,B_1954,C_1956) = A_1955
      | ~ v1_funct_2(C_1956,A_1955,B_1954)
      | ~ m1_subset_1(C_1956,k1_zfmisc_1(k2_zfmisc_1(A_1955,B_1954))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_21337,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_21326])).

tff(c_21342,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_183,c_21337])).

tff(c_21343,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_21342])).

tff(c_10231,plain,(
    ! [A_1116,D_1117] :
      ( r2_hidden(k1_funct_1(A_1116,D_1117),k2_relat_1(A_1116))
      | ~ r2_hidden(D_1117,k1_relat_1(A_1116))
      | ~ v1_funct_1(A_1116)
      | ~ v1_relat_1(A_1116) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10236,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_10231])).

tff(c_10249,plain,(
    ! [D_1119] :
      ( r2_hidden(D_1119,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_1119),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_1119,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_68,c_10236])).

tff(c_10254,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_150,c_10249])).

tff(c_10269,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_10254])).

tff(c_21346,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21343,c_10269])).

tff(c_21351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_21346])).

tff(c_21353,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_21342])).

tff(c_21352,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_21342])).

tff(c_10270,plain,(
    ! [C_1124,A_1125] :
      ( k1_xboole_0 = C_1124
      | ~ v1_funct_2(C_1124,A_1125,k1_xboole_0)
      | k1_xboole_0 = A_1125
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(k2_zfmisc_1(A_1125,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10280,plain,(
    ! [A_8,A_1125] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_1125,k1_xboole_0)
      | k1_xboole_0 = A_1125
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_1125,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_10270])).

tff(c_23110,plain,(
    ! [A_2070,A_2071] :
      ( A_2070 = '#skF_7'
      | ~ v1_funct_2(A_2070,A_2071,'#skF_7')
      | A_2071 = '#skF_7'
      | ~ r1_tarski(A_2070,k2_zfmisc_1(A_2071,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21352,c_21352,c_21352,c_21352,c_10280])).

tff(c_23133,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_23110])).

tff(c_23151,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23133])).

tff(c_23153,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_23151])).

tff(c_23238,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23153,c_66])).

tff(c_23236,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23153,c_87])).

tff(c_17178,plain,(
    ! [B_1656,C_1657] :
      ( k1_relset_1(k1_xboole_0,B_1656,C_1657) = k1_xboole_0
      | ~ v1_funct_2(C_1657,k1_xboole_0,B_1656)
      | ~ m1_subset_1(C_1657,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_1656))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_17188,plain,(
    ! [B_1656,A_8] :
      ( k1_relset_1(k1_xboole_0,B_1656,A_8) = k1_xboole_0
      | ~ v1_funct_2(A_8,k1_xboole_0,B_1656)
      | ~ r1_tarski(A_8,k2_zfmisc_1(k1_xboole_0,B_1656)) ) ),
    inference(resolution,[status(thm)],[c_16,c_17178])).

tff(c_21359,plain,(
    ! [B_1656,A_8] :
      ( k1_relset_1('#skF_7',B_1656,A_8) = '#skF_7'
      | ~ v1_funct_2(A_8,'#skF_7',B_1656)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_7',B_1656)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21352,c_21352,c_21352,c_21352,c_17188])).

tff(c_23299,plain,(
    ! [B_1656,A_8] :
      ( k1_relset_1('#skF_6',B_1656,A_8) = '#skF_6'
      | ~ v1_funct_2(A_8,'#skF_6',B_1656)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_6',B_1656)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23153,c_23153,c_23153,c_23153,c_21359])).

tff(c_23324,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_23236,c_23299])).

tff(c_23343,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23238,c_23324])).

tff(c_23229,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23153,c_183])).

tff(c_23520,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23343,c_23229])).

tff(c_23521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21353,c_23520])).

tff(c_23522,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_23151])).

tff(c_21807,plain,(
    ! [A_2005,A_2006] :
      ( A_2005 = '#skF_7'
      | ~ v1_funct_2(A_2005,A_2006,'#skF_7')
      | A_2006 = '#skF_7'
      | ~ r1_tarski(A_2005,k2_zfmisc_1(A_2006,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21352,c_21352,c_21352,c_21352,c_10280])).

tff(c_21824,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_21807])).

tff(c_21835,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_21824])).

tff(c_21837,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_21835])).

tff(c_17245,plain,(
    ! [A_1671,B_1672,B_1673,B_1674] :
      ( r2_hidden('#skF_1'(A_1671,B_1672),B_1673)
      | ~ r1_tarski(B_1674,B_1673)
      | ~ r1_tarski(A_1671,B_1674)
      | r1_tarski(A_1671,B_1672) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_17371,plain,(
    ! [A_1684,B_1685] :
      ( r2_hidden('#skF_1'(A_1684,B_1685),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski(A_1684,'#skF_8')
      | r1_tarski(A_1684,B_1685) ) ),
    inference(resolution,[status(thm)],[c_87,c_17245])).

tff(c_17379,plain,(
    ! [A_1684] :
      ( ~ r1_tarski(A_1684,'#skF_8')
      | r1_tarski(A_1684,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_17371,c_4])).

tff(c_21515,plain,(
    ! [A_1966] :
      ( v1_funct_2('#skF_7',A_1966,'#skF_7')
      | A_1966 = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_1966,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21352,c_21352,c_21352,c_21352,c_21352,c_244])).

tff(c_21520,plain,
    ( v1_funct_2('#skF_7','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_17379,c_21515])).

tff(c_21521,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_21520])).

tff(c_21871,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21837,c_21521])).

tff(c_21921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10222,c_21871])).

tff(c_21922,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_21835])).

tff(c_21945,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21922,c_21521])).

tff(c_21995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_21945])).

tff(c_21997,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_21520])).

tff(c_22035,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_21997,c_8])).

tff(c_22054,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22035])).

tff(c_23559,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23522,c_22054])).

tff(c_23616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_23559])).

tff(c_23617,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_22035])).

tff(c_21373,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21352,c_21352,c_18])).

tff(c_23630,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23617,c_23617,c_21373])).

tff(c_10224,plain,(
    ! [D_98] :
      ( r2_hidden('#skF_9'(D_98),'#skF_8')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_98,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10222,c_154])).

tff(c_10245,plain,(
    ! [D_1118] :
      ( r2_hidden('#skF_9'(D_1118),'#skF_8')
      | ~ r2_hidden(D_1118,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10224])).

tff(c_10259,plain,(
    ! [D_1121,B_1122] :
      ( r2_hidden('#skF_9'(D_1121),B_1122)
      | ~ r1_tarski('#skF_8',B_1122)
      | ~ r2_hidden(D_1121,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10245,c_2])).

tff(c_17156,plain,(
    ! [D_1653,B_1654,B_1655] :
      ( r2_hidden('#skF_9'(D_1653),B_1654)
      | ~ r1_tarski(B_1655,B_1654)
      | ~ r1_tarski('#skF_8',B_1655)
      | ~ r2_hidden(D_1653,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10259,c_2])).

tff(c_17172,plain,(
    ! [D_1653] :
      ( r2_hidden('#skF_9'(D_1653),'#skF_7')
      | ~ r1_tarski('#skF_8',k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1653,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_276,c_17156])).

tff(c_17177,plain,(
    ~ r1_tarski('#skF_8',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_17172])).

tff(c_23681,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23630,c_17177])).

tff(c_23685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_23681])).

tff(c_23687,plain,(
    r1_tarski('#skF_8',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_17172])).

tff(c_23913,plain,(
    ! [A_2117,B_2118,B_2119,B_2120] :
      ( r2_hidden('#skF_1'(A_2117,B_2118),B_2119)
      | ~ r1_tarski(B_2120,B_2119)
      | ~ r1_tarski(A_2117,B_2120)
      | r1_tarski(A_2117,B_2118) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_24897,plain,(
    ! [A_2212,B_2213] :
      ( r2_hidden('#skF_1'(A_2212,B_2213),k2_relat_1('#skF_8'))
      | ~ r1_tarski(A_2212,'#skF_8')
      | r1_tarski(A_2212,B_2213) ) ),
    inference(resolution,[status(thm)],[c_23687,c_23913])).

tff(c_24906,plain,(
    ! [A_2214] :
      ( ~ r1_tarski(A_2214,'#skF_8')
      | r1_tarski(A_2214,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_24897,c_4])).

tff(c_281,plain,(
    ! [D_98] :
      ( r2_hidden('#skF_9'(D_98),'#skF_7')
      | ~ r1_tarski('#skF_6',k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_98,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_276,c_154])).

tff(c_10281,plain,(
    ~ r1_tarski('#skF_6',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_24934,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_24906,c_10281])).

tff(c_24956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10222,c_24934])).

tff(c_24958,plain,(
    r1_tarski('#skF_6',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_29464,plain,(
    ! [B_2619,A_2620,C_2621] :
      ( k1_xboole_0 = B_2619
      | k1_relset_1(A_2620,B_2619,C_2621) = A_2620
      | ~ v1_funct_2(C_2621,A_2620,B_2619)
      | ~ m1_subset_1(C_2621,k1_zfmisc_1(k2_zfmisc_1(A_2620,B_2619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_29475,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_29464])).

tff(c_29480,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_183,c_29475])).

tff(c_29481,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_29480])).

tff(c_29486,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29481,c_10269])).

tff(c_29491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_29486])).

tff(c_29492,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_29480])).

tff(c_31142,plain,(
    ! [A_2738,A_2739] :
      ( A_2738 = '#skF_7'
      | ~ v1_funct_2(A_2738,A_2739,'#skF_7')
      | A_2739 = '#skF_7'
      | ~ r1_tarski(A_2738,k2_zfmisc_1(A_2739,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29492,c_29492,c_29492,c_29492,c_10280])).

tff(c_31162,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_31142])).

tff(c_31177,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_31162])).

tff(c_31179,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_31177])).

tff(c_31250,plain,(
    ~ r1_tarski('#skF_6',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31179,c_284])).

tff(c_31270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24958,c_31250])).

tff(c_31271,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_31177])).

tff(c_30214,plain,(
    ! [A_2691,A_2692] :
      ( A_2691 = '#skF_7'
      | ~ v1_funct_2(A_2691,A_2692,'#skF_7')
      | A_2692 = '#skF_7'
      | ~ r1_tarski(A_2691,k2_zfmisc_1(A_2692,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29492,c_29492,c_29492,c_29492,c_10280])).

tff(c_30231,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_30214])).

tff(c_30242,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_30231])).

tff(c_30244,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_30242])).

tff(c_29235,plain,(
    ! [A_2598,B_2599,B_2600,B_2601] :
      ( r2_hidden('#skF_1'(A_2598,B_2599),B_2600)
      | ~ r1_tarski(B_2601,B_2600)
      | ~ r1_tarski(A_2598,B_2601)
      | r1_tarski(A_2598,B_2599) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_29932,plain,(
    ! [A_2669,B_2670] :
      ( r2_hidden('#skF_1'(A_2669,B_2670),'#skF_7')
      | ~ r1_tarski(A_2669,k2_relat_1('#skF_8'))
      | r1_tarski(A_2669,B_2670) ) ),
    inference(resolution,[status(thm)],[c_276,c_29235])).

tff(c_29972,plain,(
    ! [A_2674] :
      ( ~ r1_tarski(A_2674,k2_relat_1('#skF_8'))
      | r1_tarski(A_2674,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_29932,c_4])).

tff(c_29990,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_24958,c_29972])).

tff(c_30012,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_29990,c_8])).

tff(c_30013,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_30012])).

tff(c_30253,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30244,c_30013])).

tff(c_30327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30253])).

tff(c_30328,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_30242])).

tff(c_29283,plain,(
    ! [A_2605,B_2606] :
      ( r2_hidden('#skF_1'(A_2605,B_2606),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski(A_2605,'#skF_8')
      | r1_tarski(A_2605,B_2606) ) ),
    inference(resolution,[status(thm)],[c_87,c_29235])).

tff(c_29291,plain,(
    ! [A_2605] :
      ( ~ r1_tarski(A_2605,'#skF_8')
      | r1_tarski(A_2605,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_29283,c_4])).

tff(c_29680,plain,(
    ! [A_2636] :
      ( v1_funct_2('#skF_7',A_2636,'#skF_7')
      | A_2636 = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_2636,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29492,c_29492,c_29492,c_29492,c_29492,c_244])).

tff(c_29685,plain,
    ( v1_funct_2('#skF_7','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_29291,c_29680])).

tff(c_29686,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_29685])).

tff(c_30386,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30328,c_29686])).

tff(c_30443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30386])).

tff(c_30444,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30012])).

tff(c_30463,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30444,c_29686])).

tff(c_30520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10222,c_30463])).

tff(c_30522,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_29685])).

tff(c_30554,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_30522,c_8])).

tff(c_30573,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_30554])).

tff(c_31300,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31271,c_30573])).

tff(c_31361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_31300])).

tff(c_31362,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_30554])).

tff(c_31459,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31362,c_184])).

tff(c_29514,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29492,c_29492,c_18])).

tff(c_31424,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31362,c_31362,c_29514])).

tff(c_31480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31459,c_31424])).

tff(c_31502,plain,(
    ! [D_2745] :
      ( r2_hidden(D_2745,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_2745,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_10254])).

tff(c_31525,plain,(
    ! [A_2749] :
      ( r1_tarski(A_2749,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_2749,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_31502,c_4])).

tff(c_31533,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_31525])).

tff(c_31538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_284,c_31533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:33:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.78/5.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.78/5.88  
% 12.78/5.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.78/5.88  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 12.78/5.88  
% 12.78/5.88  %Foreground sorts:
% 12.78/5.88  
% 12.78/5.88  
% 12.78/5.88  %Background operators:
% 12.78/5.88  
% 12.78/5.88  
% 12.78/5.88  %Foreground operators:
% 12.78/5.88  tff('#skF_9', type, '#skF_9': $i > $i).
% 12.78/5.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.78/5.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.78/5.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.78/5.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.78/5.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.78/5.88  tff('#skF_7', type, '#skF_7': $i).
% 12.78/5.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.78/5.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.78/5.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.78/5.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.78/5.88  tff('#skF_6', type, '#skF_6': $i).
% 12.78/5.88  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 12.78/5.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.78/5.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.78/5.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.78/5.88  tff('#skF_8', type, '#skF_8': $i).
% 12.78/5.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.78/5.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.78/5.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.78/5.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.78/5.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.78/5.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.78/5.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.78/5.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.78/5.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.78/5.88  
% 13.17/5.92  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 13.17/5.92  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.17/5.92  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 13.17/5.92  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.17/5.92  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.17/5.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.17/5.92  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.17/5.92  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.17/5.92  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.17/5.92  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 13.17/5.92  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 13.17/5.92  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.17/5.92  tff(c_164, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.17/5.92  tff(c_173, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_164])).
% 13.17/5.92  tff(c_62, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.17/5.92  tff(c_184, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_62])).
% 13.17/5.92  tff(c_245, plain, (![A_123, B_124, C_125]: (m1_subset_1(k2_relset_1(A_123, B_124, C_125), k1_zfmisc_1(B_124)) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.17/5.92  tff(c_266, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_173, c_245])).
% 13.17/5.92  tff(c_272, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_266])).
% 13.17/5.92  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.17/5.92  tff(c_276, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_272, c_14])).
% 13.17/5.92  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.17/5.92  tff(c_280, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_276, c_8])).
% 13.17/5.92  tff(c_284, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_184, c_280])).
% 13.17/5.92  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.17/5.92  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.17/5.92  tff(c_83, plain, (![A_75, B_76]: (r1_tarski(A_75, B_76) | ~m1_subset_1(A_75, k1_zfmisc_1(B_76)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.17/5.92  tff(c_87, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_83])).
% 13.17/5.92  tff(c_72, plain, (![D_72]: (r2_hidden('#skF_9'(D_72), '#skF_6') | ~r2_hidden(D_72, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.17/5.92  tff(c_144, plain, (![C_95, B_96, A_97]: (r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.17/5.92  tff(c_151, plain, (![D_98, B_99]: (r2_hidden('#skF_9'(D_98), B_99) | ~r1_tarski('#skF_6', B_99) | ~r2_hidden(D_98, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_144])).
% 13.17/5.92  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.17/5.92  tff(c_193, plain, (![D_109, B_110, B_111]: (r2_hidden('#skF_9'(D_109), B_110) | ~r1_tarski(B_111, B_110) | ~r1_tarski('#skF_6', B_111) | ~r2_hidden(D_109, '#skF_7'))), inference(resolution, [status(thm)], [c_151, c_2])).
% 13.17/5.92  tff(c_198, plain, (![D_109]: (r2_hidden('#skF_9'(D_109), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski('#skF_6', '#skF_8') | ~r2_hidden(D_109, '#skF_7'))), inference(resolution, [status(thm)], [c_87, c_193])).
% 13.17/5.92  tff(c_285, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_198])).
% 13.17/5.92  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.17/5.92  tff(c_174, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.17/5.92  tff(c_183, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_174])).
% 13.17/5.92  tff(c_8490, plain, (![B_985, A_986, C_987]: (k1_xboole_0=B_985 | k1_relset_1(A_986, B_985, C_987)=A_986 | ~v1_funct_2(C_987, A_986, B_985) | ~m1_subset_1(C_987, k1_zfmisc_1(k2_zfmisc_1(A_986, B_985))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_8501, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_8490])).
% 13.17/5.92  tff(c_8506, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_183, c_8501])).
% 13.17/5.92  tff(c_8521, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_8506])).
% 13.17/5.92  tff(c_150, plain, (![D_72, B_96]: (r2_hidden('#skF_9'(D_72), B_96) | ~r1_tarski('#skF_6', B_96) | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_144])).
% 13.17/5.92  tff(c_104, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.17/5.92  tff(c_113, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_104])).
% 13.17/5.92  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.17/5.92  tff(c_70, plain, (![D_72]: (k1_funct_1('#skF_8', '#skF_9'(D_72))=D_72 | ~r2_hidden(D_72, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.17/5.92  tff(c_301, plain, (![A_130, D_131]: (r2_hidden(k1_funct_1(A_130, D_131), k2_relat_1(A_130)) | ~r2_hidden(D_131, k1_relat_1(A_130)) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.17/5.92  tff(c_306, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_301])).
% 13.17/5.92  tff(c_369, plain, (![D_140]: (r2_hidden(D_140, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_140), k1_relat_1('#skF_8')) | ~r2_hidden(D_140, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_68, c_306])).
% 13.17/5.92  tff(c_374, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_150, c_369])).
% 13.17/5.92  tff(c_375, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_374])).
% 13.17/5.92  tff(c_8523, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8521, c_375])).
% 13.17/5.92  tff(c_8528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8523])).
% 13.17/5.92  tff(c_8529, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8506])).
% 13.17/5.92  tff(c_7479, plain, (![B_909, A_910, C_911]: (k1_xboole_0=B_909 | k1_relset_1(A_910, B_909, C_911)=A_910 | ~v1_funct_2(C_911, A_910, B_909) | ~m1_subset_1(C_911, k1_zfmisc_1(k2_zfmisc_1(A_910, B_909))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_7494, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_7479])).
% 13.17/5.92  tff(c_7500, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_183, c_7494])).
% 13.17/5.92  tff(c_7501, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_7500])).
% 13.17/5.92  tff(c_7503, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7501, c_375])).
% 13.17/5.92  tff(c_7508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_7503])).
% 13.17/5.92  tff(c_7510, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_7500])).
% 13.17/5.92  tff(c_7509, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7500])).
% 13.17/5.92  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.17/5.92  tff(c_3658, plain, (![C_550, A_551]: (k1_xboole_0=C_550 | ~v1_funct_2(C_550, A_551, k1_xboole_0) | k1_xboole_0=A_551 | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_551, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_3668, plain, (![A_8, A_551]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_551, k1_xboole_0) | k1_xboole_0=A_551 | ~r1_tarski(A_8, k2_zfmisc_1(A_551, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_3658])).
% 13.17/5.92  tff(c_7713, plain, (![A_940, A_941]: (A_940='#skF_7' | ~v1_funct_2(A_940, A_941, '#skF_7') | A_941='#skF_7' | ~r1_tarski(A_940, k2_zfmisc_1(A_941, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_7509, c_7509, c_7509, c_7509, c_3668])).
% 13.17/5.92  tff(c_7731, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_7713])).
% 13.17/5.92  tff(c_7742, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_7731])).
% 13.17/5.92  tff(c_7744, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_7742])).
% 13.17/5.92  tff(c_7800, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7744, c_66])).
% 13.17/5.92  tff(c_7791, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7744, c_183])).
% 13.17/5.92  tff(c_7798, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7744, c_87])).
% 13.17/5.92  tff(c_3832, plain, (![B_572, C_573]: (k1_relset_1(k1_xboole_0, B_572, C_573)=k1_xboole_0 | ~v1_funct_2(C_573, k1_xboole_0, B_572) | ~m1_subset_1(C_573, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_572))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_3842, plain, (![B_572, A_8]: (k1_relset_1(k1_xboole_0, B_572, A_8)=k1_xboole_0 | ~v1_funct_2(A_8, k1_xboole_0, B_572) | ~r1_tarski(A_8, k2_zfmisc_1(k1_xboole_0, B_572)))), inference(resolution, [status(thm)], [c_16, c_3832])).
% 13.17/5.92  tff(c_7520, plain, (![B_572, A_8]: (k1_relset_1('#skF_7', B_572, A_8)='#skF_7' | ~v1_funct_2(A_8, '#skF_7', B_572) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_7', B_572)))), inference(demodulation, [status(thm), theory('equality')], [c_7509, c_7509, c_7509, c_7509, c_3842])).
% 13.17/5.92  tff(c_8187, plain, (![B_976, A_977]: (k1_relset_1('#skF_6', B_976, A_977)='#skF_6' | ~v1_funct_2(A_977, '#skF_6', B_976) | ~r1_tarski(A_977, k2_zfmisc_1('#skF_6', B_976)))), inference(demodulation, [status(thm), theory('equality')], [c_7744, c_7744, c_7744, c_7744, c_7520])).
% 13.17/5.92  tff(c_8193, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_7798, c_8187])).
% 13.17/5.92  tff(c_8213, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7800, c_7791, c_8193])).
% 13.17/5.92  tff(c_8215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7510, c_8213])).
% 13.17/5.92  tff(c_8216, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_7742])).
% 13.17/5.92  tff(c_2751, plain, (![B_461, A_462, C_463]: (k1_xboole_0=B_461 | k1_relset_1(A_462, B_461, C_463)=A_462 | ~v1_funct_2(C_463, A_462, B_461) | ~m1_subset_1(C_463, k1_zfmisc_1(k2_zfmisc_1(A_462, B_461))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_2766, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_2751])).
% 13.17/5.92  tff(c_2773, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_183, c_2766])).
% 13.17/5.92  tff(c_2774, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_2773])).
% 13.17/5.92  tff(c_2775, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_375])).
% 13.17/5.92  tff(c_2780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2775])).
% 13.17/5.92  tff(c_2782, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_2773])).
% 13.17/5.92  tff(c_2781, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2773])).
% 13.17/5.92  tff(c_2079, plain, (![C_358, A_359]: (k1_xboole_0=C_358 | ~v1_funct_2(C_358, A_359, k1_xboole_0) | k1_xboole_0=A_359 | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_2089, plain, (![A_8, A_359]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_359, k1_xboole_0) | k1_xboole_0=A_359 | ~r1_tarski(A_8, k2_zfmisc_1(A_359, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_2079])).
% 13.17/5.92  tff(c_3009, plain, (![A_494, A_495]: (A_494='#skF_7' | ~v1_funct_2(A_494, A_495, '#skF_7') | A_495='#skF_7' | ~r1_tarski(A_494, k2_zfmisc_1(A_495, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_2781, c_2781, c_2781, c_2781, c_2089])).
% 13.17/5.92  tff(c_3027, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_3009])).
% 13.17/5.92  tff(c_3038, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3027])).
% 13.17/5.92  tff(c_3040, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_3038])).
% 13.17/5.92  tff(c_3105, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3040, c_66])).
% 13.17/5.92  tff(c_3096, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3040, c_183])).
% 13.17/5.92  tff(c_3103, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3040, c_87])).
% 13.17/5.92  tff(c_2123, plain, (![B_367, C_368]: (k1_relset_1(k1_xboole_0, B_367, C_368)=k1_xboole_0 | ~v1_funct_2(C_368, k1_xboole_0, B_367) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_367))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_2133, plain, (![B_367, A_8]: (k1_relset_1(k1_xboole_0, B_367, A_8)=k1_xboole_0 | ~v1_funct_2(A_8, k1_xboole_0, B_367) | ~r1_tarski(A_8, k2_zfmisc_1(k1_xboole_0, B_367)))), inference(resolution, [status(thm)], [c_16, c_2123])).
% 13.17/5.92  tff(c_2787, plain, (![B_367, A_8]: (k1_relset_1('#skF_7', B_367, A_8)='#skF_7' | ~v1_funct_2(A_8, '#skF_7', B_367) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_7', B_367)))), inference(demodulation, [status(thm), theory('equality')], [c_2781, c_2781, c_2781, c_2781, c_2133])).
% 13.17/5.92  tff(c_3563, plain, (![B_542, A_543]: (k1_relset_1('#skF_6', B_542, A_543)='#skF_6' | ~v1_funct_2(A_543, '#skF_6', B_542) | ~r1_tarski(A_543, k2_zfmisc_1('#skF_6', B_542)))), inference(demodulation, [status(thm), theory('equality')], [c_3040, c_3040, c_3040, c_3040, c_2787])).
% 13.17/5.92  tff(c_3569, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_3103, c_3563])).
% 13.17/5.92  tff(c_3589, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3105, c_3096, c_3569])).
% 13.17/5.92  tff(c_3591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2782, c_3589])).
% 13.17/5.92  tff(c_3592, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_3038])).
% 13.17/5.92  tff(c_1133, plain, (![B_260, A_261, C_262]: (k1_xboole_0=B_260 | k1_relset_1(A_261, B_260, C_262)=A_261 | ~v1_funct_2(C_262, A_261, B_260) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_261, B_260))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_1148, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_1133])).
% 13.17/5.92  tff(c_1155, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_183, c_1148])).
% 13.17/5.92  tff(c_1156, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1155])).
% 13.17/5.92  tff(c_1157, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_375])).
% 13.17/5.92  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1157])).
% 13.17/5.92  tff(c_1164, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_1155])).
% 13.17/5.92  tff(c_1163, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1155])).
% 13.17/5.92  tff(c_378, plain, (![C_143, A_144]: (k1_xboole_0=C_143 | ~v1_funct_2(C_143, A_144, k1_xboole_0) | k1_xboole_0=A_144 | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_388, plain, (![A_8, A_144]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_144, k1_xboole_0) | k1_xboole_0=A_144 | ~r1_tarski(A_8, k2_zfmisc_1(A_144, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_378])).
% 13.17/5.92  tff(c_1318, plain, (![A_288, A_289]: (A_288='#skF_7' | ~v1_funct_2(A_288, A_289, '#skF_7') | A_289='#skF_7' | ~r1_tarski(A_288, k2_zfmisc_1(A_289, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_1163, c_1163, c_1163, c_388])).
% 13.17/5.92  tff(c_1336, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_1318])).
% 13.17/5.92  tff(c_1347, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1336])).
% 13.17/5.92  tff(c_1349, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_1347])).
% 13.17/5.92  tff(c_1398, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_66])).
% 13.17/5.92  tff(c_1389, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_183])).
% 13.17/5.92  tff(c_1396, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_87])).
% 13.17/5.92  tff(c_477, plain, (![B_165, C_166]: (k1_relset_1(k1_xboole_0, B_165, C_166)=k1_xboole_0 | ~v1_funct_2(C_166, k1_xboole_0, B_165) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_165))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_487, plain, (![B_165, A_8]: (k1_relset_1(k1_xboole_0, B_165, A_8)=k1_xboole_0 | ~v1_funct_2(A_8, k1_xboole_0, B_165) | ~r1_tarski(A_8, k2_zfmisc_1(k1_xboole_0, B_165)))), inference(resolution, [status(thm)], [c_16, c_477])).
% 13.17/5.92  tff(c_1167, plain, (![B_165, A_8]: (k1_relset_1('#skF_7', B_165, A_8)='#skF_7' | ~v1_funct_2(A_8, '#skF_7', B_165) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_7', B_165)))), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_1163, c_1163, c_1163, c_487])).
% 13.17/5.92  tff(c_1977, plain, (![B_351, A_352]: (k1_relset_1('#skF_6', B_351, A_352)='#skF_6' | ~v1_funct_2(A_352, '#skF_6', B_351) | ~r1_tarski(A_352, k2_zfmisc_1('#skF_6', B_351)))), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_1349, c_1349, c_1349, c_1167])).
% 13.17/5.92  tff(c_1983, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1396, c_1977])).
% 13.17/5.92  tff(c_2003, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1389, c_1983])).
% 13.17/5.92  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1164, c_2003])).
% 13.17/5.92  tff(c_2006, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_1347])).
% 13.17/5.92  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.17/5.92  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.17/5.92  tff(c_309, plain, (![D_131]: (r2_hidden(k1_funct_1(k1_xboole_0, D_131), k1_xboole_0) | ~r2_hidden(D_131, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_301])).
% 13.17/5.92  tff(c_313, plain, (![D_131]: (r2_hidden(k1_funct_1(k1_xboole_0, D_131), k1_xboole_0) | ~r2_hidden(D_131, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_309])).
% 13.17/5.92  tff(c_377, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_313])).
% 13.17/5.92  tff(c_1175, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_377])).
% 13.17/5.92  tff(c_2034, plain, (~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2006, c_1175])).
% 13.17/5.92  tff(c_2074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_2034])).
% 13.17/5.92  tff(c_2075, plain, (![D_131]: (~v1_funct_1(k1_xboole_0) | r2_hidden(k1_funct_1(k1_xboole_0, D_131), k1_xboole_0) | ~r2_hidden(D_131, k1_xboole_0))), inference(splitRight, [status(thm)], [c_313])).
% 13.17/5.92  tff(c_2077, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2075])).
% 13.17/5.92  tff(c_2793, plain, (~v1_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2781, c_2077])).
% 13.17/5.92  tff(c_3605, plain, (~v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3592, c_2793])).
% 13.17/5.92  tff(c_3646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_3605])).
% 13.17/5.92  tff(c_3649, plain, (![D_544]: (r2_hidden(k1_funct_1(k1_xboole_0, D_544), k1_xboole_0) | ~r2_hidden(D_544, k1_xboole_0))), inference(splitRight, [status(thm)], [c_2075])).
% 13.17/5.92  tff(c_3654, plain, (![D_548, B_549]: (r2_hidden(k1_funct_1(k1_xboole_0, D_548), B_549) | ~r1_tarski(k1_xboole_0, B_549) | ~r2_hidden(D_548, k1_xboole_0))), inference(resolution, [status(thm)], [c_3649, c_2])).
% 13.17/5.92  tff(c_7250, plain, (![D_872, B_873, B_874]: (r2_hidden(k1_funct_1(k1_xboole_0, D_872), B_873) | ~r1_tarski(B_874, B_873) | ~r1_tarski(k1_xboole_0, B_874) | ~r2_hidden(D_872, k1_xboole_0))), inference(resolution, [status(thm)], [c_3654, c_2])).
% 13.17/5.92  tff(c_7273, plain, (![D_872]: (r2_hidden(k1_funct_1(k1_xboole_0, D_872), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski(k1_xboole_0, '#skF_8') | ~r2_hidden(D_872, k1_xboole_0))), inference(resolution, [status(thm)], [c_87, c_7250])).
% 13.17/5.92  tff(c_7275, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(splitLeft, [status(thm)], [c_7273])).
% 13.17/5.92  tff(c_7514, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7509, c_7275])).
% 13.17/5.92  tff(c_8233, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8216, c_7514])).
% 13.17/5.92  tff(c_8275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8233])).
% 13.17/5.92  tff(c_8277, plain, (r1_tarski(k1_xboole_0, '#skF_8')), inference(splitRight, [status(thm)], [c_7273])).
% 13.17/5.92  tff(c_8538, plain, (r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8529, c_8277])).
% 13.17/5.92  tff(c_155, plain, (![A_100, B_101, B_102]: (r2_hidden('#skF_1'(A_100, B_101), B_102) | ~r1_tarski(A_100, B_102) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_6, c_144])).
% 13.17/5.92  tff(c_3686, plain, (![A_555, B_556, B_557, B_558]: (r2_hidden('#skF_1'(A_555, B_556), B_557) | ~r1_tarski(B_558, B_557) | ~r1_tarski(A_555, B_558) | r1_tarski(A_555, B_556))), inference(resolution, [status(thm)], [c_155, c_2])).
% 13.17/5.92  tff(c_3749, plain, (![A_565, B_566]: (r2_hidden('#skF_1'(A_565, B_566), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski(A_565, '#skF_8') | r1_tarski(A_565, B_566))), inference(resolution, [status(thm)], [c_87, c_3686])).
% 13.17/5.92  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.17/5.92  tff(c_3757, plain, (![A_565]: (~r1_tarski(A_565, '#skF_8') | r1_tarski(A_565, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_3749, c_4])).
% 13.17/5.92  tff(c_240, plain, (![A_122]: (v1_funct_2(k1_xboole_0, A_122, k1_xboole_0) | k1_xboole_0=A_122 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_122, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_244, plain, (![A_122]: (v1_funct_2(k1_xboole_0, A_122, k1_xboole_0) | k1_xboole_0=A_122 | ~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_122, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_240])).
% 13.17/5.92  tff(c_8832, plain, (![A_1005]: (v1_funct_2('#skF_7', A_1005, '#skF_7') | A_1005='#skF_7' | ~r1_tarski('#skF_7', k2_zfmisc_1(A_1005, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_8529, c_8529, c_8529, c_8529, c_8529, c_244])).
% 13.17/5.92  tff(c_8839, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_3757, c_8832])).
% 13.17/5.92  tff(c_8843, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8538, c_8839])).
% 13.17/5.92  tff(c_8844, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_8843])).
% 13.17/5.92  tff(c_154, plain, (![D_98, B_2, B_99]: (r2_hidden('#skF_9'(D_98), B_2) | ~r1_tarski(B_99, B_2) | ~r1_tarski('#skF_6', B_99) | ~r2_hidden(D_98, '#skF_7'))), inference(resolution, [status(thm)], [c_151, c_2])).
% 13.17/5.92  tff(c_8305, plain, (![D_98]: (r2_hidden('#skF_9'(D_98), '#skF_8') | ~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_98, '#skF_7'))), inference(resolution, [status(thm)], [c_8277, c_154])).
% 13.17/5.92  tff(c_8634, plain, (![D_98]: (r2_hidden('#skF_9'(D_98), '#skF_8') | ~r1_tarski('#skF_6', '#skF_7') | ~r2_hidden(D_98, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8529, c_8305])).
% 13.17/5.92  tff(c_8635, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_8634])).
% 13.17/5.92  tff(c_8858, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8844, c_8635])).
% 13.17/5.92  tff(c_8900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8858])).
% 13.17/5.92  tff(c_8902, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_8843])).
% 13.17/5.92  tff(c_9410, plain, (![A_1057, A_1058]: (A_1057='#skF_7' | ~v1_funct_2(A_1057, A_1058, '#skF_7') | A_1058='#skF_7' | ~r1_tarski(A_1057, k2_zfmisc_1(A_1058, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_8529, c_8529, c_8529, c_8529, c_3668])).
% 13.17/5.92  tff(c_9430, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_9410])).
% 13.17/5.92  tff(c_9450, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9430])).
% 13.17/5.92  tff(c_9451, plain, ('#skF_7'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_8902, c_9450])).
% 13.17/5.92  tff(c_8306, plain, (k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_8277, c_8])).
% 13.17/5.92  tff(c_8307, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8306])).
% 13.17/5.92  tff(c_8536, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8529, c_8307])).
% 13.17/5.92  tff(c_9497, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9451, c_8536])).
% 13.17/5.92  tff(c_9542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_9497])).
% 13.17/5.92  tff(c_9544, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_8634])).
% 13.17/5.92  tff(c_162, plain, (![A_100, B_101, B_2, B_102]: (r2_hidden('#skF_1'(A_100, B_101), B_2) | ~r1_tarski(B_102, B_2) | ~r1_tarski(A_100, B_102) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_155, c_2])).
% 13.17/5.92  tff(c_9914, plain, (![A_1094, B_1095]: (r2_hidden('#skF_1'(A_1094, B_1095), '#skF_8') | ~r1_tarski(A_1094, '#skF_7') | r1_tarski(A_1094, B_1095))), inference(resolution, [status(thm)], [c_8538, c_162])).
% 13.17/5.92  tff(c_9923, plain, (![A_1096]: (~r1_tarski(A_1096, '#skF_7') | r1_tarski(A_1096, '#skF_8'))), inference(resolution, [status(thm)], [c_9914, c_4])).
% 13.17/5.92  tff(c_9926, plain, (r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_9544, c_9923])).
% 13.17/5.92  tff(c_9951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_9926])).
% 13.17/5.92  tff(c_9952, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_8306])).
% 13.17/5.92  tff(c_9974, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9952, c_9952, c_18])).
% 13.17/5.92  tff(c_9996, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9974, c_184])).
% 13.17/5.92  tff(c_9975, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9952, c_9952, c_20])).
% 13.17/5.92  tff(c_10019, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9975, c_183])).
% 13.17/5.92  tff(c_58, plain, (![B_63, A_62, C_64]: (k1_xboole_0=B_63 | k1_relset_1(A_62, B_63, C_64)=A_62 | ~v1_funct_2(C_64, A_62, B_63) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_10139, plain, (![B_1107, A_1108, C_1109]: (B_1107='#skF_8' | k1_relset_1(A_1108, B_1107, C_1109)=A_1108 | ~v1_funct_2(C_1109, A_1108, B_1107) | ~m1_subset_1(C_1109, k1_zfmisc_1(k2_zfmisc_1(A_1108, B_1107))))), inference(demodulation, [status(thm), theory('equality')], [c_9952, c_58])).
% 13.17/5.92  tff(c_10150, plain, ('#skF_7'='#skF_8' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_10139])).
% 13.17/5.92  tff(c_10155, plain, ('#skF_7'='#skF_8' | '#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10019, c_10150])).
% 13.17/5.92  tff(c_10156, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_9996, c_10155])).
% 13.17/5.92  tff(c_10171, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10156, c_285])).
% 13.17/5.92  tff(c_10181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10171])).
% 13.17/5.92  tff(c_10192, plain, (![D_1110]: (r2_hidden(D_1110, k2_relat_1('#skF_8')) | ~r2_hidden(D_1110, '#skF_7'))), inference(splitRight, [status(thm)], [c_374])).
% 13.17/5.92  tff(c_10207, plain, (![A_1115]: (r1_tarski(A_1115, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_1115, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_10192, c_4])).
% 13.17/5.92  tff(c_10215, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_10207])).
% 13.17/5.92  tff(c_10220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_284, c_10215])).
% 13.17/5.92  tff(c_10222, plain, (r1_tarski('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_198])).
% 13.17/5.92  tff(c_21326, plain, (![B_1954, A_1955, C_1956]: (k1_xboole_0=B_1954 | k1_relset_1(A_1955, B_1954, C_1956)=A_1955 | ~v1_funct_2(C_1956, A_1955, B_1954) | ~m1_subset_1(C_1956, k1_zfmisc_1(k2_zfmisc_1(A_1955, B_1954))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_21337, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_21326])).
% 13.17/5.92  tff(c_21342, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_183, c_21337])).
% 13.17/5.92  tff(c_21343, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_21342])).
% 13.17/5.92  tff(c_10231, plain, (![A_1116, D_1117]: (r2_hidden(k1_funct_1(A_1116, D_1117), k2_relat_1(A_1116)) | ~r2_hidden(D_1117, k1_relat_1(A_1116)) | ~v1_funct_1(A_1116) | ~v1_relat_1(A_1116))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.17/5.92  tff(c_10236, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_10231])).
% 13.17/5.92  tff(c_10249, plain, (![D_1119]: (r2_hidden(D_1119, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_1119), k1_relat_1('#skF_8')) | ~r2_hidden(D_1119, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_68, c_10236])).
% 13.17/5.92  tff(c_10254, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_150, c_10249])).
% 13.17/5.92  tff(c_10269, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_10254])).
% 13.17/5.92  tff(c_21346, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21343, c_10269])).
% 13.17/5.92  tff(c_21351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_21346])).
% 13.17/5.92  tff(c_21353, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_21342])).
% 13.17/5.92  tff(c_21352, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_21342])).
% 13.17/5.92  tff(c_10270, plain, (![C_1124, A_1125]: (k1_xboole_0=C_1124 | ~v1_funct_2(C_1124, A_1125, k1_xboole_0) | k1_xboole_0=A_1125 | ~m1_subset_1(C_1124, k1_zfmisc_1(k2_zfmisc_1(A_1125, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_10280, plain, (![A_8, A_1125]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_1125, k1_xboole_0) | k1_xboole_0=A_1125 | ~r1_tarski(A_8, k2_zfmisc_1(A_1125, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_10270])).
% 13.17/5.92  tff(c_23110, plain, (![A_2070, A_2071]: (A_2070='#skF_7' | ~v1_funct_2(A_2070, A_2071, '#skF_7') | A_2071='#skF_7' | ~r1_tarski(A_2070, k2_zfmisc_1(A_2071, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_21352, c_21352, c_21352, c_21352, c_10280])).
% 13.17/5.92  tff(c_23133, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_23110])).
% 13.17/5.92  tff(c_23151, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_23133])).
% 13.17/5.92  tff(c_23153, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_23151])).
% 13.17/5.92  tff(c_23238, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23153, c_66])).
% 13.17/5.92  tff(c_23236, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_23153, c_87])).
% 13.17/5.92  tff(c_17178, plain, (![B_1656, C_1657]: (k1_relset_1(k1_xboole_0, B_1656, C_1657)=k1_xboole_0 | ~v1_funct_2(C_1657, k1_xboole_0, B_1656) | ~m1_subset_1(C_1657, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_1656))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_17188, plain, (![B_1656, A_8]: (k1_relset_1(k1_xboole_0, B_1656, A_8)=k1_xboole_0 | ~v1_funct_2(A_8, k1_xboole_0, B_1656) | ~r1_tarski(A_8, k2_zfmisc_1(k1_xboole_0, B_1656)))), inference(resolution, [status(thm)], [c_16, c_17178])).
% 13.17/5.92  tff(c_21359, plain, (![B_1656, A_8]: (k1_relset_1('#skF_7', B_1656, A_8)='#skF_7' | ~v1_funct_2(A_8, '#skF_7', B_1656) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_7', B_1656)))), inference(demodulation, [status(thm), theory('equality')], [c_21352, c_21352, c_21352, c_21352, c_17188])).
% 13.17/5.92  tff(c_23299, plain, (![B_1656, A_8]: (k1_relset_1('#skF_6', B_1656, A_8)='#skF_6' | ~v1_funct_2(A_8, '#skF_6', B_1656) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_6', B_1656)))), inference(demodulation, [status(thm), theory('equality')], [c_23153, c_23153, c_23153, c_23153, c_21359])).
% 13.17/5.92  tff(c_23324, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_23236, c_23299])).
% 13.17/5.92  tff(c_23343, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_23238, c_23324])).
% 13.17/5.92  tff(c_23229, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23153, c_183])).
% 13.17/5.92  tff(c_23520, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_23343, c_23229])).
% 13.17/5.92  tff(c_23521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21353, c_23520])).
% 13.17/5.92  tff(c_23522, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_23151])).
% 13.17/5.92  tff(c_21807, plain, (![A_2005, A_2006]: (A_2005='#skF_7' | ~v1_funct_2(A_2005, A_2006, '#skF_7') | A_2006='#skF_7' | ~r1_tarski(A_2005, k2_zfmisc_1(A_2006, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_21352, c_21352, c_21352, c_21352, c_10280])).
% 13.17/5.92  tff(c_21824, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_21807])).
% 13.17/5.92  tff(c_21835, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_21824])).
% 13.17/5.92  tff(c_21837, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_21835])).
% 13.17/5.92  tff(c_17245, plain, (![A_1671, B_1672, B_1673, B_1674]: (r2_hidden('#skF_1'(A_1671, B_1672), B_1673) | ~r1_tarski(B_1674, B_1673) | ~r1_tarski(A_1671, B_1674) | r1_tarski(A_1671, B_1672))), inference(resolution, [status(thm)], [c_155, c_2])).
% 13.17/5.92  tff(c_17371, plain, (![A_1684, B_1685]: (r2_hidden('#skF_1'(A_1684, B_1685), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski(A_1684, '#skF_8') | r1_tarski(A_1684, B_1685))), inference(resolution, [status(thm)], [c_87, c_17245])).
% 13.17/5.92  tff(c_17379, plain, (![A_1684]: (~r1_tarski(A_1684, '#skF_8') | r1_tarski(A_1684, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_17371, c_4])).
% 13.17/5.92  tff(c_21515, plain, (![A_1966]: (v1_funct_2('#skF_7', A_1966, '#skF_7') | A_1966='#skF_7' | ~r1_tarski('#skF_7', k2_zfmisc_1(A_1966, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_21352, c_21352, c_21352, c_21352, c_21352, c_244])).
% 13.17/5.92  tff(c_21520, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_17379, c_21515])).
% 13.17/5.92  tff(c_21521, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_21520])).
% 13.17/5.92  tff(c_21871, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_21837, c_21521])).
% 13.17/5.92  tff(c_21921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10222, c_21871])).
% 13.17/5.92  tff(c_21922, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_21835])).
% 13.17/5.92  tff(c_21945, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_21922, c_21521])).
% 13.17/5.92  tff(c_21995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_21945])).
% 13.17/5.92  tff(c_21997, plain, (r1_tarski('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_21520])).
% 13.17/5.92  tff(c_22035, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_21997, c_8])).
% 13.17/5.92  tff(c_22054, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_22035])).
% 13.17/5.92  tff(c_23559, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23522, c_22054])).
% 13.17/5.92  tff(c_23616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_23559])).
% 13.17/5.92  tff(c_23617, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_22035])).
% 13.17/5.92  tff(c_21373, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_21352, c_21352, c_18])).
% 13.17/5.92  tff(c_23630, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_23617, c_23617, c_21373])).
% 13.17/5.92  tff(c_10224, plain, (![D_98]: (r2_hidden('#skF_9'(D_98), '#skF_8') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_98, '#skF_7'))), inference(resolution, [status(thm)], [c_10222, c_154])).
% 13.17/5.92  tff(c_10245, plain, (![D_1118]: (r2_hidden('#skF_9'(D_1118), '#skF_8') | ~r2_hidden(D_1118, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10224])).
% 13.17/5.92  tff(c_10259, plain, (![D_1121, B_1122]: (r2_hidden('#skF_9'(D_1121), B_1122) | ~r1_tarski('#skF_8', B_1122) | ~r2_hidden(D_1121, '#skF_7'))), inference(resolution, [status(thm)], [c_10245, c_2])).
% 13.17/5.92  tff(c_17156, plain, (![D_1653, B_1654, B_1655]: (r2_hidden('#skF_9'(D_1653), B_1654) | ~r1_tarski(B_1655, B_1654) | ~r1_tarski('#skF_8', B_1655) | ~r2_hidden(D_1653, '#skF_7'))), inference(resolution, [status(thm)], [c_10259, c_2])).
% 13.17/5.92  tff(c_17172, plain, (![D_1653]: (r2_hidden('#skF_9'(D_1653), '#skF_7') | ~r1_tarski('#skF_8', k2_relat_1('#skF_8')) | ~r2_hidden(D_1653, '#skF_7'))), inference(resolution, [status(thm)], [c_276, c_17156])).
% 13.17/5.92  tff(c_17177, plain, (~r1_tarski('#skF_8', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_17172])).
% 13.17/5.92  tff(c_23681, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23630, c_17177])).
% 13.17/5.92  tff(c_23685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_23681])).
% 13.17/5.92  tff(c_23687, plain, (r1_tarski('#skF_8', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_17172])).
% 13.17/5.92  tff(c_23913, plain, (![A_2117, B_2118, B_2119, B_2120]: (r2_hidden('#skF_1'(A_2117, B_2118), B_2119) | ~r1_tarski(B_2120, B_2119) | ~r1_tarski(A_2117, B_2120) | r1_tarski(A_2117, B_2118))), inference(resolution, [status(thm)], [c_155, c_2])).
% 13.17/5.92  tff(c_24897, plain, (![A_2212, B_2213]: (r2_hidden('#skF_1'(A_2212, B_2213), k2_relat_1('#skF_8')) | ~r1_tarski(A_2212, '#skF_8') | r1_tarski(A_2212, B_2213))), inference(resolution, [status(thm)], [c_23687, c_23913])).
% 13.17/5.92  tff(c_24906, plain, (![A_2214]: (~r1_tarski(A_2214, '#skF_8') | r1_tarski(A_2214, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_24897, c_4])).
% 13.17/5.92  tff(c_281, plain, (![D_98]: (r2_hidden('#skF_9'(D_98), '#skF_7') | ~r1_tarski('#skF_6', k2_relat_1('#skF_8')) | ~r2_hidden(D_98, '#skF_7'))), inference(resolution, [status(thm)], [c_276, c_154])).
% 13.17/5.92  tff(c_10281, plain, (~r1_tarski('#skF_6', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_281])).
% 13.17/5.92  tff(c_24934, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_24906, c_10281])).
% 13.17/5.92  tff(c_24956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10222, c_24934])).
% 13.17/5.92  tff(c_24958, plain, (r1_tarski('#skF_6', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_281])).
% 13.17/5.92  tff(c_29464, plain, (![B_2619, A_2620, C_2621]: (k1_xboole_0=B_2619 | k1_relset_1(A_2620, B_2619, C_2621)=A_2620 | ~v1_funct_2(C_2621, A_2620, B_2619) | ~m1_subset_1(C_2621, k1_zfmisc_1(k2_zfmisc_1(A_2620, B_2619))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.17/5.92  tff(c_29475, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_29464])).
% 13.17/5.92  tff(c_29480, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_183, c_29475])).
% 13.17/5.92  tff(c_29481, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_29480])).
% 13.17/5.92  tff(c_29486, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29481, c_10269])).
% 13.17/5.92  tff(c_29491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_29486])).
% 13.17/5.92  tff(c_29492, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_29480])).
% 13.17/5.92  tff(c_31142, plain, (![A_2738, A_2739]: (A_2738='#skF_7' | ~v1_funct_2(A_2738, A_2739, '#skF_7') | A_2739='#skF_7' | ~r1_tarski(A_2738, k2_zfmisc_1(A_2739, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_29492, c_29492, c_29492, c_29492, c_10280])).
% 13.17/5.92  tff(c_31162, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_31142])).
% 13.17/5.92  tff(c_31177, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_31162])).
% 13.17/5.92  tff(c_31179, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_31177])).
% 13.17/5.92  tff(c_31250, plain, (~r1_tarski('#skF_6', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_31179, c_284])).
% 13.17/5.92  tff(c_31270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24958, c_31250])).
% 13.17/5.92  tff(c_31271, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_31177])).
% 13.17/5.92  tff(c_30214, plain, (![A_2691, A_2692]: (A_2691='#skF_7' | ~v1_funct_2(A_2691, A_2692, '#skF_7') | A_2692='#skF_7' | ~r1_tarski(A_2691, k2_zfmisc_1(A_2692, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_29492, c_29492, c_29492, c_29492, c_10280])).
% 13.17/5.92  tff(c_30231, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_87, c_30214])).
% 13.17/5.92  tff(c_30242, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_30231])).
% 13.17/5.92  tff(c_30244, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_30242])).
% 13.17/5.92  tff(c_29235, plain, (![A_2598, B_2599, B_2600, B_2601]: (r2_hidden('#skF_1'(A_2598, B_2599), B_2600) | ~r1_tarski(B_2601, B_2600) | ~r1_tarski(A_2598, B_2601) | r1_tarski(A_2598, B_2599))), inference(resolution, [status(thm)], [c_155, c_2])).
% 13.17/5.92  tff(c_29932, plain, (![A_2669, B_2670]: (r2_hidden('#skF_1'(A_2669, B_2670), '#skF_7') | ~r1_tarski(A_2669, k2_relat_1('#skF_8')) | r1_tarski(A_2669, B_2670))), inference(resolution, [status(thm)], [c_276, c_29235])).
% 13.17/5.92  tff(c_29972, plain, (![A_2674]: (~r1_tarski(A_2674, k2_relat_1('#skF_8')) | r1_tarski(A_2674, '#skF_7'))), inference(resolution, [status(thm)], [c_29932, c_4])).
% 13.17/5.92  tff(c_29990, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_24958, c_29972])).
% 13.17/5.92  tff(c_30012, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_29990, c_8])).
% 13.17/5.92  tff(c_30013, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_30012])).
% 13.17/5.92  tff(c_30253, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30244, c_30013])).
% 13.17/5.92  tff(c_30327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_30253])).
% 13.17/5.92  tff(c_30328, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_30242])).
% 13.17/5.92  tff(c_29283, plain, (![A_2605, B_2606]: (r2_hidden('#skF_1'(A_2605, B_2606), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski(A_2605, '#skF_8') | r1_tarski(A_2605, B_2606))), inference(resolution, [status(thm)], [c_87, c_29235])).
% 13.17/5.92  tff(c_29291, plain, (![A_2605]: (~r1_tarski(A_2605, '#skF_8') | r1_tarski(A_2605, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_29283, c_4])).
% 13.17/5.92  tff(c_29680, plain, (![A_2636]: (v1_funct_2('#skF_7', A_2636, '#skF_7') | A_2636='#skF_7' | ~r1_tarski('#skF_7', k2_zfmisc_1(A_2636, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_29492, c_29492, c_29492, c_29492, c_29492, c_244])).
% 13.17/5.92  tff(c_29685, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_29291, c_29680])).
% 13.17/5.92  tff(c_29686, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_29685])).
% 13.17/5.92  tff(c_30386, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30328, c_29686])).
% 13.17/5.92  tff(c_30443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_30386])).
% 13.17/5.92  tff(c_30444, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_30012])).
% 13.17/5.92  tff(c_30463, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30444, c_29686])).
% 13.17/5.92  tff(c_30520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10222, c_30463])).
% 13.17/5.92  tff(c_30522, plain, (r1_tarski('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_29685])).
% 13.17/5.92  tff(c_30554, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_30522, c_8])).
% 13.17/5.92  tff(c_30573, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_30554])).
% 13.17/5.92  tff(c_31300, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_31271, c_30573])).
% 13.17/5.92  tff(c_31361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_31300])).
% 13.17/5.92  tff(c_31362, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_30554])).
% 13.17/5.92  tff(c_31459, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31362, c_184])).
% 13.17/5.92  tff(c_29514, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_29492, c_29492, c_18])).
% 13.17/5.92  tff(c_31424, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31362, c_31362, c_29514])).
% 13.17/5.92  tff(c_31480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31459, c_31424])).
% 13.17/5.92  tff(c_31502, plain, (![D_2745]: (r2_hidden(D_2745, k2_relat_1('#skF_8')) | ~r2_hidden(D_2745, '#skF_7'))), inference(splitRight, [status(thm)], [c_10254])).
% 13.17/5.92  tff(c_31525, plain, (![A_2749]: (r1_tarski(A_2749, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_2749, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_31502, c_4])).
% 13.17/5.92  tff(c_31533, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_31525])).
% 13.17/5.92  tff(c_31538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_284, c_31533])).
% 13.17/5.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.17/5.92  
% 13.17/5.92  Inference rules
% 13.17/5.92  ----------------------
% 13.17/5.92  #Ref     : 30
% 13.17/5.92  #Sup     : 5967
% 13.17/5.92  #Fact    : 0
% 13.17/5.92  #Define  : 0
% 13.17/5.92  #Split   : 258
% 13.17/5.92  #Chain   : 0
% 13.17/5.92  #Close   : 0
% 13.17/5.92  
% 13.17/5.92  Ordering : KBO
% 13.17/5.92  
% 13.17/5.92  Simplification rules
% 13.17/5.92  ----------------------
% 13.17/5.92  #Subsume      : 1393
% 13.17/5.92  #Demod        : 11459
% 13.17/5.92  #Tautology    : 1796
% 13.17/5.92  #SimpNegUnit  : 59
% 13.17/5.92  #BackRed      : 5068
% 13.17/5.92  
% 13.17/5.92  #Partial instantiations: 0
% 13.17/5.92  #Strategies tried      : 1
% 13.17/5.92  
% 13.17/5.92  Timing (in seconds)
% 13.17/5.92  ----------------------
% 13.17/5.93  Preprocessing        : 0.52
% 13.17/5.93  Parsing              : 0.28
% 13.17/5.93  CNF conversion       : 0.04
% 13.17/5.93  Main loop            : 4.43
% 13.17/5.93  Inferencing          : 1.28
% 13.17/5.93  Reduction            : 1.58
% 13.17/5.93  Demodulation         : 1.08
% 13.17/5.93  BG Simplification    : 0.15
% 13.17/5.93  Subsumption          : 1.06
% 13.17/5.93  Abstraction          : 0.16
% 13.17/5.93  MUC search           : 0.00
% 13.17/5.93  Cooper               : 0.00
% 13.17/5.93  Total                : 5.06
% 13.17/5.93  Index Insertion      : 0.00
% 13.17/5.93  Index Deletion       : 0.00
% 13.17/5.93  Index Matching       : 0.00
% 13.17/5.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
