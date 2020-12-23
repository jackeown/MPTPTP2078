%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:16 EST 2020

% Result     : Theorem 6.52s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 358 expanded)
%              Number of leaves         :   42 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  217 (1057 expanded)
%              Number of equality atoms :   64 ( 246 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_343,plain,(
    ! [C_86,B_87,A_88] :
      ( v1_xboole_0(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(B_87,A_88)))
      | ~ v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_369,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_343])).

tff(c_376,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1000,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( r2_relset_1(A_153,B_154,C_155,C_155)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1052,plain,(
    ! [C_165] :
      ( r2_relset_1('#skF_3','#skF_4',C_165,C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_64,c_1000])).

tff(c_1068,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_1052])).

tff(c_152,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_176,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_578,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_604,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_578])).

tff(c_803,plain,(
    ! [B_138,A_139,C_140] :
      ( k1_xboole_0 = B_138
      | k1_relset_1(A_139,B_138,C_140) = A_139
      | ~ v1_funct_2(C_140,A_139,B_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_810,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_803])).

tff(c_831,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_604,c_810])).

tff(c_839,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_831])).

tff(c_177,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_152])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_605,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_578])).

tff(c_813,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_803])).

tff(c_834,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_605,c_813])).

tff(c_846,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_834])).

tff(c_180,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_206,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_180])).

tff(c_246,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,A_77) = B_76
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_255,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_206,c_246])).

tff(c_264,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_255])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_289,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_24])).

tff(c_293,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_289])).

tff(c_841,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_293])).

tff(c_1096,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_2'(A_170,B_171),k1_relat_1(A_170))
      | B_171 = A_170
      | k1_relat_1(B_171) != k1_relat_1(A_170)
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1101,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_2'('#skF_6',B_171),'#skF_3')
      | B_171 = '#skF_6'
      | k1_relat_1(B_171) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_1096])).

tff(c_1913,plain,(
    ! [B_244] :
      ( r2_hidden('#skF_2'('#skF_6',B_244),'#skF_3')
      | B_244 = '#skF_6'
      | k1_relat_1(B_244) != '#skF_3'
      | ~ v1_funct_1(B_244)
      | ~ v1_relat_1(B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_62,c_846,c_1101])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_394,plain,(
    ! [A_90,C_91,B_92] :
      ( m1_subset_1(A_90,C_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(C_91))
      | ~ r2_hidden(A_90,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_406,plain,(
    ! [A_90,B_9,A_8] :
      ( m1_subset_1(A_90,B_9)
      | ~ r2_hidden(A_90,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_394])).

tff(c_4276,plain,(
    ! [B_359,B_360] :
      ( m1_subset_1('#skF_2'('#skF_6',B_359),B_360)
      | ~ r1_tarski('#skF_3',B_360)
      | B_359 = '#skF_6'
      | k1_relat_1(B_359) != '#skF_3'
      | ~ v1_funct_1(B_359)
      | ~ v1_relat_1(B_359) ) ),
    inference(resolution,[status(thm)],[c_1913,c_406])).

tff(c_56,plain,(
    ! [E_47] :
      ( k1_funct_1('#skF_5',E_47) = k1_funct_1('#skF_6',E_47)
      | ~ m1_subset_1(E_47,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4343,plain,(
    ! [B_359] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_359)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_359))
      | ~ r1_tarski('#skF_3','#skF_3')
      | B_359 = '#skF_6'
      | k1_relat_1(B_359) != '#skF_3'
      | ~ v1_funct_1(B_359)
      | ~ v1_relat_1(B_359) ) ),
    inference(resolution,[status(thm)],[c_4276,c_56])).

tff(c_4830,plain,(
    ! [B_374] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_374)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_374))
      | B_374 = '#skF_6'
      | k1_relat_1(B_374) != '#skF_3'
      | ~ v1_funct_1(B_374)
      | ~ v1_relat_1(B_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_4343])).

tff(c_26,plain,(
    ! [B_21,A_17] :
      ( k1_funct_1(B_21,'#skF_2'(A_17,B_21)) != k1_funct_1(A_17,'#skF_2'(A_17,B_21))
      | B_21 = A_17
      | k1_relat_1(B_21) != k1_relat_1(A_17)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4837,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4830,c_26])).

tff(c_4844,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_68,c_839,c_177,c_62,c_839,c_846,c_4837])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4860,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4844,c_54])).

tff(c_4874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1068,c_4860])).

tff(c_4875,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4907,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4875,c_2])).

tff(c_4909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_4907])).

tff(c_4910,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_831])).

tff(c_4942,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4910,c_2])).

tff(c_4944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_4942])).

tff(c_4946,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_98,plain,(
    ! [B_52,A_53] :
      ( ~ v1_xboole_0(B_52)
      | B_52 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_4959,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4946,c_101])).

tff(c_4945,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_4952,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4945,c_101])).

tff(c_5001,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4959,c_4952])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4993,plain,(
    ! [A_7] : m1_subset_1('#skF_5',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4952,c_14])).

tff(c_5053,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_4993])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5366,plain,(
    ! [A_402,B_403,C_404,D_405] :
      ( r2_relset_1(A_402,B_403,C_404,C_404)
      | ~ m1_subset_1(D_405,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5978,plain,(
    ! [A_485,B_486,C_487] :
      ( r2_relset_1(A_485,B_486,C_487,C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486))) ) ),
    inference(resolution,[status(thm)],[c_12,c_5366])).

tff(c_5992,plain,(
    ! [A_485,B_486] : r2_relset_1(A_485,B_486,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5053,c_5978])).

tff(c_370,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_343])).

tff(c_5045,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4946,c_370])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4953,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4945,c_4])).

tff(c_5088,plain,(
    ! [A_384] :
      ( A_384 = '#skF_4'
      | ~ v1_xboole_0(A_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_4953])).

tff(c_5095,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5045,c_5088])).

tff(c_5016,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_54])).

tff(c_5187,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5095,c_5016])).

tff(c_5997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5992,c_5187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:52:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.52/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.26  
% 6.52/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.26  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 6.52/2.26  
% 6.52/2.26  %Foreground sorts:
% 6.52/2.26  
% 6.52/2.26  
% 6.52/2.26  %Background operators:
% 6.52/2.26  
% 6.52/2.26  
% 6.52/2.26  %Foreground operators:
% 6.52/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.52/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.52/2.26  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.52/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.52/2.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.52/2.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.52/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.52/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.52/2.26  tff('#skF_5', type, '#skF_5': $i).
% 6.52/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.52/2.26  tff('#skF_6', type, '#skF_6': $i).
% 6.52/2.26  tff('#skF_3', type, '#skF_3': $i).
% 6.52/2.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.52/2.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.52/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.52/2.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.52/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.52/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.52/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.52/2.26  tff('#skF_4', type, '#skF_4': $i).
% 6.52/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.52/2.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.52/2.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.52/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.52/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.52/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.52/2.26  
% 6.52/2.28  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 6.52/2.28  tff(f_100, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.52/2.28  tff(f_110, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.52/2.28  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.52/2.28  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.52/2.28  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.52/2.28  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.52/2.28  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.52/2.28  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 6.52/2.28  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 6.52/2.28  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.52/2.28  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.52/2.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.52/2.28  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.52/2.28  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.52/2.28  tff(f_43, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.52/2.28  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_343, plain, (![C_86, B_87, A_88]: (v1_xboole_0(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(B_87, A_88))) | ~v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.52/2.28  tff(c_369, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_343])).
% 6.52/2.28  tff(c_376, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_369])).
% 6.52/2.28  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_1000, plain, (![A_153, B_154, C_155, D_156]: (r2_relset_1(A_153, B_154, C_155, C_155) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.52/2.28  tff(c_1052, plain, (![C_165]: (r2_relset_1('#skF_3', '#skF_4', C_165, C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_64, c_1000])).
% 6.52/2.28  tff(c_1068, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_1052])).
% 6.52/2.28  tff(c_152, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.52/2.28  tff(c_176, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_152])).
% 6.52/2.28  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_578, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.52/2.28  tff(c_604, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_578])).
% 6.52/2.28  tff(c_803, plain, (![B_138, A_139, C_140]: (k1_xboole_0=B_138 | k1_relset_1(A_139, B_138, C_140)=A_139 | ~v1_funct_2(C_140, A_139, B_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.52/2.28  tff(c_810, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_803])).
% 6.52/2.28  tff(c_831, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_604, c_810])).
% 6.52/2.28  tff(c_839, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_831])).
% 6.52/2.28  tff(c_177, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_152])).
% 6.52/2.28  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_605, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_578])).
% 6.52/2.28  tff(c_813, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_803])).
% 6.52/2.28  tff(c_834, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_605, c_813])).
% 6.52/2.28  tff(c_846, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_834])).
% 6.52/2.28  tff(c_180, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.52/2.28  tff(c_206, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_180])).
% 6.52/2.28  tff(c_246, plain, (![B_76, A_77]: (k7_relat_1(B_76, A_77)=B_76 | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.52/2.28  tff(c_255, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_206, c_246])).
% 6.52/2.28  tff(c_264, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_255])).
% 6.52/2.28  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.52/2.28  tff(c_289, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_264, c_24])).
% 6.52/2.28  tff(c_293, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_289])).
% 6.52/2.28  tff(c_841, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_293])).
% 6.52/2.28  tff(c_1096, plain, (![A_170, B_171]: (r2_hidden('#skF_2'(A_170, B_171), k1_relat_1(A_170)) | B_171=A_170 | k1_relat_1(B_171)!=k1_relat_1(A_170) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.52/2.28  tff(c_1101, plain, (![B_171]: (r2_hidden('#skF_2'('#skF_6', B_171), '#skF_3') | B_171='#skF_6' | k1_relat_1(B_171)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_171) | ~v1_relat_1(B_171) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_846, c_1096])).
% 6.52/2.28  tff(c_1913, plain, (![B_244]: (r2_hidden('#skF_2'('#skF_6', B_244), '#skF_3') | B_244='#skF_6' | k1_relat_1(B_244)!='#skF_3' | ~v1_funct_1(B_244) | ~v1_relat_1(B_244))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_62, c_846, c_1101])).
% 6.52/2.28  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.52/2.28  tff(c_394, plain, (![A_90, C_91, B_92]: (m1_subset_1(A_90, C_91) | ~m1_subset_1(B_92, k1_zfmisc_1(C_91)) | ~r2_hidden(A_90, B_92))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.52/2.28  tff(c_406, plain, (![A_90, B_9, A_8]: (m1_subset_1(A_90, B_9) | ~r2_hidden(A_90, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_394])).
% 6.52/2.28  tff(c_4276, plain, (![B_359, B_360]: (m1_subset_1('#skF_2'('#skF_6', B_359), B_360) | ~r1_tarski('#skF_3', B_360) | B_359='#skF_6' | k1_relat_1(B_359)!='#skF_3' | ~v1_funct_1(B_359) | ~v1_relat_1(B_359))), inference(resolution, [status(thm)], [c_1913, c_406])).
% 6.52/2.28  tff(c_56, plain, (![E_47]: (k1_funct_1('#skF_5', E_47)=k1_funct_1('#skF_6', E_47) | ~m1_subset_1(E_47, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_4343, plain, (![B_359]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_359))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_359)) | ~r1_tarski('#skF_3', '#skF_3') | B_359='#skF_6' | k1_relat_1(B_359)!='#skF_3' | ~v1_funct_1(B_359) | ~v1_relat_1(B_359))), inference(resolution, [status(thm)], [c_4276, c_56])).
% 6.52/2.28  tff(c_4830, plain, (![B_374]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_374))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_374)) | B_374='#skF_6' | k1_relat_1(B_374)!='#skF_3' | ~v1_funct_1(B_374) | ~v1_relat_1(B_374))), inference(demodulation, [status(thm), theory('equality')], [c_841, c_4343])).
% 6.52/2.28  tff(c_26, plain, (![B_21, A_17]: (k1_funct_1(B_21, '#skF_2'(A_17, B_21))!=k1_funct_1(A_17, '#skF_2'(A_17, B_21)) | B_21=A_17 | k1_relat_1(B_21)!=k1_relat_1(A_17) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.52/2.28  tff(c_4837, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4830, c_26])).
% 6.52/2.28  tff(c_4844, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_68, c_839, c_177, c_62, c_839, c_846, c_4837])).
% 6.52/2.28  tff(c_54, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.52/2.28  tff(c_4860, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4844, c_54])).
% 6.52/2.28  tff(c_4874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1068, c_4860])).
% 6.52/2.28  tff(c_4875, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_834])).
% 6.52/2.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.52/2.28  tff(c_4907, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4875, c_2])).
% 6.52/2.28  tff(c_4909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_4907])).
% 6.52/2.28  tff(c_4910, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_831])).
% 6.52/2.28  tff(c_4942, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4910, c_2])).
% 6.52/2.28  tff(c_4944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_4942])).
% 6.52/2.28  tff(c_4946, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_369])).
% 6.52/2.28  tff(c_98, plain, (![B_52, A_53]: (~v1_xboole_0(B_52) | B_52=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.52/2.28  tff(c_101, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_2, c_98])).
% 6.52/2.28  tff(c_4959, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4946, c_101])).
% 6.52/2.28  tff(c_4945, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_369])).
% 6.52/2.28  tff(c_4952, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4945, c_101])).
% 6.52/2.28  tff(c_5001, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4959, c_4952])).
% 6.52/2.28  tff(c_14, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.52/2.28  tff(c_4993, plain, (![A_7]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_4952, c_14])).
% 6.52/2.28  tff(c_5053, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_4993])).
% 6.52/2.28  tff(c_12, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.52/2.28  tff(c_5366, plain, (![A_402, B_403, C_404, D_405]: (r2_relset_1(A_402, B_403, C_404, C_404) | ~m1_subset_1(D_405, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.52/2.28  tff(c_5978, plain, (![A_485, B_486, C_487]: (r2_relset_1(A_485, B_486, C_487, C_487) | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))))), inference(resolution, [status(thm)], [c_12, c_5366])).
% 6.52/2.28  tff(c_5992, plain, (![A_485, B_486]: (r2_relset_1(A_485, B_486, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_5053, c_5978])).
% 6.52/2.28  tff(c_370, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_343])).
% 6.52/2.28  tff(c_5045, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4946, c_370])).
% 6.52/2.28  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.52/2.28  tff(c_4953, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4945, c_4])).
% 6.52/2.28  tff(c_5088, plain, (![A_384]: (A_384='#skF_4' | ~v1_xboole_0(A_384))), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_4953])).
% 6.52/2.28  tff(c_5095, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_5045, c_5088])).
% 6.52/2.28  tff(c_5016, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_54])).
% 6.52/2.28  tff(c_5187, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5095, c_5016])).
% 6.52/2.28  tff(c_5997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5992, c_5187])).
% 6.52/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.28  
% 6.52/2.28  Inference rules
% 6.52/2.28  ----------------------
% 6.52/2.28  #Ref     : 2
% 6.52/2.28  #Sup     : 1367
% 6.52/2.28  #Fact    : 0
% 6.52/2.28  #Define  : 0
% 6.52/2.28  #Split   : 17
% 6.52/2.28  #Chain   : 0
% 6.52/2.28  #Close   : 0
% 6.52/2.28  
% 6.52/2.28  Ordering : KBO
% 6.52/2.28  
% 6.52/2.28  Simplification rules
% 6.52/2.28  ----------------------
% 6.52/2.28  #Subsume      : 442
% 6.52/2.28  #Demod        : 1446
% 6.52/2.28  #Tautology    : 540
% 6.52/2.28  #SimpNegUnit  : 41
% 6.52/2.28  #BackRed      : 150
% 6.52/2.28  
% 6.52/2.28  #Partial instantiations: 0
% 6.52/2.28  #Strategies tried      : 1
% 6.52/2.28  
% 6.52/2.28  Timing (in seconds)
% 6.52/2.28  ----------------------
% 6.52/2.28  Preprocessing        : 0.34
% 6.52/2.28  Parsing              : 0.18
% 6.52/2.28  CNF conversion       : 0.02
% 6.52/2.28  Main loop            : 1.18
% 6.52/2.28  Inferencing          : 0.38
% 6.52/2.28  Reduction            : 0.43
% 6.52/2.28  Demodulation         : 0.31
% 6.52/2.28  BG Simplification    : 0.04
% 6.52/2.28  Subsumption          : 0.23
% 6.52/2.28  Abstraction          : 0.05
% 6.52/2.28  MUC search           : 0.00
% 6.52/2.28  Cooper               : 0.00
% 6.52/2.28  Total                : 1.56
% 6.52/2.28  Index Insertion      : 0.00
% 6.52/2.28  Index Deletion       : 0.00
% 6.52/2.28  Index Matching       : 0.00
% 6.52/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
