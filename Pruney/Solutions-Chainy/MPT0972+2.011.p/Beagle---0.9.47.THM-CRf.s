%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:36 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  127 (1420 expanded)
%              Number of leaves         :   37 ( 505 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 (5002 expanded)
%              Number of equality atoms :   84 (1709 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_73,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_123,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_138,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_123])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2810,plain,(
    ! [A_327,B_328,C_329,D_330] :
      ( r2_relset_1(A_327,B_328,C_329,C_329)
      | ~ m1_subset_1(D_330,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328)))
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2826,plain,(
    ! [C_331] :
      ( r2_relset_1('#skF_4','#skF_5',C_331,C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_58,c_2810])).

tff(c_2835,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_2826])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2459,plain,(
    ! [A_287,B_288,C_289] :
      ( k1_relset_1(A_287,B_288,C_289) = k1_relat_1(C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2476,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_2459])).

tff(c_2618,plain,(
    ! [B_312,A_313,C_314] :
      ( k1_xboole_0 = B_312
      | k1_relset_1(A_313,B_312,C_314) = A_313
      | ~ v1_funct_2(C_314,A_313,B_312)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_313,B_312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2621,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2618])).

tff(c_2637,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2476,c_2621])).

tff(c_2643,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2637])).

tff(c_139,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_123])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2477,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_2459])).

tff(c_2624,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2618])).

tff(c_2640,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2477,c_2624])).

tff(c_2664,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2640])).

tff(c_2872,plain,(
    ! [A_341,B_342] :
      ( r2_hidden('#skF_3'(A_341,B_342),k1_relat_1(A_341))
      | B_342 = A_341
      | k1_relat_1(B_342) != k1_relat_1(A_341)
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342)
      | ~ v1_funct_1(A_341)
      | ~ v1_relat_1(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2877,plain,(
    ! [B_342] :
      ( r2_hidden('#skF_3'('#skF_6',B_342),'#skF_4')
      | B_342 = '#skF_6'
      | k1_relat_1(B_342) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2664,c_2872])).

tff(c_3226,plain,(
    ! [B_374] :
      ( r2_hidden('#skF_3'('#skF_6',B_374),'#skF_4')
      | B_374 = '#skF_6'
      | k1_relat_1(B_374) != '#skF_4'
      | ~ v1_funct_1(B_374)
      | ~ v1_relat_1(B_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_68,c_2664,c_2877])).

tff(c_56,plain,(
    ! [E_41] :
      ( k1_funct_1('#skF_7',E_41) = k1_funct_1('#skF_6',E_41)
      | ~ r2_hidden(E_41,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3664,plain,(
    ! [B_399] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_399)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_399))
      | B_399 = '#skF_6'
      | k1_relat_1(B_399) != '#skF_4'
      | ~ v1_funct_1(B_399)
      | ~ v1_relat_1(B_399) ) ),
    inference(resolution,[status(thm)],[c_3226,c_56])).

tff(c_28,plain,(
    ! [B_19,A_15] :
      ( k1_funct_1(B_19,'#skF_3'(A_15,B_19)) != k1_funct_1(A_15,'#skF_3'(A_15,B_19))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3671,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3664,c_28])).

tff(c_3678,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_62,c_2643,c_139,c_68,c_2664,c_2643,c_3671])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3698,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3678,c_54])).

tff(c_3710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2835,c_3698])).

tff(c_3712,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2640])).

tff(c_3711,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2640])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3738,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3711,c_3711,c_18])).

tff(c_3780,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3738,c_64])).

tff(c_178,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_190,plain,(
    ! [C_63,A_9] :
      ( v4_relat_1(C_63,A_9)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_178])).

tff(c_4024,plain,(
    ! [C_431,A_432] :
      ( v4_relat_1(C_431,A_432)
      | ~ m1_subset_1(C_431,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3711,c_190])).

tff(c_4034,plain,(
    ! [A_432] : v4_relat_1('#skF_6',A_432) ),
    inference(resolution,[status(thm)],[c_3780,c_4024])).

tff(c_3779,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3738,c_58])).

tff(c_4035,plain,(
    ! [A_432] : v4_relat_1('#skF_7',A_432) ),
    inference(resolution,[status(thm)],[c_3779,c_4024])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2654,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_4',A_13)
      | ~ v4_relat_1('#skF_7',A_13)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2643,c_26])).

tff(c_2662,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_4',A_13)
      | ~ v4_relat_1('#skF_7',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2654])).

tff(c_4059,plain,(
    ! [A_437] : r1_tarski('#skF_4',A_437) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_2662])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_3736,plain,(
    ! [A_8] :
      ( A_8 = '#skF_5'
      | ~ r1_tarski(A_8,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3711,c_3711,c_108])).

tff(c_4066,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4059,c_3736])).

tff(c_233,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_240,plain,(
    ! [B_76] :
      ( k1_relat_1(B_76) = k1_xboole_0
      | ~ v4_relat_1(B_76,k1_xboole_0)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_233,c_108])).

tff(c_3730,plain,(
    ! [B_76] :
      ( k1_relat_1(B_76) = '#skF_5'
      | ~ v4_relat_1(B_76,'#skF_5')
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3711,c_3711,c_240])).

tff(c_4578,plain,(
    ! [B_478] :
      ( k1_relat_1(B_478) = '#skF_4'
      | ~ v4_relat_1(B_478,'#skF_4')
      | ~ v1_relat_1(B_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4066,c_4066,c_3730])).

tff(c_4594,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4034,c_4578])).

tff(c_4610,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_4594])).

tff(c_4612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3712,c_4610])).

tff(c_4613,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_4640,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_4613,c_18])).

tff(c_4678,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4640,c_58])).

tff(c_4892,plain,(
    ! [C_507,A_508] :
      ( v4_relat_1(C_507,A_508)
      | ~ m1_subset_1(C_507,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_190])).

tff(c_4903,plain,(
    ! [A_508] : v4_relat_1('#skF_7',A_508) ),
    inference(resolution,[status(thm)],[c_4678,c_4892])).

tff(c_4762,plain,(
    ! [A_491] :
      ( A_491 = '#skF_5'
      | ~ r1_tarski(A_491,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_4613,c_108])).

tff(c_4946,plain,(
    ! [B_515] :
      ( k1_relat_1(B_515) = '#skF_5'
      | ~ v4_relat_1(B_515,'#skF_5')
      | ~ v1_relat_1(B_515) ) ),
    inference(resolution,[status(thm)],[c_26,c_4762])).

tff(c_4950,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4903,c_4946])).

tff(c_4969,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_4950])).

tff(c_4614,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_4982,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4969,c_4614])).

tff(c_4679,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4640,c_64])).

tff(c_44,plain,(
    ! [C_36,A_34] :
      ( k1_xboole_0 = C_36
      | ~ v1_funct_2(C_36,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_72,plain,(
    ! [C_36,A_34] :
      ( k1_xboole_0 = C_36
      | ~ v1_funct_2(C_36,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_44])).

tff(c_5256,plain,(
    ! [C_550,A_551] :
      ( C_550 = '#skF_5'
      | ~ v1_funct_2(C_550,A_551,'#skF_5')
      | A_551 = '#skF_5'
      | ~ m1_subset_1(C_550,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_4613,c_4613,c_4613,c_72])).

tff(c_5271,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_5256])).

tff(c_5294,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4679,c_5271])).

tff(c_5295,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_4982,c_5294])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1('#skF_2'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4746,plain,(
    ! [A_486,B_487,C_488,D_489] :
      ( r2_relset_1(A_486,B_487,C_488,C_488)
      | ~ m1_subset_1(D_489,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487)))
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5152,plain,(
    ! [A_531,B_532,C_533] :
      ( r2_relset_1(A_531,B_532,C_533,C_533)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532))) ) ),
    inference(resolution,[status(thm)],[c_22,c_4746])).

tff(c_5215,plain,(
    ! [A_541,C_542] :
      ( r2_relset_1(A_541,'#skF_5',C_542,C_542)
      | ~ m1_subset_1(C_542,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4640,c_5152])).

tff(c_5225,plain,(
    ! [A_541] : r2_relset_1(A_541,'#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_4679,c_5215])).

tff(c_5332,plain,(
    ! [A_541] : r2_relset_1(A_541,'#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_5225])).

tff(c_5269,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_5256])).

tff(c_5290,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4678,c_5269])).

tff(c_5291,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_4982,c_5290])).

tff(c_5310,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5291,c_54])).

tff(c_5521,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_5295,c_5310])).

tff(c_5545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5332,c_5521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:48:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.19  
% 5.80/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1
% 5.80/2.19  
% 5.80/2.19  %Foreground sorts:
% 5.80/2.19  
% 5.80/2.19  
% 5.80/2.19  %Background operators:
% 5.80/2.19  
% 5.80/2.19  
% 5.80/2.19  %Foreground operators:
% 5.80/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.80/2.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.80/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.80/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.80/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.80/2.19  tff('#skF_7', type, '#skF_7': $i).
% 5.80/2.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.80/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.19  tff('#skF_5', type, '#skF_5': $i).
% 5.80/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.80/2.19  tff('#skF_6', type, '#skF_6': $i).
% 5.80/2.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.80/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.80/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.80/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.80/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.80/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.80/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.80/2.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.80/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.80/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.19  
% 5.80/2.21  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 5.80/2.21  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.80/2.21  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.80/2.21  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.80/2.21  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.80/2.21  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.80/2.21  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.80/2.21  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.80/2.21  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.80/2.21  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.80/2.21  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.80/2.21  tff(f_49, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.80/2.21  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_123, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.80/2.21  tff(c_138, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_123])).
% 5.80/2.21  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_2810, plain, (![A_327, B_328, C_329, D_330]: (r2_relset_1(A_327, B_328, C_329, C_329) | ~m1_subset_1(D_330, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.80/2.21  tff(c_2826, plain, (![C_331]: (r2_relset_1('#skF_4', '#skF_5', C_331, C_331) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_58, c_2810])).
% 5.80/2.21  tff(c_2835, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_2826])).
% 5.80/2.21  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_2459, plain, (![A_287, B_288, C_289]: (k1_relset_1(A_287, B_288, C_289)=k1_relat_1(C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.80/2.21  tff(c_2476, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_2459])).
% 5.80/2.21  tff(c_2618, plain, (![B_312, A_313, C_314]: (k1_xboole_0=B_312 | k1_relset_1(A_313, B_312, C_314)=A_313 | ~v1_funct_2(C_314, A_313, B_312) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_313, B_312))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.21  tff(c_2621, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_2618])).
% 5.80/2.21  tff(c_2637, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2476, c_2621])).
% 5.80/2.21  tff(c_2643, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_2637])).
% 5.80/2.21  tff(c_139, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_123])).
% 5.80/2.21  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_2477, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_2459])).
% 5.80/2.21  tff(c_2624, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_2618])).
% 5.80/2.21  tff(c_2640, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2477, c_2624])).
% 5.80/2.21  tff(c_2664, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2640])).
% 5.80/2.21  tff(c_2872, plain, (![A_341, B_342]: (r2_hidden('#skF_3'(A_341, B_342), k1_relat_1(A_341)) | B_342=A_341 | k1_relat_1(B_342)!=k1_relat_1(A_341) | ~v1_funct_1(B_342) | ~v1_relat_1(B_342) | ~v1_funct_1(A_341) | ~v1_relat_1(A_341))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.80/2.21  tff(c_2877, plain, (![B_342]: (r2_hidden('#skF_3'('#skF_6', B_342), '#skF_4') | B_342='#skF_6' | k1_relat_1(B_342)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_342) | ~v1_relat_1(B_342) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2664, c_2872])).
% 5.80/2.21  tff(c_3226, plain, (![B_374]: (r2_hidden('#skF_3'('#skF_6', B_374), '#skF_4') | B_374='#skF_6' | k1_relat_1(B_374)!='#skF_4' | ~v1_funct_1(B_374) | ~v1_relat_1(B_374))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_68, c_2664, c_2877])).
% 5.80/2.21  tff(c_56, plain, (![E_41]: (k1_funct_1('#skF_7', E_41)=k1_funct_1('#skF_6', E_41) | ~r2_hidden(E_41, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_3664, plain, (![B_399]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_399))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_399)) | B_399='#skF_6' | k1_relat_1(B_399)!='#skF_4' | ~v1_funct_1(B_399) | ~v1_relat_1(B_399))), inference(resolution, [status(thm)], [c_3226, c_56])).
% 5.80/2.21  tff(c_28, plain, (![B_19, A_15]: (k1_funct_1(B_19, '#skF_3'(A_15, B_19))!=k1_funct_1(A_15, '#skF_3'(A_15, B_19)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.80/2.21  tff(c_3671, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3664, c_28])).
% 5.80/2.21  tff(c_3678, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_62, c_2643, c_139, c_68, c_2664, c_2643, c_3671])).
% 5.80/2.21  tff(c_54, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.80/2.21  tff(c_3698, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3678, c_54])).
% 5.80/2.21  tff(c_3710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2835, c_3698])).
% 5.80/2.21  tff(c_3712, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitRight, [status(thm)], [c_2640])).
% 5.80/2.21  tff(c_3711, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2640])).
% 5.80/2.21  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.80/2.21  tff(c_3738, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3711, c_3711, c_18])).
% 5.80/2.21  tff(c_3780, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3738, c_64])).
% 5.80/2.21  tff(c_178, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.80/2.21  tff(c_190, plain, (![C_63, A_9]: (v4_relat_1(C_63, A_9) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_178])).
% 5.80/2.21  tff(c_4024, plain, (![C_431, A_432]: (v4_relat_1(C_431, A_432) | ~m1_subset_1(C_431, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_3711, c_190])).
% 5.80/2.21  tff(c_4034, plain, (![A_432]: (v4_relat_1('#skF_6', A_432))), inference(resolution, [status(thm)], [c_3780, c_4024])).
% 5.80/2.21  tff(c_3779, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3738, c_58])).
% 5.80/2.21  tff(c_4035, plain, (![A_432]: (v4_relat_1('#skF_7', A_432))), inference(resolution, [status(thm)], [c_3779, c_4024])).
% 5.80/2.21  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.80/2.21  tff(c_2654, plain, (![A_13]: (r1_tarski('#skF_4', A_13) | ~v4_relat_1('#skF_7', A_13) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2643, c_26])).
% 5.80/2.21  tff(c_2662, plain, (![A_13]: (r1_tarski('#skF_4', A_13) | ~v4_relat_1('#skF_7', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_2654])).
% 5.80/2.21  tff(c_4059, plain, (![A_437]: (r1_tarski('#skF_4', A_437))), inference(demodulation, [status(thm), theory('equality')], [c_4035, c_2662])).
% 5.80/2.21  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.80/2.21  tff(c_99, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.80/2.21  tff(c_108, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_99])).
% 5.80/2.21  tff(c_3736, plain, (![A_8]: (A_8='#skF_5' | ~r1_tarski(A_8, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3711, c_3711, c_108])).
% 5.80/2.21  tff(c_4066, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4059, c_3736])).
% 5.80/2.21  tff(c_233, plain, (![B_76, A_77]: (r1_tarski(k1_relat_1(B_76), A_77) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.80/2.21  tff(c_240, plain, (![B_76]: (k1_relat_1(B_76)=k1_xboole_0 | ~v4_relat_1(B_76, k1_xboole_0) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_233, c_108])).
% 5.80/2.21  tff(c_3730, plain, (![B_76]: (k1_relat_1(B_76)='#skF_5' | ~v4_relat_1(B_76, '#skF_5') | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_3711, c_3711, c_240])).
% 5.80/2.21  tff(c_4578, plain, (![B_478]: (k1_relat_1(B_478)='#skF_4' | ~v4_relat_1(B_478, '#skF_4') | ~v1_relat_1(B_478))), inference(demodulation, [status(thm), theory('equality')], [c_4066, c_4066, c_3730])).
% 5.80/2.21  tff(c_4594, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4034, c_4578])).
% 5.80/2.21  tff(c_4610, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_4594])).
% 5.80/2.21  tff(c_4612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3712, c_4610])).
% 5.80/2.21  tff(c_4613, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2637])).
% 5.80/2.21  tff(c_4640, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_4613, c_18])).
% 5.80/2.21  tff(c_4678, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4640, c_58])).
% 5.80/2.21  tff(c_4892, plain, (![C_507, A_508]: (v4_relat_1(C_507, A_508) | ~m1_subset_1(C_507, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_190])).
% 5.80/2.21  tff(c_4903, plain, (![A_508]: (v4_relat_1('#skF_7', A_508))), inference(resolution, [status(thm)], [c_4678, c_4892])).
% 5.80/2.21  tff(c_4762, plain, (![A_491]: (A_491='#skF_5' | ~r1_tarski(A_491, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_4613, c_108])).
% 5.80/2.21  tff(c_4946, plain, (![B_515]: (k1_relat_1(B_515)='#skF_5' | ~v4_relat_1(B_515, '#skF_5') | ~v1_relat_1(B_515))), inference(resolution, [status(thm)], [c_26, c_4762])).
% 5.80/2.21  tff(c_4950, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4903, c_4946])).
% 5.80/2.21  tff(c_4969, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_4950])).
% 5.80/2.21  tff(c_4614, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_2637])).
% 5.80/2.21  tff(c_4982, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4969, c_4614])).
% 5.80/2.21  tff(c_4679, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4640, c_64])).
% 5.80/2.21  tff(c_44, plain, (![C_36, A_34]: (k1_xboole_0=C_36 | ~v1_funct_2(C_36, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.21  tff(c_72, plain, (![C_36, A_34]: (k1_xboole_0=C_36 | ~v1_funct_2(C_36, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_44])).
% 5.80/2.21  tff(c_5256, plain, (![C_550, A_551]: (C_550='#skF_5' | ~v1_funct_2(C_550, A_551, '#skF_5') | A_551='#skF_5' | ~m1_subset_1(C_550, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_4613, c_4613, c_4613, c_72])).
% 5.80/2.21  tff(c_5271, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_5256])).
% 5.80/2.21  tff(c_5294, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4679, c_5271])).
% 5.80/2.21  tff(c_5295, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_4982, c_5294])).
% 5.80/2.21  tff(c_22, plain, (![A_11]: (m1_subset_1('#skF_2'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.80/2.21  tff(c_4746, plain, (![A_486, B_487, C_488, D_489]: (r2_relset_1(A_486, B_487, C_488, C_488) | ~m1_subset_1(D_489, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.80/2.21  tff(c_5152, plain, (![A_531, B_532, C_533]: (r2_relset_1(A_531, B_532, C_533, C_533) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_531, B_532))))), inference(resolution, [status(thm)], [c_22, c_4746])).
% 5.80/2.21  tff(c_5215, plain, (![A_541, C_542]: (r2_relset_1(A_541, '#skF_5', C_542, C_542) | ~m1_subset_1(C_542, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4640, c_5152])).
% 5.80/2.21  tff(c_5225, plain, (![A_541]: (r2_relset_1(A_541, '#skF_5', '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_4679, c_5215])).
% 5.80/2.21  tff(c_5332, plain, (![A_541]: (r2_relset_1(A_541, '#skF_6', '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_5225])).
% 5.80/2.21  tff(c_5269, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_5256])).
% 5.80/2.21  tff(c_5290, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4678, c_5269])).
% 5.80/2.21  tff(c_5291, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_4982, c_5290])).
% 5.80/2.21  tff(c_5310, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5291, c_54])).
% 5.80/2.21  tff(c_5521, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_5295, c_5310])).
% 5.80/2.21  tff(c_5545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5332, c_5521])).
% 5.80/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.21  
% 5.80/2.21  Inference rules
% 5.80/2.21  ----------------------
% 5.80/2.21  #Ref     : 6
% 5.80/2.21  #Sup     : 1133
% 5.80/2.21  #Fact    : 0
% 5.80/2.21  #Define  : 0
% 5.80/2.21  #Split   : 11
% 5.80/2.21  #Chain   : 0
% 5.80/2.21  #Close   : 0
% 5.80/2.21  
% 5.80/2.21  Ordering : KBO
% 5.80/2.21  
% 5.80/2.21  Simplification rules
% 5.80/2.21  ----------------------
% 5.80/2.21  #Subsume      : 190
% 5.80/2.21  #Demod        : 1504
% 5.80/2.21  #Tautology    : 719
% 5.80/2.21  #SimpNegUnit  : 7
% 5.80/2.21  #BackRed      : 301
% 5.80/2.21  
% 5.80/2.21  #Partial instantiations: 0
% 5.80/2.21  #Strategies tried      : 1
% 5.80/2.21  
% 5.80/2.21  Timing (in seconds)
% 5.80/2.21  ----------------------
% 5.80/2.22  Preprocessing        : 0.35
% 5.80/2.22  Parsing              : 0.18
% 5.80/2.22  CNF conversion       : 0.02
% 5.80/2.22  Main loop            : 1.09
% 5.80/2.22  Inferencing          : 0.36
% 5.80/2.22  Reduction            : 0.41
% 5.80/2.22  Demodulation         : 0.30
% 5.80/2.22  BG Simplification    : 0.04
% 5.80/2.22  Subsumption          : 0.18
% 5.80/2.22  Abstraction          : 0.04
% 5.80/2.22  MUC search           : 0.00
% 5.80/2.22  Cooper               : 0.00
% 5.80/2.22  Total                : 1.49
% 5.80/2.22  Index Insertion      : 0.00
% 5.80/2.22  Index Deletion       : 0.00
% 5.80/2.22  Index Matching       : 0.00
% 5.80/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
