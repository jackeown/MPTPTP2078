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
% DateTime   : Thu Dec  3 10:11:35 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 318 expanded)
%              Number of leaves         :   40 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 962 expanded)
%              Number of equality atoms :   53 ( 207 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2909,plain,(
    ! [C_310,B_311,A_312] :
      ( v1_xboole_0(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(B_311,A_312)))
      | ~ v1_xboole_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2920,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_2909])).

tff(c_2923,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2920])).

tff(c_60,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3704,plain,(
    ! [A_401,B_402,C_403,D_404] :
      ( r2_relset_1(A_401,B_402,C_403,C_403)
      | ~ m1_subset_1(D_404,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402)))
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3798,plain,(
    ! [C_408] :
      ( r2_relset_1('#skF_7','#skF_8',C_408,C_408)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_3704])).

tff(c_3810,plain,(
    r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_66,c_3798])).

tff(c_91,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_64,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2924,plain,(
    ! [A_313,B_314,C_315] :
      ( k1_relset_1(A_313,B_314,C_315) = k1_relat_1(C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2936,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_2924])).

tff(c_3851,plain,(
    ! [B_413,A_414,C_415] :
      ( k1_xboole_0 = B_413
      | k1_relset_1(A_414,B_413,C_415) = A_414
      | ~ v1_funct_2(C_415,A_414,B_413)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_414,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3860,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_3851])).

tff(c_3871,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2936,c_3860])).

tff(c_3924,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3871])).

tff(c_102,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_66,c_91])).

tff(c_70,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2935,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_66,c_2924])).

tff(c_3857,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_3851])).

tff(c_3868,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2935,c_3857])).

tff(c_3873,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3868])).

tff(c_4098,plain,(
    ! [A_425,B_426] :
      ( r2_hidden('#skF_6'(A_425,B_426),k1_relat_1(A_425))
      | B_426 = A_425
      | k1_relat_1(B_426) != k1_relat_1(A_425)
      | ~ v1_funct_1(B_426)
      | ~ v1_relat_1(B_426)
      | ~ v1_funct_1(A_425)
      | ~ v1_relat_1(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4109,plain,(
    ! [B_426] :
      ( r2_hidden('#skF_6'('#skF_9',B_426),'#skF_7')
      | B_426 = '#skF_9'
      | k1_relat_1(B_426) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_426)
      | ~ v1_relat_1(B_426)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3873,c_4098])).

tff(c_6466,plain,(
    ! [B_569] :
      ( r2_hidden('#skF_6'('#skF_9',B_569),'#skF_7')
      | B_569 = '#skF_9'
      | k1_relat_1(B_569) != '#skF_7'
      | ~ v1_funct_1(B_569)
      | ~ v1_relat_1(B_569) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_70,c_3873,c_4109])).

tff(c_58,plain,(
    ! [E_47] :
      ( k1_funct_1('#skF_10',E_47) = k1_funct_1('#skF_9',E_47)
      | ~ r2_hidden(E_47,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7201,plain,(
    ! [B_597] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_9',B_597)) = k1_funct_1('#skF_9','#skF_6'('#skF_9',B_597))
      | B_597 = '#skF_9'
      | k1_relat_1(B_597) != '#skF_7'
      | ~ v1_funct_1(B_597)
      | ~ v1_relat_1(B_597) ) ),
    inference(resolution,[status(thm)],[c_6466,c_58])).

tff(c_28,plain,(
    ! [B_21,A_17] :
      ( k1_funct_1(B_21,'#skF_6'(A_17,B_21)) != k1_funct_1(A_17,'#skF_6'(A_17,B_21))
      | B_21 = A_17
      | k1_relat_1(B_21) != k1_relat_1(A_17)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7208,plain,
    ( k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_7201,c_28])).

tff(c_7215,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_64,c_3924,c_102,c_70,c_3873,c_3924,c_7208])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7248,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7215,c_56])).

tff(c_7260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3810,c_7248])).

tff(c_7261,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3871])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7289,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7261,c_12])).

tff(c_7291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2923,c_7289])).

tff(c_7292,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3868])).

tff(c_7319,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7292,c_12])).

tff(c_7321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2923,c_7319])).

tff(c_7323,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2920])).

tff(c_2921,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_2909])).

tff(c_7339,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7323,c_2921])).

tff(c_7348,plain,(
    ! [A_601,B_602] :
      ( r2_hidden('#skF_3'(A_601,B_602),B_602)
      | r2_hidden('#skF_4'(A_601,B_602),A_601)
      | B_602 = A_601 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7397,plain,(
    ! [B_609,A_610] :
      ( ~ v1_xboole_0(B_609)
      | r2_hidden('#skF_4'(A_610,B_609),A_610)
      | B_609 = A_610 ) ),
    inference(resolution,[status(thm)],[c_7348,c_2])).

tff(c_7410,plain,(
    ! [A_611,B_612] :
      ( ~ v1_xboole_0(A_611)
      | ~ v1_xboole_0(B_612)
      | B_612 = A_611 ) ),
    inference(resolution,[status(thm)],[c_7397,c_2])).

tff(c_7432,plain,(
    ! [B_615] :
      ( ~ v1_xboole_0(B_615)
      | B_615 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_7339,c_7410])).

tff(c_7451,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7323,c_7432])).

tff(c_7322,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2920])).

tff(c_7452,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7322,c_7432])).

tff(c_7472,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7451,c_7452])).

tff(c_7464,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7451,c_56])).

tff(c_7525,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7472,c_7464])).

tff(c_7463,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7451,c_60])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1('#skF_5'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7977,plain,(
    ! [A_672,B_673,C_674,D_675] :
      ( r2_relset_1(A_672,B_673,C_674,C_674)
      | ~ m1_subset_1(D_675,k1_zfmisc_1(k2_zfmisc_1(A_672,B_673)))
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(A_672,B_673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7987,plain,(
    ! [A_676,B_677,C_678] :
      ( r2_relset_1(A_676,B_677,C_678,C_678)
      | ~ m1_subset_1(C_678,k1_zfmisc_1(k2_zfmisc_1(A_676,B_677))) ) ),
    inference(resolution,[status(thm)],[c_22,c_7977])).

tff(c_7991,plain,(
    r2_relset_1('#skF_7','#skF_8','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_7463,c_7987])).

tff(c_7999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7525,c_7991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:29:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.67  
% 7.59/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.67  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 7.59/2.67  
% 7.59/2.67  %Foreground sorts:
% 7.59/2.67  
% 7.59/2.67  
% 7.59/2.67  %Background operators:
% 7.59/2.67  
% 7.59/2.67  
% 7.59/2.67  %Foreground operators:
% 7.59/2.67  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.59/2.67  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.59/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.59/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.59/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.59/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.59/2.67  tff('#skF_7', type, '#skF_7': $i).
% 7.59/2.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.59/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.59/2.67  tff('#skF_10', type, '#skF_10': $i).
% 7.59/2.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.59/2.67  tff('#skF_9', type, '#skF_9': $i).
% 7.59/2.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.59/2.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.59/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.59/2.67  tff('#skF_8', type, '#skF_8': $i).
% 7.59/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.59/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.59/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.59/2.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.59/2.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.59/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.59/2.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.59/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.59/2.67  
% 7.59/2.68  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 7.59/2.68  tff(f_90, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.59/2.68  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 7.59/2.68  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.59/2.68  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.59/2.68  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.59/2.68  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 7.59/2.68  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.59/2.68  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 7.59/2.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.59/2.68  tff(f_49, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.59/2.68  tff(c_66, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_2909, plain, (![C_310, B_311, A_312]: (v1_xboole_0(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(B_311, A_312))) | ~v1_xboole_0(A_312))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.59/2.68  tff(c_2920, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_66, c_2909])).
% 7.59/2.68  tff(c_2923, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_2920])).
% 7.59/2.68  tff(c_60, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_3704, plain, (![A_401, B_402, C_403, D_404]: (r2_relset_1(A_401, B_402, C_403, C_403) | ~m1_subset_1(D_404, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.59/2.68  tff(c_3798, plain, (![C_408]: (r2_relset_1('#skF_7', '#skF_8', C_408, C_408) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))))), inference(resolution, [status(thm)], [c_60, c_3704])).
% 7.59/2.68  tff(c_3810, plain, (r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_66, c_3798])).
% 7.59/2.68  tff(c_91, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.59/2.68  tff(c_103, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_91])).
% 7.59/2.68  tff(c_64, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_62, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_2924, plain, (![A_313, B_314, C_315]: (k1_relset_1(A_313, B_314, C_315)=k1_relat_1(C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.59/2.68  tff(c_2936, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_2924])).
% 7.59/2.68  tff(c_3851, plain, (![B_413, A_414, C_415]: (k1_xboole_0=B_413 | k1_relset_1(A_414, B_413, C_415)=A_414 | ~v1_funct_2(C_415, A_414, B_413) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_414, B_413))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.59/2.68  tff(c_3860, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_3851])).
% 7.59/2.68  tff(c_3871, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2936, c_3860])).
% 7.59/2.68  tff(c_3924, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_3871])).
% 7.59/2.68  tff(c_102, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_66, c_91])).
% 7.59/2.68  tff(c_70, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_68, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_2935, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_66, c_2924])).
% 7.59/2.68  tff(c_3857, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_66, c_3851])).
% 7.59/2.68  tff(c_3868, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2935, c_3857])).
% 7.59/2.68  tff(c_3873, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_3868])).
% 7.59/2.68  tff(c_4098, plain, (![A_425, B_426]: (r2_hidden('#skF_6'(A_425, B_426), k1_relat_1(A_425)) | B_426=A_425 | k1_relat_1(B_426)!=k1_relat_1(A_425) | ~v1_funct_1(B_426) | ~v1_relat_1(B_426) | ~v1_funct_1(A_425) | ~v1_relat_1(A_425))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.59/2.68  tff(c_4109, plain, (![B_426]: (r2_hidden('#skF_6'('#skF_9', B_426), '#skF_7') | B_426='#skF_9' | k1_relat_1(B_426)!=k1_relat_1('#skF_9') | ~v1_funct_1(B_426) | ~v1_relat_1(B_426) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3873, c_4098])).
% 7.59/2.68  tff(c_6466, plain, (![B_569]: (r2_hidden('#skF_6'('#skF_9', B_569), '#skF_7') | B_569='#skF_9' | k1_relat_1(B_569)!='#skF_7' | ~v1_funct_1(B_569) | ~v1_relat_1(B_569))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_70, c_3873, c_4109])).
% 7.59/2.68  tff(c_58, plain, (![E_47]: (k1_funct_1('#skF_10', E_47)=k1_funct_1('#skF_9', E_47) | ~r2_hidden(E_47, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_7201, plain, (![B_597]: (k1_funct_1('#skF_10', '#skF_6'('#skF_9', B_597))=k1_funct_1('#skF_9', '#skF_6'('#skF_9', B_597)) | B_597='#skF_9' | k1_relat_1(B_597)!='#skF_7' | ~v1_funct_1(B_597) | ~v1_relat_1(B_597))), inference(resolution, [status(thm)], [c_6466, c_58])).
% 7.59/2.68  tff(c_28, plain, (![B_21, A_17]: (k1_funct_1(B_21, '#skF_6'(A_17, B_21))!=k1_funct_1(A_17, '#skF_6'(A_17, B_21)) | B_21=A_17 | k1_relat_1(B_21)!=k1_relat_1(A_17) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.59/2.68  tff(c_7208, plain, (k1_relat_1('#skF_10')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | '#skF_10'='#skF_9' | k1_relat_1('#skF_10')!='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_7201, c_28])).
% 7.59/2.68  tff(c_7215, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_64, c_3924, c_102, c_70, c_3873, c_3924, c_7208])).
% 7.59/2.68  tff(c_56, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.59/2.68  tff(c_7248, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7215, c_56])).
% 7.59/2.68  tff(c_7260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3810, c_7248])).
% 7.59/2.68  tff(c_7261, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3871])).
% 7.59/2.68  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.59/2.68  tff(c_7289, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7261, c_12])).
% 7.59/2.68  tff(c_7291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2923, c_7289])).
% 7.59/2.68  tff(c_7292, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3868])).
% 7.59/2.68  tff(c_7319, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7292, c_12])).
% 7.59/2.68  tff(c_7321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2923, c_7319])).
% 7.59/2.68  tff(c_7323, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2920])).
% 7.59/2.68  tff(c_2921, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_60, c_2909])).
% 7.59/2.68  tff(c_7339, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_7323, c_2921])).
% 7.59/2.68  tff(c_7348, plain, (![A_601, B_602]: (r2_hidden('#skF_3'(A_601, B_602), B_602) | r2_hidden('#skF_4'(A_601, B_602), A_601) | B_602=A_601)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.59/2.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.59/2.68  tff(c_7397, plain, (![B_609, A_610]: (~v1_xboole_0(B_609) | r2_hidden('#skF_4'(A_610, B_609), A_610) | B_609=A_610)), inference(resolution, [status(thm)], [c_7348, c_2])).
% 7.59/2.68  tff(c_7410, plain, (![A_611, B_612]: (~v1_xboole_0(A_611) | ~v1_xboole_0(B_612) | B_612=A_611)), inference(resolution, [status(thm)], [c_7397, c_2])).
% 7.59/2.68  tff(c_7432, plain, (![B_615]: (~v1_xboole_0(B_615) | B_615='#skF_10')), inference(resolution, [status(thm)], [c_7339, c_7410])).
% 7.59/2.68  tff(c_7451, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_7323, c_7432])).
% 7.59/2.68  tff(c_7322, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_2920])).
% 7.59/2.68  tff(c_7452, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_7322, c_7432])).
% 7.59/2.68  tff(c_7472, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7451, c_7452])).
% 7.59/2.68  tff(c_7464, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7451, c_56])).
% 7.59/2.68  tff(c_7525, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7472, c_7464])).
% 7.59/2.68  tff(c_7463, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_7451, c_60])).
% 7.59/2.68  tff(c_22, plain, (![A_13]: (m1_subset_1('#skF_5'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.59/2.68  tff(c_7977, plain, (![A_672, B_673, C_674, D_675]: (r2_relset_1(A_672, B_673, C_674, C_674) | ~m1_subset_1(D_675, k1_zfmisc_1(k2_zfmisc_1(A_672, B_673))) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_zfmisc_1(A_672, B_673))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.59/2.68  tff(c_7987, plain, (![A_676, B_677, C_678]: (r2_relset_1(A_676, B_677, C_678, C_678) | ~m1_subset_1(C_678, k1_zfmisc_1(k2_zfmisc_1(A_676, B_677))))), inference(resolution, [status(thm)], [c_22, c_7977])).
% 7.59/2.68  tff(c_7991, plain, (r2_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_7463, c_7987])).
% 7.59/2.68  tff(c_7999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7525, c_7991])).
% 7.59/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.68  
% 7.59/2.68  Inference rules
% 7.59/2.68  ----------------------
% 7.59/2.68  #Ref     : 2
% 7.59/2.68  #Sup     : 1632
% 7.59/2.68  #Fact    : 0
% 7.59/2.68  #Define  : 0
% 7.59/2.68  #Split   : 26
% 7.59/2.68  #Chain   : 0
% 7.59/2.68  #Close   : 0
% 7.59/2.68  
% 7.59/2.68  Ordering : KBO
% 7.59/2.68  
% 7.59/2.68  Simplification rules
% 7.59/2.68  ----------------------
% 7.59/2.68  #Subsume      : 939
% 7.59/2.68  #Demod        : 1454
% 7.59/2.68  #Tautology    : 701
% 7.59/2.68  #SimpNegUnit  : 212
% 7.59/2.68  #BackRed      : 304
% 7.59/2.68  
% 7.59/2.68  #Partial instantiations: 0
% 7.59/2.68  #Strategies tried      : 1
% 7.59/2.68  
% 7.59/2.68  Timing (in seconds)
% 7.59/2.68  ----------------------
% 7.59/2.69  Preprocessing        : 0.37
% 7.59/2.69  Parsing              : 0.17
% 7.59/2.69  CNF conversion       : 0.03
% 7.59/2.69  Main loop            : 1.50
% 7.59/2.69  Inferencing          : 0.49
% 7.59/2.69  Reduction            : 0.49
% 7.59/2.69  Demodulation         : 0.34
% 7.59/2.69  BG Simplification    : 0.05
% 7.59/2.69  Subsumption          : 0.35
% 7.59/2.69  Abstraction          : 0.07
% 7.59/2.69  MUC search           : 0.00
% 7.59/2.69  Cooper               : 0.00
% 7.59/2.69  Total                : 1.92
% 7.59/2.69  Index Insertion      : 0.00
% 7.59/2.69  Index Deletion       : 0.00
% 7.59/2.69  Index Matching       : 0.00
% 7.59/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
