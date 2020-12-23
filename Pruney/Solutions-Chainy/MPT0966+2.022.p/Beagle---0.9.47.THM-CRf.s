%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:11 EST 2020

% Result     : Theorem 10.13s
% Output     : CNFRefutation 10.13s
% Verified   : 
% Statistics : Number of formulae       :  198 (2481 expanded)
%              Number of leaves         :   41 ( 841 expanded)
%              Depth                    :   16
%              Number of atoms          :  347 (7616 expanded)
%              Number of equality atoms :  123 (2520 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_134,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_26,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_20620,plain,(
    ! [B_33457,A_33458] :
      ( v1_relat_1(B_33457)
      | ~ m1_subset_1(B_33457,k1_zfmisc_1(A_33458))
      | ~ v1_relat_1(A_33458) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20632,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_20620])).

tff(c_20642,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20632])).

tff(c_20816,plain,(
    ! [C_33474,A_33475,B_33476] :
      ( v4_relat_1(C_33474,A_33475)
      | ~ m1_subset_1(C_33474,k1_zfmisc_1(k2_zfmisc_1(A_33475,B_33476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20836,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_20816])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21191,plain,(
    ! [A_33516,B_33517,C_33518] :
      ( k2_relset_1(A_33516,B_33517,C_33518) = k2_relat_1(C_33518)
      | ~ m1_subset_1(C_33518,k1_zfmisc_1(k2_zfmisc_1(A_33516,B_33517))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_21210,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_21191])).

tff(c_76,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_21212,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21210,c_76])).

tff(c_21433,plain,(
    ! [C_33544,A_33545,B_33546] :
      ( m1_subset_1(C_33544,k1_zfmisc_1(k2_zfmisc_1(A_33545,B_33546)))
      | ~ r1_tarski(k2_relat_1(C_33544),B_33546)
      | ~ r1_tarski(k1_relat_1(C_33544),A_33545)
      | ~ v1_relat_1(C_33544) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_145,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_151,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_145])).

tff(c_155,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_151])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_111,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_14576,plain,(
    ! [A_23402,B_23403,C_23404] :
      ( k1_relset_1(A_23402,B_23403,C_23404) = k1_relat_1(C_23404)
      | ~ m1_subset_1(C_23404,k1_zfmisc_1(k2_zfmisc_1(A_23402,B_23403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14595,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_14576])).

tff(c_14868,plain,(
    ! [B_23437,A_23438,C_23439] :
      ( k1_xboole_0 = B_23437
      | k1_relset_1(A_23438,B_23437,C_23439) = A_23438
      | ~ v1_funct_2(C_23439,A_23438,B_23437)
      | ~ m1_subset_1(C_23439,k1_zfmisc_1(k2_zfmisc_1(A_23438,B_23437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14881,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_14868])).

tff(c_14895,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_14595,c_14881])).

tff(c_14896,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_14895])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5692,plain,(
    ! [A_3981,B_3982,C_3983] :
      ( k1_relset_1(A_3981,B_3982,C_3983) = k1_relat_1(C_3983)
      | ~ m1_subset_1(C_3983,k1_zfmisc_1(k2_zfmisc_1(A_3981,B_3982))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5711,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_5692])).

tff(c_6148,plain,(
    ! [B_4033,A_4034,C_4035] :
      ( k1_xboole_0 = B_4033
      | k1_relset_1(A_4034,B_4033,C_4035) = A_4034
      | ~ v1_funct_2(C_4035,A_4034,B_4033)
      | ~ m1_subset_1(C_4035,k1_zfmisc_1(k2_zfmisc_1(A_4034,B_4033))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6161,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_6148])).

tff(c_6175,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5711,c_6161])).

tff(c_6176,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_6175])).

tff(c_5758,plain,(
    ! [A_3987,B_3988,C_3989] :
      ( k2_relset_1(A_3987,B_3988,C_3989) = k2_relat_1(C_3989)
      | ~ m1_subset_1(C_3989,k1_zfmisc_1(k2_zfmisc_1(A_3987,B_3988))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5777,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_5758])).

tff(c_5780,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5777,c_76])).

tff(c_5851,plain,(
    ! [C_3995,A_3996,B_3997] :
      ( m1_subset_1(C_3995,k1_zfmisc_1(k2_zfmisc_1(A_3996,B_3997)))
      | ~ r1_tarski(k2_relat_1(C_3995),B_3997)
      | ~ r1_tarski(k1_relat_1(C_3995),A_3996)
      | ~ v1_relat_1(C_3995) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10331,plain,(
    ! [C_14453,A_14454,B_14455] :
      ( r1_tarski(C_14453,k2_zfmisc_1(A_14454,B_14455))
      | ~ r1_tarski(k2_relat_1(C_14453),B_14455)
      | ~ r1_tarski(k1_relat_1(C_14453),A_14454)
      | ~ v1_relat_1(C_14453) ) ),
    inference(resolution,[status(thm)],[c_5851,c_16])).

tff(c_10339,plain,(
    ! [A_14454] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_14454,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_14454)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5780,c_10331])).

tff(c_10356,plain,(
    ! [A_14456] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_14456,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_14456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_6176,c_10339])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5710,plain,(
    ! [A_3981,B_3982,A_6] :
      ( k1_relset_1(A_3981,B_3982,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_3981,B_3982)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5692])).

tff(c_10359,plain,(
    ! [A_14456] :
      ( k1_relset_1(A_14456,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_14456) ) ),
    inference(resolution,[status(thm)],[c_10356,c_5710])).

tff(c_10389,plain,(
    ! [A_14457] :
      ( k1_relset_1(A_14457,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_14457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6176,c_10359])).

tff(c_10406,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_10389])).

tff(c_10352,plain,(
    ! [A_14454] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_14454,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_14454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_6176,c_10339])).

tff(c_13337,plain,(
    ! [B_23318,A_23319,A_23320] :
      ( k1_xboole_0 = B_23318
      | k1_relset_1(A_23319,B_23318,A_23320) = A_23319
      | ~ v1_funct_2(A_23320,A_23319,B_23318)
      | ~ r1_tarski(A_23320,k2_zfmisc_1(A_23319,B_23318)) ) ),
    inference(resolution,[status(thm)],[c_18,c_6148])).

tff(c_13373,plain,(
    ! [A_14454] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1(A_14454,'#skF_4','#skF_5') = A_14454
      | ~ v1_funct_2('#skF_5',A_14454,'#skF_4')
      | ~ r1_tarski('#skF_2',A_14454) ) ),
    inference(resolution,[status(thm)],[c_10352,c_13337])).

tff(c_13523,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13373])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13630,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13523,c_8])).

tff(c_156,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_76,c_156])).

tff(c_5188,plain,(
    ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_5778,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5777,c_5188])).

tff(c_13760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13630,c_5778])).

tff(c_13762,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13373])).

tff(c_5998,plain,(
    ! [B_4014,C_4015,A_4016] :
      ( k1_xboole_0 = B_4014
      | v1_funct_2(C_4015,A_4016,B_4014)
      | k1_relset_1(A_4016,B_4014,C_4015) != A_4016
      | ~ m1_subset_1(C_4015,k1_zfmisc_1(k2_zfmisc_1(A_4016,B_4014))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_13901,plain,(
    ! [B_23339,A_23340,A_23341] :
      ( k1_xboole_0 = B_23339
      | v1_funct_2(A_23340,A_23341,B_23339)
      | k1_relset_1(A_23341,B_23339,A_23340) != A_23341
      | ~ r1_tarski(A_23340,k2_zfmisc_1(A_23341,B_23339)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5998])).

tff(c_13907,plain,(
    ! [A_14454] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_14454,'#skF_4')
      | k1_relset_1(A_14454,'#skF_4','#skF_5') != A_14454
      | ~ r1_tarski('#skF_2',A_14454) ) ),
    inference(resolution,[status(thm)],[c_10352,c_13901])).

tff(c_13977,plain,(
    ! [A_23344] :
      ( v1_funct_2('#skF_5',A_23344,'#skF_4')
      | k1_relset_1(A_23344,'#skF_4','#skF_5') != A_23344
      | ~ r1_tarski('#skF_2',A_23344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13762,c_13907])).

tff(c_82,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_84,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_72])).

tff(c_134,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_13986,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_13977,c_134])).

tff(c_13992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10406,c_13986])).

tff(c_13993,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_14390,plain,(
    ! [A_23386,B_23387,C_23388] :
      ( k2_relset_1(A_23386,B_23387,C_23388) = k2_relat_1(C_23388)
      | ~ m1_subset_1(C_23388,k1_zfmisc_1(k2_zfmisc_1(A_23386,B_23387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14400,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_14390])).

tff(c_14410,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13993,c_14400])).

tff(c_14292,plain,(
    ! [C_23374,A_23375,B_23376] :
      ( v4_relat_1(C_23374,A_23375)
      | ~ m1_subset_1(C_23374,k1_zfmisc_1(k2_zfmisc_1(A_23375,B_23376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14312,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_14292])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14315,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14312,c_32])).

tff(c_14318,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_14315])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14322,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14318,c_28])).

tff(c_14326,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_14322])).

tff(c_14411,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14410,c_14326])).

tff(c_14495,plain,(
    ! [B_23395,A_23396] :
      ( k9_relat_1(B_23395,A_23396) != k1_xboole_0
      | ~ r1_tarski(A_23396,k1_relat_1(B_23395))
      | k1_xboole_0 = A_23396
      | ~ v1_relat_1(B_23395) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14514,plain,(
    ! [B_23395] :
      ( k9_relat_1(B_23395,k1_relat_1(B_23395)) != k1_xboole_0
      | k1_relat_1(B_23395) = k1_xboole_0
      | ~ v1_relat_1(B_23395) ) ),
    inference(resolution,[status(thm)],[c_6,c_14495])).

tff(c_14902,plain,
    ( k9_relat_1('#skF_5','#skF_2') != k1_xboole_0
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14896,c_14514])).

tff(c_14921,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_14896,c_14411,c_14902])).

tff(c_14933,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14921])).

tff(c_14717,plain,(
    ! [C_23419,A_23420,B_23421] :
      ( m1_subset_1(C_23419,k1_zfmisc_1(k2_zfmisc_1(A_23420,B_23421)))
      | ~ r1_tarski(k2_relat_1(C_23419),B_23421)
      | ~ r1_tarski(k1_relat_1(C_23419),A_23420)
      | ~ v1_relat_1(C_23419) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    ! [A_24,B_25,C_26] :
      ( k1_relset_1(A_24,B_25,C_26) = k1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_19583,plain,(
    ! [A_33398,B_33399,C_33400] :
      ( k1_relset_1(A_33398,B_33399,C_33400) = k1_relat_1(C_33400)
      | ~ r1_tarski(k2_relat_1(C_33400),B_33399)
      | ~ r1_tarski(k1_relat_1(C_33400),A_33398)
      | ~ v1_relat_1(C_33400) ) ),
    inference(resolution,[status(thm)],[c_14717,c_42])).

tff(c_19588,plain,(
    ! [A_33398,B_33399] :
      ( k1_relset_1(A_33398,B_33399,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_4',B_33399)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_33398)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14410,c_19583])).

tff(c_19628,plain,(
    ! [A_33403,B_33404] :
      ( k1_relset_1(A_33403,B_33404,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_4',B_33404)
      | ~ r1_tarski('#skF_2',A_33403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_14896,c_14896,c_19588])).

tff(c_19637,plain,(
    ! [A_33405] :
      ( k1_relset_1(A_33405,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_33405) ) ),
    inference(resolution,[status(thm)],[c_6,c_19628])).

tff(c_19647,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_19637])).

tff(c_18833,plain,(
    ! [C_33351,A_33352,B_33353] :
      ( r1_tarski(C_33351,k2_zfmisc_1(A_33352,B_33353))
      | ~ r1_tarski(k2_relat_1(C_33351),B_33353)
      | ~ r1_tarski(k1_relat_1(C_33351),A_33352)
      | ~ v1_relat_1(C_33351) ) ),
    inference(resolution,[status(thm)],[c_14717,c_16])).

tff(c_18841,plain,(
    ! [A_33352,B_33353] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_33352,B_33353))
      | ~ r1_tarski('#skF_4',B_33353)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_33352)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14410,c_18833])).

tff(c_18853,plain,(
    ! [A_33352,B_33353] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_33352,B_33353))
      | ~ r1_tarski('#skF_4',B_33353)
      | ~ r1_tarski('#skF_2',A_33352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_14896,c_18841])).

tff(c_15116,plain,(
    ! [B_23454,C_23455,A_23456] :
      ( k1_xboole_0 = B_23454
      | v1_funct_2(C_23455,A_23456,B_23454)
      | k1_relset_1(A_23456,B_23454,C_23455) != A_23456
      | ~ m1_subset_1(C_23455,k1_zfmisc_1(k2_zfmisc_1(A_23456,B_23454))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_19762,plain,(
    ! [B_33413,A_33414,A_33415] :
      ( k1_xboole_0 = B_33413
      | v1_funct_2(A_33414,A_33415,B_33413)
      | k1_relset_1(A_33415,B_33413,A_33414) != A_33415
      | ~ r1_tarski(A_33414,k2_zfmisc_1(A_33415,B_33413)) ) ),
    inference(resolution,[status(thm)],[c_18,c_15116])).

tff(c_19843,plain,(
    ! [B_33419,A_33420] :
      ( k1_xboole_0 = B_33419
      | v1_funct_2('#skF_5',A_33420,B_33419)
      | k1_relset_1(A_33420,B_33419,'#skF_5') != A_33420
      | ~ r1_tarski('#skF_4',B_33419)
      | ~ r1_tarski('#skF_2',A_33420) ) ),
    inference(resolution,[status(thm)],[c_18853,c_19762])).

tff(c_19852,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_19843,c_134])).

tff(c_19857,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_19647,c_19852])).

tff(c_19859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14933,c_19857])).

tff(c_19861,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14921])).

tff(c_19860,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14921])).

tff(c_19907,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19861,c_19860])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5103,plain,(
    ! [A_3922,B_3923] : m1_subset_1('#skF_1'(A_3922,B_3923),k1_zfmisc_1(k2_zfmisc_1(A_3922,B_3923))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5120,plain,(
    ! [A_3924] : m1_subset_1('#skF_1'(A_3924,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5103])).

tff(c_5143,plain,(
    ! [A_3928] : r1_tarski('#skF_1'(A_3928,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5120,c_16])).

tff(c_171,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_5155,plain,(
    ! [A_3928] : '#skF_1'(A_3928,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5143,c_171])).

tff(c_19892,plain,(
    ! [A_3928] : '#skF_1'(A_3928,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19860,c_19860,c_5155])).

tff(c_20365,plain,(
    ! [A_33433] : '#skF_1'(A_33433,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19907,c_19907,c_19892])).

tff(c_60,plain,(
    ! [A_36,B_37] : v1_funct_2('#skF_1'(A_36,B_37),A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20391,plain,(
    ! [A_33433] : v1_funct_2('#skF_4',A_33433,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20365,c_60])).

tff(c_19902,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19860,c_8])).

tff(c_19996,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19907,c_19902])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19899,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19860,c_19860,c_14])).

tff(c_20128,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19907,c_19907,c_19899])).

tff(c_135,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_135])).

tff(c_19920,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19907,c_139])).

tff(c_20285,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20128,c_19920])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20290,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_20285,c_2])).

tff(c_20296,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19996,c_20290])).

tff(c_19921,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19907,c_134])).

tff(c_20302,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20296,c_19921])).

tff(c_20498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20391,c_20302])).

tff(c_20499,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_21454,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_21433,c_20499])).

tff(c_21471,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20642,c_21212,c_21454])).

tff(c_21474,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_21471])).

tff(c_21478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20642,c_20836,c_21474])).

tff(c_21480,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_21479,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_21490,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21480,c_21479])).

tff(c_21485,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21479,c_8])).

tff(c_21506,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21490,c_21485])).

tff(c_21482,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21479,c_21479,c_14])).

tff(c_21526,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21490,c_21490,c_21482])).

tff(c_21604,plain,(
    ! [A_33568,B_33569] : m1_subset_1('#skF_1'(A_33568,B_33569),k1_zfmisc_1(k2_zfmisc_1(A_33568,B_33569))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_21621,plain,(
    ! [B_33570] : m1_subset_1('#skF_1'('#skF_3',B_33570),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21526,c_21604])).

tff(c_21631,plain,(
    ! [B_33570] : r1_tarski('#skF_1'('#skF_3',B_33570),'#skF_3') ),
    inference(resolution,[status(thm)],[c_21621,c_16])).

tff(c_21673,plain,(
    ! [B_33576,A_33577] :
      ( B_33576 = A_33577
      | ~ r1_tarski(B_33576,A_33577)
      | ~ r1_tarski(A_33577,B_33576) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21679,plain,(
    ! [B_33570] :
      ( '#skF_1'('#skF_3',B_33570) = '#skF_3'
      | ~ r1_tarski('#skF_3','#skF_1'('#skF_3',B_33570)) ) ),
    inference(resolution,[status(thm)],[c_21631,c_21673])).

tff(c_21799,plain,(
    ! [B_33583] : '#skF_1'('#skF_3',B_33583) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21506,c_21679])).

tff(c_21813,plain,(
    ! [B_33583] : v1_funct_2('#skF_3','#skF_3',B_33583) ),
    inference(superposition,[status(thm),theory(equality)],[c_21799,c_60])).

tff(c_21513,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21480,c_21480,c_12])).

tff(c_21524,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21513,c_21490,c_78])).

tff(c_21549,plain,(
    ! [A_33558,B_33559] :
      ( r1_tarski(A_33558,B_33559)
      | ~ m1_subset_1(A_33558,k1_zfmisc_1(B_33559)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_21553,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_21524,c_21549])).

tff(c_21681,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_21553,c_21673])).

tff(c_21697,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21506,c_21681])).

tff(c_21555,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21490,c_21524,c_21526,c_21490,c_84])).

tff(c_21705,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21697,c_21555])).

tff(c_21856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21813,c_21705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:24:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.13/3.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.13/3.53  
% 10.13/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.13/3.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.13/3.53  
% 10.13/3.53  %Foreground sorts:
% 10.13/3.53  
% 10.13/3.53  
% 10.13/3.53  %Background operators:
% 10.13/3.53  
% 10.13/3.53  
% 10.13/3.53  %Foreground operators:
% 10.13/3.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.13/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.13/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.13/3.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.13/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.13/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.13/3.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.13/3.53  tff('#skF_5', type, '#skF_5': $i).
% 10.13/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.13/3.53  tff('#skF_2', type, '#skF_2': $i).
% 10.13/3.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.13/3.53  tff('#skF_3', type, '#skF_3': $i).
% 10.13/3.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.13/3.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.13/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.13/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.13/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.13/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.13/3.53  tff('#skF_4', type, '#skF_4': $i).
% 10.13/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.13/3.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.13/3.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.13/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.13/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.13/3.53  
% 10.13/3.56  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.13/3.56  tff(f_154, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 10.13/3.56  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.13/3.56  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.13/3.56  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.13/3.56  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.13/3.56  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 10.13/3.56  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.13/3.56  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.13/3.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.13/3.56  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.13/3.56  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.13/3.56  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.13/3.56  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 10.13/3.56  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 10.13/3.56  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.13/3.56  tff(f_134, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 10.13/3.56  tff(c_26, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.13/3.56  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.13/3.56  tff(c_20620, plain, (![B_33457, A_33458]: (v1_relat_1(B_33457) | ~m1_subset_1(B_33457, k1_zfmisc_1(A_33458)) | ~v1_relat_1(A_33458))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.13/3.56  tff(c_20632, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_20620])).
% 10.13/3.56  tff(c_20642, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20632])).
% 10.13/3.56  tff(c_20816, plain, (![C_33474, A_33475, B_33476]: (v4_relat_1(C_33474, A_33475) | ~m1_subset_1(C_33474, k1_zfmisc_1(k2_zfmisc_1(A_33475, B_33476))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.13/3.56  tff(c_20836, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_20816])).
% 10.13/3.56  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.13/3.56  tff(c_21191, plain, (![A_33516, B_33517, C_33518]: (k2_relset_1(A_33516, B_33517, C_33518)=k2_relat_1(C_33518) | ~m1_subset_1(C_33518, k1_zfmisc_1(k2_zfmisc_1(A_33516, B_33517))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.13/3.56  tff(c_21210, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_21191])).
% 10.13/3.56  tff(c_76, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.13/3.56  tff(c_21212, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21210, c_76])).
% 10.13/3.56  tff(c_21433, plain, (![C_33544, A_33545, B_33546]: (m1_subset_1(C_33544, k1_zfmisc_1(k2_zfmisc_1(A_33545, B_33546))) | ~r1_tarski(k2_relat_1(C_33544), B_33546) | ~r1_tarski(k1_relat_1(C_33544), A_33545) | ~v1_relat_1(C_33544))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.13/3.56  tff(c_145, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.13/3.56  tff(c_151, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_145])).
% 10.13/3.56  tff(c_155, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_151])).
% 10.13/3.56  tff(c_74, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.13/3.56  tff(c_111, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_74])).
% 10.13/3.56  tff(c_80, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.13/3.56  tff(c_14576, plain, (![A_23402, B_23403, C_23404]: (k1_relset_1(A_23402, B_23403, C_23404)=k1_relat_1(C_23404) | ~m1_subset_1(C_23404, k1_zfmisc_1(k2_zfmisc_1(A_23402, B_23403))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.13/3.56  tff(c_14595, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_14576])).
% 10.13/3.56  tff(c_14868, plain, (![B_23437, A_23438, C_23439]: (k1_xboole_0=B_23437 | k1_relset_1(A_23438, B_23437, C_23439)=A_23438 | ~v1_funct_2(C_23439, A_23438, B_23437) | ~m1_subset_1(C_23439, k1_zfmisc_1(k2_zfmisc_1(A_23438, B_23437))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.13/3.56  tff(c_14881, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_14868])).
% 10.13/3.56  tff(c_14895, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_14595, c_14881])).
% 10.13/3.56  tff(c_14896, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_111, c_14895])).
% 10.13/3.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.13/3.56  tff(c_5692, plain, (![A_3981, B_3982, C_3983]: (k1_relset_1(A_3981, B_3982, C_3983)=k1_relat_1(C_3983) | ~m1_subset_1(C_3983, k1_zfmisc_1(k2_zfmisc_1(A_3981, B_3982))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.13/3.56  tff(c_5711, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_5692])).
% 10.13/3.56  tff(c_6148, plain, (![B_4033, A_4034, C_4035]: (k1_xboole_0=B_4033 | k1_relset_1(A_4034, B_4033, C_4035)=A_4034 | ~v1_funct_2(C_4035, A_4034, B_4033) | ~m1_subset_1(C_4035, k1_zfmisc_1(k2_zfmisc_1(A_4034, B_4033))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.13/3.56  tff(c_6161, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_6148])).
% 10.13/3.56  tff(c_6175, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5711, c_6161])).
% 10.13/3.56  tff(c_6176, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_111, c_6175])).
% 10.13/3.56  tff(c_5758, plain, (![A_3987, B_3988, C_3989]: (k2_relset_1(A_3987, B_3988, C_3989)=k2_relat_1(C_3989) | ~m1_subset_1(C_3989, k1_zfmisc_1(k2_zfmisc_1(A_3987, B_3988))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.13/3.56  tff(c_5777, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_5758])).
% 10.13/3.56  tff(c_5780, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5777, c_76])).
% 10.13/3.56  tff(c_5851, plain, (![C_3995, A_3996, B_3997]: (m1_subset_1(C_3995, k1_zfmisc_1(k2_zfmisc_1(A_3996, B_3997))) | ~r1_tarski(k2_relat_1(C_3995), B_3997) | ~r1_tarski(k1_relat_1(C_3995), A_3996) | ~v1_relat_1(C_3995))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.13/3.56  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.13/3.56  tff(c_10331, plain, (![C_14453, A_14454, B_14455]: (r1_tarski(C_14453, k2_zfmisc_1(A_14454, B_14455)) | ~r1_tarski(k2_relat_1(C_14453), B_14455) | ~r1_tarski(k1_relat_1(C_14453), A_14454) | ~v1_relat_1(C_14453))), inference(resolution, [status(thm)], [c_5851, c_16])).
% 10.13/3.56  tff(c_10339, plain, (![A_14454]: (r1_tarski('#skF_5', k2_zfmisc_1(A_14454, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_14454) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_5780, c_10331])).
% 10.13/3.56  tff(c_10356, plain, (![A_14456]: (r1_tarski('#skF_5', k2_zfmisc_1(A_14456, '#skF_4')) | ~r1_tarski('#skF_2', A_14456))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_6176, c_10339])).
% 10.13/3.56  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.13/3.56  tff(c_5710, plain, (![A_3981, B_3982, A_6]: (k1_relset_1(A_3981, B_3982, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_3981, B_3982)))), inference(resolution, [status(thm)], [c_18, c_5692])).
% 10.13/3.56  tff(c_10359, plain, (![A_14456]: (k1_relset_1(A_14456, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_14456))), inference(resolution, [status(thm)], [c_10356, c_5710])).
% 10.13/3.56  tff(c_10389, plain, (![A_14457]: (k1_relset_1(A_14457, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_14457))), inference(demodulation, [status(thm), theory('equality')], [c_6176, c_10359])).
% 10.13/3.56  tff(c_10406, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_10389])).
% 10.13/3.56  tff(c_10352, plain, (![A_14454]: (r1_tarski('#skF_5', k2_zfmisc_1(A_14454, '#skF_4')) | ~r1_tarski('#skF_2', A_14454))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_6176, c_10339])).
% 10.13/3.56  tff(c_13337, plain, (![B_23318, A_23319, A_23320]: (k1_xboole_0=B_23318 | k1_relset_1(A_23319, B_23318, A_23320)=A_23319 | ~v1_funct_2(A_23320, A_23319, B_23318) | ~r1_tarski(A_23320, k2_zfmisc_1(A_23319, B_23318)))), inference(resolution, [status(thm)], [c_18, c_6148])).
% 10.13/3.56  tff(c_13373, plain, (![A_14454]: (k1_xboole_0='#skF_4' | k1_relset_1(A_14454, '#skF_4', '#skF_5')=A_14454 | ~v1_funct_2('#skF_5', A_14454, '#skF_4') | ~r1_tarski('#skF_2', A_14454))), inference(resolution, [status(thm)], [c_10352, c_13337])).
% 10.13/3.56  tff(c_13523, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_13373])).
% 10.13/3.56  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.13/3.56  tff(c_13630, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13523, c_8])).
% 10.13/3.56  tff(c_156, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.13/3.56  tff(c_166, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_76, c_156])).
% 10.13/3.56  tff(c_5188, plain, (~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_166])).
% 10.13/3.56  tff(c_5778, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5777, c_5188])).
% 10.13/3.56  tff(c_13760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13630, c_5778])).
% 10.13/3.56  tff(c_13762, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_13373])).
% 10.13/3.56  tff(c_5998, plain, (![B_4014, C_4015, A_4016]: (k1_xboole_0=B_4014 | v1_funct_2(C_4015, A_4016, B_4014) | k1_relset_1(A_4016, B_4014, C_4015)!=A_4016 | ~m1_subset_1(C_4015, k1_zfmisc_1(k2_zfmisc_1(A_4016, B_4014))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.13/3.56  tff(c_13901, plain, (![B_23339, A_23340, A_23341]: (k1_xboole_0=B_23339 | v1_funct_2(A_23340, A_23341, B_23339) | k1_relset_1(A_23341, B_23339, A_23340)!=A_23341 | ~r1_tarski(A_23340, k2_zfmisc_1(A_23341, B_23339)))), inference(resolution, [status(thm)], [c_18, c_5998])).
% 10.13/3.56  tff(c_13907, plain, (![A_14454]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_14454, '#skF_4') | k1_relset_1(A_14454, '#skF_4', '#skF_5')!=A_14454 | ~r1_tarski('#skF_2', A_14454))), inference(resolution, [status(thm)], [c_10352, c_13901])).
% 10.13/3.56  tff(c_13977, plain, (![A_23344]: (v1_funct_2('#skF_5', A_23344, '#skF_4') | k1_relset_1(A_23344, '#skF_4', '#skF_5')!=A_23344 | ~r1_tarski('#skF_2', A_23344))), inference(negUnitSimplification, [status(thm)], [c_13762, c_13907])).
% 10.13/3.56  tff(c_82, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.13/3.56  tff(c_72, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.13/3.56  tff(c_84, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_72])).
% 10.13/3.56  tff(c_134, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 10.13/3.56  tff(c_13986, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_13977, c_134])).
% 10.13/3.56  tff(c_13992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10406, c_13986])).
% 10.13/3.56  tff(c_13993, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_166])).
% 10.13/3.56  tff(c_14390, plain, (![A_23386, B_23387, C_23388]: (k2_relset_1(A_23386, B_23387, C_23388)=k2_relat_1(C_23388) | ~m1_subset_1(C_23388, k1_zfmisc_1(k2_zfmisc_1(A_23386, B_23387))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.13/3.56  tff(c_14400, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_14390])).
% 10.13/3.56  tff(c_14410, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13993, c_14400])).
% 10.13/3.56  tff(c_14292, plain, (![C_23374, A_23375, B_23376]: (v4_relat_1(C_23374, A_23375) | ~m1_subset_1(C_23374, k1_zfmisc_1(k2_zfmisc_1(A_23375, B_23376))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.13/3.56  tff(c_14312, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_14292])).
% 10.13/3.56  tff(c_32, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.13/3.56  tff(c_14315, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14312, c_32])).
% 10.13/3.56  tff(c_14318, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_14315])).
% 10.13/3.56  tff(c_28, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.13/3.56  tff(c_14322, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14318, c_28])).
% 10.13/3.56  tff(c_14326, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_14322])).
% 10.13/3.56  tff(c_14411, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14410, c_14326])).
% 10.13/3.56  tff(c_14495, plain, (![B_23395, A_23396]: (k9_relat_1(B_23395, A_23396)!=k1_xboole_0 | ~r1_tarski(A_23396, k1_relat_1(B_23395)) | k1_xboole_0=A_23396 | ~v1_relat_1(B_23395))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.13/3.56  tff(c_14514, plain, (![B_23395]: (k9_relat_1(B_23395, k1_relat_1(B_23395))!=k1_xboole_0 | k1_relat_1(B_23395)=k1_xboole_0 | ~v1_relat_1(B_23395))), inference(resolution, [status(thm)], [c_6, c_14495])).
% 10.13/3.56  tff(c_14902, plain, (k9_relat_1('#skF_5', '#skF_2')!=k1_xboole_0 | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14896, c_14514])).
% 10.13/3.56  tff(c_14921, plain, (k1_xboole_0!='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_14896, c_14411, c_14902])).
% 10.13/3.56  tff(c_14933, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_14921])).
% 10.13/3.56  tff(c_14717, plain, (![C_23419, A_23420, B_23421]: (m1_subset_1(C_23419, k1_zfmisc_1(k2_zfmisc_1(A_23420, B_23421))) | ~r1_tarski(k2_relat_1(C_23419), B_23421) | ~r1_tarski(k1_relat_1(C_23419), A_23420) | ~v1_relat_1(C_23419))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.13/3.56  tff(c_42, plain, (![A_24, B_25, C_26]: (k1_relset_1(A_24, B_25, C_26)=k1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.13/3.56  tff(c_19583, plain, (![A_33398, B_33399, C_33400]: (k1_relset_1(A_33398, B_33399, C_33400)=k1_relat_1(C_33400) | ~r1_tarski(k2_relat_1(C_33400), B_33399) | ~r1_tarski(k1_relat_1(C_33400), A_33398) | ~v1_relat_1(C_33400))), inference(resolution, [status(thm)], [c_14717, c_42])).
% 10.13/3.56  tff(c_19588, plain, (![A_33398, B_33399]: (k1_relset_1(A_33398, B_33399, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_4', B_33399) | ~r1_tarski(k1_relat_1('#skF_5'), A_33398) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14410, c_19583])).
% 10.13/3.56  tff(c_19628, plain, (![A_33403, B_33404]: (k1_relset_1(A_33403, B_33404, '#skF_5')='#skF_2' | ~r1_tarski('#skF_4', B_33404) | ~r1_tarski('#skF_2', A_33403))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_14896, c_14896, c_19588])).
% 10.13/3.56  tff(c_19637, plain, (![A_33405]: (k1_relset_1(A_33405, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_33405))), inference(resolution, [status(thm)], [c_6, c_19628])).
% 10.13/3.56  tff(c_19647, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_19637])).
% 10.13/3.56  tff(c_18833, plain, (![C_33351, A_33352, B_33353]: (r1_tarski(C_33351, k2_zfmisc_1(A_33352, B_33353)) | ~r1_tarski(k2_relat_1(C_33351), B_33353) | ~r1_tarski(k1_relat_1(C_33351), A_33352) | ~v1_relat_1(C_33351))), inference(resolution, [status(thm)], [c_14717, c_16])).
% 10.13/3.56  tff(c_18841, plain, (![A_33352, B_33353]: (r1_tarski('#skF_5', k2_zfmisc_1(A_33352, B_33353)) | ~r1_tarski('#skF_4', B_33353) | ~r1_tarski(k1_relat_1('#skF_5'), A_33352) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14410, c_18833])).
% 10.13/3.56  tff(c_18853, plain, (![A_33352, B_33353]: (r1_tarski('#skF_5', k2_zfmisc_1(A_33352, B_33353)) | ~r1_tarski('#skF_4', B_33353) | ~r1_tarski('#skF_2', A_33352))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_14896, c_18841])).
% 10.13/3.56  tff(c_15116, plain, (![B_23454, C_23455, A_23456]: (k1_xboole_0=B_23454 | v1_funct_2(C_23455, A_23456, B_23454) | k1_relset_1(A_23456, B_23454, C_23455)!=A_23456 | ~m1_subset_1(C_23455, k1_zfmisc_1(k2_zfmisc_1(A_23456, B_23454))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.13/3.56  tff(c_19762, plain, (![B_33413, A_33414, A_33415]: (k1_xboole_0=B_33413 | v1_funct_2(A_33414, A_33415, B_33413) | k1_relset_1(A_33415, B_33413, A_33414)!=A_33415 | ~r1_tarski(A_33414, k2_zfmisc_1(A_33415, B_33413)))), inference(resolution, [status(thm)], [c_18, c_15116])).
% 10.13/3.56  tff(c_19843, plain, (![B_33419, A_33420]: (k1_xboole_0=B_33419 | v1_funct_2('#skF_5', A_33420, B_33419) | k1_relset_1(A_33420, B_33419, '#skF_5')!=A_33420 | ~r1_tarski('#skF_4', B_33419) | ~r1_tarski('#skF_2', A_33420))), inference(resolution, [status(thm)], [c_18853, c_19762])).
% 10.13/3.56  tff(c_19852, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_19843, c_134])).
% 10.13/3.56  tff(c_19857, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_19647, c_19852])).
% 10.13/3.56  tff(c_19859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14933, c_19857])).
% 10.13/3.56  tff(c_19861, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_14921])).
% 10.13/3.56  tff(c_19860, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14921])).
% 10.13/3.56  tff(c_19907, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19861, c_19860])).
% 10.13/3.56  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.13/3.56  tff(c_5103, plain, (![A_3922, B_3923]: (m1_subset_1('#skF_1'(A_3922, B_3923), k1_zfmisc_1(k2_zfmisc_1(A_3922, B_3923))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.13/3.56  tff(c_5120, plain, (![A_3924]: (m1_subset_1('#skF_1'(A_3924, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5103])).
% 10.13/3.56  tff(c_5143, plain, (![A_3928]: (r1_tarski('#skF_1'(A_3928, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_5120, c_16])).
% 10.13/3.56  tff(c_171, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_156])).
% 10.13/3.56  tff(c_5155, plain, (![A_3928]: ('#skF_1'(A_3928, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5143, c_171])).
% 10.13/3.56  tff(c_19892, plain, (![A_3928]: ('#skF_1'(A_3928, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19860, c_19860, c_5155])).
% 10.13/3.56  tff(c_20365, plain, (![A_33433]: ('#skF_1'(A_33433, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19907, c_19907, c_19892])).
% 10.13/3.56  tff(c_60, plain, (![A_36, B_37]: (v1_funct_2('#skF_1'(A_36, B_37), A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.13/3.56  tff(c_20391, plain, (![A_33433]: (v1_funct_2('#skF_4', A_33433, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_20365, c_60])).
% 10.13/3.56  tff(c_19902, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_19860, c_8])).
% 10.13/3.56  tff(c_19996, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_19907, c_19902])).
% 10.13/3.56  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.13/3.56  tff(c_19899, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19860, c_19860, c_14])).
% 10.13/3.56  tff(c_20128, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19907, c_19907, c_19899])).
% 10.13/3.56  tff(c_135, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.13/3.56  tff(c_139, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_135])).
% 10.13/3.56  tff(c_19920, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19907, c_139])).
% 10.13/3.56  tff(c_20285, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20128, c_19920])).
% 10.13/3.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.13/3.56  tff(c_20290, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_20285, c_2])).
% 10.13/3.56  tff(c_20296, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19996, c_20290])).
% 10.13/3.56  tff(c_19921, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19907, c_134])).
% 10.13/3.56  tff(c_20302, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20296, c_19921])).
% 10.13/3.56  tff(c_20498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20391, c_20302])).
% 10.13/3.56  tff(c_20499, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_84])).
% 10.13/3.56  tff(c_21454, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_21433, c_20499])).
% 10.13/3.56  tff(c_21471, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20642, c_21212, c_21454])).
% 10.13/3.56  tff(c_21474, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_21471])).
% 10.13/3.56  tff(c_21478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20642, c_20836, c_21474])).
% 10.13/3.56  tff(c_21480, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_74])).
% 10.13/3.56  tff(c_21479, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_74])).
% 10.13/3.56  tff(c_21490, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21480, c_21479])).
% 10.13/3.56  tff(c_21485, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_21479, c_8])).
% 10.13/3.56  tff(c_21506, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_21490, c_21485])).
% 10.13/3.56  tff(c_21482, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21479, c_21479, c_14])).
% 10.13/3.56  tff(c_21526, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21490, c_21490, c_21482])).
% 10.13/3.56  tff(c_21604, plain, (![A_33568, B_33569]: (m1_subset_1('#skF_1'(A_33568, B_33569), k1_zfmisc_1(k2_zfmisc_1(A_33568, B_33569))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.13/3.56  tff(c_21621, plain, (![B_33570]: (m1_subset_1('#skF_1'('#skF_3', B_33570), k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_21526, c_21604])).
% 10.13/3.56  tff(c_21631, plain, (![B_33570]: (r1_tarski('#skF_1'('#skF_3', B_33570), '#skF_3'))), inference(resolution, [status(thm)], [c_21621, c_16])).
% 10.13/3.56  tff(c_21673, plain, (![B_33576, A_33577]: (B_33576=A_33577 | ~r1_tarski(B_33576, A_33577) | ~r1_tarski(A_33577, B_33576))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.13/3.56  tff(c_21679, plain, (![B_33570]: ('#skF_1'('#skF_3', B_33570)='#skF_3' | ~r1_tarski('#skF_3', '#skF_1'('#skF_3', B_33570)))), inference(resolution, [status(thm)], [c_21631, c_21673])).
% 10.13/3.56  tff(c_21799, plain, (![B_33583]: ('#skF_1'('#skF_3', B_33583)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21506, c_21679])).
% 10.13/3.56  tff(c_21813, plain, (![B_33583]: (v1_funct_2('#skF_3', '#skF_3', B_33583))), inference(superposition, [status(thm), theory('equality')], [c_21799, c_60])).
% 10.13/3.56  tff(c_21513, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21480, c_21480, c_12])).
% 10.13/3.56  tff(c_21524, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21513, c_21490, c_78])).
% 10.13/3.56  tff(c_21549, plain, (![A_33558, B_33559]: (r1_tarski(A_33558, B_33559) | ~m1_subset_1(A_33558, k1_zfmisc_1(B_33559)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.13/3.56  tff(c_21553, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_21524, c_21549])).
% 10.13/3.56  tff(c_21681, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_21553, c_21673])).
% 10.13/3.56  tff(c_21697, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21506, c_21681])).
% 10.13/3.56  tff(c_21555, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21490, c_21524, c_21526, c_21490, c_84])).
% 10.13/3.56  tff(c_21705, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21697, c_21555])).
% 10.13/3.56  tff(c_21856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21813, c_21705])).
% 10.13/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.13/3.56  
% 10.13/3.56  Inference rules
% 10.13/3.56  ----------------------
% 10.13/3.56  #Ref     : 0
% 10.13/3.56  #Sup     : 4499
% 10.13/3.56  #Fact    : 12
% 10.13/3.56  #Define  : 0
% 10.13/3.56  #Split   : 44
% 10.13/3.56  #Chain   : 0
% 10.13/3.56  #Close   : 0
% 10.13/3.56  
% 10.13/3.56  Ordering : KBO
% 10.13/3.56  
% 10.13/3.56  Simplification rules
% 10.13/3.56  ----------------------
% 10.13/3.56  #Subsume      : 985
% 10.13/3.56  #Demod        : 3569
% 10.13/3.56  #Tautology    : 1525
% 10.13/3.56  #SimpNegUnit  : 81
% 10.13/3.56  #BackRed      : 341
% 10.13/3.56  
% 10.13/3.56  #Partial instantiations: 7624
% 10.13/3.56  #Strategies tried      : 1
% 10.13/3.56  
% 10.13/3.56  Timing (in seconds)
% 10.13/3.56  ----------------------
% 10.13/3.56  Preprocessing        : 0.36
% 10.13/3.56  Parsing              : 0.20
% 10.13/3.56  CNF conversion       : 0.02
% 10.13/3.56  Main loop            : 2.34
% 10.13/3.56  Inferencing          : 0.85
% 10.13/3.56  Reduction            : 0.81
% 10.13/3.56  Demodulation         : 0.60
% 10.13/3.56  BG Simplification    : 0.06
% 10.13/3.56  Subsumption          : 0.45
% 10.13/3.56  Abstraction          : 0.09
% 10.13/3.56  MUC search           : 0.00
% 10.13/3.56  Cooper               : 0.00
% 10.13/3.56  Total                : 2.76
% 10.13/3.56  Index Insertion      : 0.00
% 10.13/3.56  Index Deletion       : 0.00
% 10.13/3.56  Index Matching       : 0.00
% 10.13/3.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
