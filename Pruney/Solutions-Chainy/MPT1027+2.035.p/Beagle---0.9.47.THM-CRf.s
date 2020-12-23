%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:46 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   95 (1257 expanded)
%              Number of leaves         :   34 ( 417 expanded)
%              Depth                    :   14
%              Number of atoms          :  138 (3231 expanded)
%              Number of equality atoms :   48 ( 789 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_92,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_107,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | ~ v1_xboole_0(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_341,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_357,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_66,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_341])).

tff(c_412,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_416,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_412])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50])).

tff(c_52,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_626,plain,(
    ! [B_84,C_85,A_86] :
      ( k1_xboole_0 = B_84
      | v1_funct_2(C_85,A_86,B_84)
      | k1_relset_1(A_86,B_84,C_85) != A_86
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_638,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_626])).

tff(c_649,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_638])).

tff(c_650,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_649])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_680,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_2])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_680])).

tff(c_685,plain,(
    ! [A_87] : ~ r2_hidden(A_87,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_690,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_685])).

tff(c_99,plain,(
    ! [A_43] :
      ( v1_xboole_0(k1_relat_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_106,plain,(
    ! [A_46] :
      ( k1_relat_1(A_46) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_114,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_708,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_114])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_31,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_397,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [A_50] : m1_subset_1('#skF_2'(A_50),k1_zfmisc_1(k2_zfmisc_1(A_50,A_50))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_147,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_345,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_66,'#skF_2'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_147,c_341])).

tff(c_358,plain,(
    ! [A_67] : ~ r2_hidden(A_67,'#skF_2'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_345])).

tff(c_363,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_358])).

tff(c_365,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_147])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_365])).

tff(c_405,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_693,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_405])).

tff(c_684,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_815,plain,(
    ! [A_93] :
      ( A_93 = '#skF_5'
      | ~ v1_xboole_0(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_4])).

tff(c_828,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_684,c_815])).

tff(c_855,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_884,plain,(
    ! [C_98] :
      ( k1_relset_1('#skF_3','#skF_4',C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_855])).

tff(c_887,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_693,c_884])).

tff(c_889,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_52,c_887])).

tff(c_903,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_889,c_708])).

tff(c_896,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_889,c_693])).

tff(c_710,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_5',B_5) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_12])).

tff(c_861,plain,(
    ! [B_5,C_96] :
      ( k1_relset_1('#skF_5',B_5,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_855])).

tff(c_1872,plain,(
    ! [B_165,C_166] :
      ( k1_relset_1('#skF_3',B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_889,c_861])).

tff(c_1878,plain,(
    ! [B_165] : k1_relset_1('#skF_3',B_165,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_896,c_1872])).

tff(c_1882,plain,(
    ! [B_165] : k1_relset_1('#skF_3',B_165,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_1878])).

tff(c_907,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_690])).

tff(c_28,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_920,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,'#skF_3',B_32)
      | k1_relset_1('#skF_3',B_32,C_33) != '#skF_3'
      | ~ m1_subset_1(C_33,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_907,c_907,c_907,c_60])).

tff(c_1024,plain,(
    ! [B_32] :
      ( v1_funct_2('#skF_3','#skF_3',B_32)
      | k1_relset_1('#skF_3',B_32,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_896,c_920])).

tff(c_1893,plain,(
    ! [B_32] : v1_funct_2('#skF_3','#skF_3',B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_1024])).

tff(c_910,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_58])).

tff(c_1897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:38:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.55  
% 3.49/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.55  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.49/1.55  
% 3.49/1.55  %Foreground sorts:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Background operators:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Foreground operators:
% 3.49/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.55  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.49/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.49/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.55  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.49/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.55  
% 3.49/1.57  tff(f_74, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_mcart_1)).
% 3.49/1.57  tff(f_34, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.49/1.57  tff(f_120, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.49/1.57  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.49/1.57  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.49/1.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.49/1.57  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.49/1.57  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.49/1.57  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.49/1.57  tff(f_107, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_funct_2)).
% 3.49/1.57  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.49/1.57  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_1'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.49/1.57  tff(c_6, plain, (![A_2, B_3]: (v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | ~v1_xboole_0(B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.49/1.57  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.57  tff(c_341, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.57  tff(c_357, plain, (![A_66]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_66, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_341])).
% 3.49/1.57  tff(c_412, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_357])).
% 3.49/1.57  tff(c_416, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6, c_412])).
% 3.49/1.57  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.57  tff(c_50, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.57  tff(c_58, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50])).
% 3.49/1.57  tff(c_52, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.57  tff(c_626, plain, (![B_84, C_85, A_86]: (k1_xboole_0=B_84 | v1_funct_2(C_85, A_86, B_84) | k1_relset_1(A_86, B_84, C_85)!=A_86 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_84))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.49/1.57  tff(c_638, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_54, c_626])).
% 3.49/1.57  tff(c_649, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_638])).
% 3.49/1.57  tff(c_650, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_649])).
% 3.49/1.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.49/1.57  tff(c_680, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_650, c_2])).
% 3.49/1.57  tff(c_682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_416, c_680])).
% 3.49/1.57  tff(c_685, plain, (![A_87]: (~r2_hidden(A_87, '#skF_5'))), inference(splitRight, [status(thm)], [c_357])).
% 3.49/1.57  tff(c_690, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_685])).
% 3.49/1.57  tff(c_99, plain, (![A_43]: (v1_xboole_0(k1_relat_1(A_43)) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.49/1.57  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.49/1.57  tff(c_106, plain, (![A_46]: (k1_relat_1(A_46)=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_99, c_4])).
% 3.49/1.57  tff(c_114, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_106])).
% 3.49/1.57  tff(c_708, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_690, c_690, c_114])).
% 3.49/1.57  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.49/1.57  tff(c_24, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_31, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.49/1.57  tff(c_62, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 3.49/1.57  tff(c_397, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_62])).
% 3.49/1.57  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.49/1.57  tff(c_143, plain, (![A_50]: (m1_subset_1('#skF_2'(A_50), k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.57  tff(c_147, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_143])).
% 3.49/1.57  tff(c_345, plain, (![A_66]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_66, '#skF_2'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_147, c_341])).
% 3.49/1.57  tff(c_358, plain, (![A_67]: (~r2_hidden(A_67, '#skF_2'(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_345])).
% 3.49/1.57  tff(c_363, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_358])).
% 3.49/1.57  tff(c_365, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_147])).
% 3.49/1.57  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_365])).
% 3.49/1.57  tff(c_405, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_62])).
% 3.49/1.57  tff(c_693, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_690, c_405])).
% 3.49/1.57  tff(c_684, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_357])).
% 3.49/1.57  tff(c_815, plain, (![A_93]: (A_93='#skF_5' | ~v1_xboole_0(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_4])).
% 3.49/1.57  tff(c_828, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_684, c_815])).
% 3.49/1.57  tff(c_855, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.57  tff(c_884, plain, (![C_98]: (k1_relset_1('#skF_3', '#skF_4', C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_828, c_855])).
% 3.49/1.57  tff(c_887, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_693, c_884])).
% 3.49/1.57  tff(c_889, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_708, c_52, c_887])).
% 3.49/1.57  tff(c_903, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_889, c_889, c_708])).
% 3.49/1.57  tff(c_896, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_889, c_693])).
% 3.49/1.57  tff(c_710, plain, (![B_5]: (k2_zfmisc_1('#skF_5', B_5)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_690, c_690, c_12])).
% 3.49/1.57  tff(c_861, plain, (![B_5, C_96]: (k1_relset_1('#skF_5', B_5, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_710, c_855])).
% 3.49/1.57  tff(c_1872, plain, (![B_165, C_166]: (k1_relset_1('#skF_3', B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_889, c_861])).
% 3.49/1.57  tff(c_1878, plain, (![B_165]: (k1_relset_1('#skF_3', B_165, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_896, c_1872])).
% 3.49/1.57  tff(c_1882, plain, (![B_165]: (k1_relset_1('#skF_3', B_165, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_903, c_1878])).
% 3.49/1.57  tff(c_907, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_889, c_690])).
% 3.49/1.57  tff(c_28, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.49/1.57  tff(c_60, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 3.49/1.57  tff(c_920, plain, (![C_33, B_32]: (v1_funct_2(C_33, '#skF_3', B_32) | k1_relset_1('#skF_3', B_32, C_33)!='#skF_3' | ~m1_subset_1(C_33, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_907, c_907, c_907, c_60])).
% 3.49/1.57  tff(c_1024, plain, (![B_32]: (v1_funct_2('#skF_3', '#skF_3', B_32) | k1_relset_1('#skF_3', B_32, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_896, c_920])).
% 3.49/1.57  tff(c_1893, plain, (![B_32]: (v1_funct_2('#skF_3', '#skF_3', B_32))), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_1024])).
% 3.49/1.57  tff(c_910, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_889, c_58])).
% 3.49/1.57  tff(c_1897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1893, c_910])).
% 3.49/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.57  
% 3.49/1.57  Inference rules
% 3.49/1.57  ----------------------
% 3.49/1.57  #Ref     : 0
% 3.49/1.57  #Sup     : 418
% 3.49/1.57  #Fact    : 0
% 3.49/1.57  #Define  : 0
% 3.49/1.57  #Split   : 4
% 3.49/1.57  #Chain   : 0
% 3.49/1.57  #Close   : 0
% 3.49/1.57  
% 3.49/1.57  Ordering : KBO
% 3.49/1.57  
% 3.49/1.57  Simplification rules
% 3.49/1.57  ----------------------
% 3.49/1.57  #Subsume      : 75
% 3.49/1.57  #Demod        : 445
% 3.49/1.57  #Tautology    : 249
% 3.49/1.57  #SimpNegUnit  : 3
% 3.49/1.57  #BackRed      : 79
% 3.49/1.57  
% 3.49/1.57  #Partial instantiations: 0
% 3.49/1.57  #Strategies tried      : 1
% 3.49/1.57  
% 3.49/1.57  Timing (in seconds)
% 3.49/1.57  ----------------------
% 3.49/1.57  Preprocessing        : 0.32
% 3.49/1.57  Parsing              : 0.17
% 3.49/1.57  CNF conversion       : 0.02
% 3.49/1.57  Main loop            : 0.49
% 3.49/1.57  Inferencing          : 0.16
% 3.49/1.57  Reduction            : 0.17
% 3.49/1.57  Demodulation         : 0.13
% 3.49/1.57  BG Simplification    : 0.03
% 3.49/1.57  Subsumption          : 0.09
% 3.49/1.57  Abstraction          : 0.03
% 3.49/1.57  MUC search           : 0.00
% 3.49/1.57  Cooper               : 0.00
% 3.49/1.57  Total                : 0.85
% 3.49/1.58  Index Insertion      : 0.00
% 3.49/1.58  Index Deletion       : 0.00
% 3.49/1.58  Index Matching       : 0.00
% 3.49/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
