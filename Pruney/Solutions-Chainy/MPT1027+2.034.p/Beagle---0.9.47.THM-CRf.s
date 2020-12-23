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
% DateTime   : Thu Dec  3 10:16:46 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   95 (1257 expanded)
%              Number of leaves         :   34 ( 417 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 (3153 expanded)
%              Number of equality atoms :   48 ( 789 expanded)
%              Maximal formula depth    :   13 (   3 average)
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

tff(f_72,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_118,negated_conjecture,(
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

tff(f_90,axiom,(
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

tff(f_105,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | ~ v1_xboole_0(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_341,plain,(
    ! [C_60,B_61,A_62] :
      ( ~ v1_xboole_0(C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_357,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_62,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_341])).

tff(c_412,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_416,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_412])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_58,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50])).

tff(c_52,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_818,plain,(
    ! [B_98,C_99,A_100] :
      ( k1_xboole_0 = B_98
      | v1_funct_2(C_99,A_100,B_98)
      | k1_relset_1(A_100,B_98,C_99) != A_100
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_830,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_818])).

tff(c_841,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_830])).

tff(c_842,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_841])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_880,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_2])).

tff(c_882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_880])).

tff(c_885,plain,(
    ! [A_101] : ~ r2_hidden(A_101,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_890,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_885])).

tff(c_99,plain,(
    ! [A_39] :
      ( v1_xboole_0(k1_relat_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_106,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) = k1_xboole_0
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_114,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_908,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_890,c_114])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_27] :
      ( v1_funct_2(k1_xboole_0,A_27,k1_xboole_0)
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_27,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    ! [A_27] :
      ( v1_funct_2(k1_xboole_0,A_27,k1_xboole_0)
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_397,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [A_46] : m1_subset_1('#skF_2'(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_147,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_345,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_62,'#skF_2'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_147,c_341])).

tff(c_358,plain,(
    ! [A_63] : ~ r2_hidden(A_63,'#skF_2'(k1_xboole_0)) ),
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

tff(c_893,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_890,c_405])).

tff(c_884,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_1015,plain,(
    ! [A_107] :
      ( A_107 = '#skF_5'
      | ~ v1_xboole_0(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_4])).

tff(c_1028,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_884,c_1015])).

tff(c_1055,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1084,plain,(
    ! [C_112] :
      ( k1_relset_1('#skF_3','#skF_4',C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_1055])).

tff(c_1087,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_893,c_1084])).

tff(c_1089,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_52,c_1087])).

tff(c_1103,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1089,c_908])).

tff(c_1096,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1089,c_893])).

tff(c_910,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_5',B_5) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_890,c_12])).

tff(c_1061,plain,(
    ! [B_5,C_110] :
      ( k1_relset_1('#skF_5',B_5,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_1055])).

tff(c_2072,plain,(
    ! [B_178,C_179] :
      ( k1_relset_1('#skF_3',B_178,C_179) = k1_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1089,c_1061])).

tff(c_2078,plain,(
    ! [B_178] : k1_relset_1('#skF_3',B_178,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1096,c_2072])).

tff(c_2082,plain,(
    ! [B_178] : k1_relset_1('#skF_3',B_178,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_2078])).

tff(c_1107,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_890])).

tff(c_28,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,k1_xboole_0,B_28)
      | k1_relset_1(k1_xboole_0,B_28,C_29) != k1_xboole_0
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_1120,plain,(
    ! [C_29,B_28] :
      ( v1_funct_2(C_29,'#skF_3',B_28)
      | k1_relset_1('#skF_3',B_28,C_29) != '#skF_3'
      | ~ m1_subset_1(C_29,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1107,c_1107,c_1107,c_60])).

tff(c_1224,plain,(
    ! [B_28] :
      ( v1_funct_2('#skF_3','#skF_3',B_28)
      | k1_relset_1('#skF_3',B_28,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1096,c_1120])).

tff(c_2093,plain,(
    ! [B_28] : v1_funct_2('#skF_3','#skF_3',B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2082,c_1224])).

tff(c_1110,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_58])).

tff(c_2097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_1110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.61  
% 3.49/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.61  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.49/1.61  
% 3.49/1.61  %Foreground sorts:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Background operators:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Foreground operators:
% 3.49/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.49/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.49/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.61  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.49/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.61  
% 3.82/1.63  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: (((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_mcart_1)).
% 3.82/1.63  tff(f_34, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.82/1.63  tff(f_118, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.82/1.63  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.82/1.63  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.82/1.63  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.82/1.63  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.82/1.63  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.82/1.63  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.82/1.63  tff(f_105, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_funct_2)).
% 3.82/1.63  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.82/1.63  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_1'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.63  tff(c_6, plain, (![A_2, B_3]: (v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | ~v1_xboole_0(B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.82/1.63  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.82/1.63  tff(c_341, plain, (![C_60, B_61, A_62]: (~v1_xboole_0(C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.63  tff(c_357, plain, (![A_62]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_62, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_341])).
% 3.82/1.63  tff(c_412, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_357])).
% 3.82/1.63  tff(c_416, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6, c_412])).
% 3.82/1.63  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.82/1.63  tff(c_50, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.82/1.63  tff(c_58, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50])).
% 3.82/1.63  tff(c_52, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.82/1.63  tff(c_818, plain, (![B_98, C_99, A_100]: (k1_xboole_0=B_98 | v1_funct_2(C_99, A_100, B_98) | k1_relset_1(A_100, B_98, C_99)!=A_100 | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_98))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.82/1.63  tff(c_830, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_54, c_818])).
% 3.82/1.63  tff(c_841, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_830])).
% 3.82/1.63  tff(c_842, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_841])).
% 3.82/1.63  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.82/1.63  tff(c_880, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_2])).
% 3.82/1.63  tff(c_882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_416, c_880])).
% 3.82/1.63  tff(c_885, plain, (![A_101]: (~r2_hidden(A_101, '#skF_5'))), inference(splitRight, [status(thm)], [c_357])).
% 3.82/1.63  tff(c_890, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_885])).
% 3.82/1.63  tff(c_99, plain, (![A_39]: (v1_xboole_0(k1_relat_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/1.63  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.82/1.63  tff(c_106, plain, (![A_42]: (k1_relat_1(A_42)=k1_xboole_0 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_99, c_4])).
% 3.82/1.63  tff(c_114, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_106])).
% 3.82/1.63  tff(c_908, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_890, c_890, c_114])).
% 3.82/1.63  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.82/1.63  tff(c_24, plain, (![A_27]: (v1_funct_2(k1_xboole_0, A_27, k1_xboole_0) | k1_xboole_0=A_27 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_27, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.82/1.63  tff(c_62, plain, (![A_27]: (v1_funct_2(k1_xboole_0, A_27, k1_xboole_0) | k1_xboole_0=A_27 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 3.82/1.63  tff(c_397, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_62])).
% 3.82/1.63  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.82/1.63  tff(c_143, plain, (![A_46]: (m1_subset_1('#skF_2'(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.82/1.63  tff(c_147, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_143])).
% 3.82/1.63  tff(c_345, plain, (![A_62]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_62, '#skF_2'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_147, c_341])).
% 3.82/1.63  tff(c_358, plain, (![A_63]: (~r2_hidden(A_63, '#skF_2'(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_345])).
% 3.82/1.63  tff(c_363, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_358])).
% 3.82/1.63  tff(c_365, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_147])).
% 3.82/1.63  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_365])).
% 3.82/1.63  tff(c_405, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_62])).
% 3.82/1.63  tff(c_893, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_890, c_890, c_405])).
% 3.82/1.63  tff(c_884, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_357])).
% 3.82/1.63  tff(c_1015, plain, (![A_107]: (A_107='#skF_5' | ~v1_xboole_0(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_890, c_4])).
% 3.82/1.63  tff(c_1028, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_884, c_1015])).
% 3.82/1.63  tff(c_1055, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.82/1.63  tff(c_1084, plain, (![C_112]: (k1_relset_1('#skF_3', '#skF_4', C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1028, c_1055])).
% 3.82/1.63  tff(c_1087, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_893, c_1084])).
% 3.82/1.63  tff(c_1089, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_908, c_52, c_1087])).
% 3.82/1.63  tff(c_1103, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1089, c_908])).
% 3.82/1.63  tff(c_1096, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1089, c_893])).
% 3.82/1.63  tff(c_910, plain, (![B_5]: (k2_zfmisc_1('#skF_5', B_5)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_890, c_890, c_12])).
% 3.82/1.63  tff(c_1061, plain, (![B_5, C_110]: (k1_relset_1('#skF_5', B_5, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_910, c_1055])).
% 3.82/1.63  tff(c_2072, plain, (![B_178, C_179]: (k1_relset_1('#skF_3', B_178, C_179)=k1_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1089, c_1061])).
% 3.82/1.63  tff(c_2078, plain, (![B_178]: (k1_relset_1('#skF_3', B_178, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1096, c_2072])).
% 3.82/1.63  tff(c_2082, plain, (![B_178]: (k1_relset_1('#skF_3', B_178, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_2078])).
% 3.82/1.63  tff(c_1107, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_890])).
% 3.82/1.63  tff(c_28, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.82/1.63  tff(c_60, plain, (![C_29, B_28]: (v1_funct_2(C_29, k1_xboole_0, B_28) | k1_relset_1(k1_xboole_0, B_28, C_29)!=k1_xboole_0 | ~m1_subset_1(C_29, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 3.82/1.63  tff(c_1120, plain, (![C_29, B_28]: (v1_funct_2(C_29, '#skF_3', B_28) | k1_relset_1('#skF_3', B_28, C_29)!='#skF_3' | ~m1_subset_1(C_29, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1107, c_1107, c_1107, c_60])).
% 3.82/1.63  tff(c_1224, plain, (![B_28]: (v1_funct_2('#skF_3', '#skF_3', B_28) | k1_relset_1('#skF_3', B_28, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_1096, c_1120])).
% 3.82/1.63  tff(c_2093, plain, (![B_28]: (v1_funct_2('#skF_3', '#skF_3', B_28))), inference(demodulation, [status(thm), theory('equality')], [c_2082, c_1224])).
% 3.82/1.63  tff(c_1110, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_58])).
% 3.82/1.63  tff(c_2097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2093, c_1110])).
% 3.82/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.63  
% 3.82/1.63  Inference rules
% 3.82/1.63  ----------------------
% 3.82/1.63  #Ref     : 0
% 3.82/1.63  #Sup     : 467
% 3.82/1.63  #Fact    : 0
% 3.82/1.63  #Define  : 0
% 3.82/1.63  #Split   : 4
% 3.82/1.63  #Chain   : 0
% 3.82/1.63  #Close   : 0
% 3.82/1.63  
% 3.82/1.63  Ordering : KBO
% 3.82/1.63  
% 3.82/1.63  Simplification rules
% 3.82/1.63  ----------------------
% 3.82/1.63  #Subsume      : 86
% 3.82/1.63  #Demod        : 493
% 3.82/1.63  #Tautology    : 272
% 3.82/1.63  #SimpNegUnit  : 3
% 3.82/1.63  #BackRed      : 87
% 3.82/1.63  
% 3.82/1.63  #Partial instantiations: 0
% 3.82/1.63  #Strategies tried      : 1
% 3.82/1.63  
% 3.82/1.63  Timing (in seconds)
% 3.82/1.63  ----------------------
% 3.82/1.63  Preprocessing        : 0.34
% 3.82/1.63  Parsing              : 0.17
% 3.82/1.64  CNF conversion       : 0.02
% 3.82/1.64  Main loop            : 0.53
% 3.82/1.64  Inferencing          : 0.18
% 3.82/1.64  Reduction            : 0.18
% 3.82/1.64  Demodulation         : 0.13
% 3.82/1.64  BG Simplification    : 0.03
% 3.82/1.64  Subsumption          : 0.10
% 3.82/1.64  Abstraction          : 0.03
% 3.82/1.64  MUC search           : 0.00
% 3.82/1.64  Cooper               : 0.00
% 3.82/1.64  Total                : 0.91
% 3.82/1.64  Index Insertion      : 0.00
% 3.82/1.64  Index Deletion       : 0.00
% 3.82/1.64  Index Matching       : 0.00
% 3.82/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
