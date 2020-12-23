%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:13 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 386 expanded)
%              Number of leaves         :   29 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 (1036 expanded)
%              Number of equality atoms :   41 ( 172 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_46,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2127,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(A_175,B_176)
      | ~ m1_subset_1(A_175,k1_zfmisc_1(B_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2131,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_2127])).

tff(c_2208,plain,(
    ! [C_188,A_189,B_190] :
      ( r1_tarski(k2_zfmisc_1(C_188,A_189),k2_zfmisc_1(C_188,B_190))
      | ~ r1_tarski(A_189,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2402,plain,(
    ! [A_225,C_226,B_227,A_228] :
      ( r1_tarski(A_225,k2_zfmisc_1(C_226,B_227))
      | ~ r1_tarski(A_225,k2_zfmisc_1(C_226,A_228))
      | ~ r1_tarski(A_228,B_227) ) ),
    inference(resolution,[status(thm)],[c_2208,c_10])).

tff(c_2424,plain,(
    ! [B_229] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_229))
      | ~ r1_tarski('#skF_2',B_229) ) ),
    inference(resolution,[status(thm)],[c_2131,c_2402])).

tff(c_2132,plain,(
    ! [A_177,B_178] :
      ( m1_subset_1(A_177,k1_zfmisc_1(B_178))
      | ~ r1_tarski(A_177,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_59,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_224,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_233,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_224])).

tff(c_1046,plain,(
    ! [B_127,A_128,C_129] :
      ( k1_xboole_0 = B_127
      | k1_relset_1(A_128,B_127,C_129) = A_128
      | ~ v1_funct_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1053,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1046])).

tff(c_1057,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_233,c_1053])).

tff(c_1058,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1057])).

tff(c_60,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_64,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_145,plain,(
    ! [C_41,A_42,B_43] :
      ( r1_tarski(k2_zfmisc_1(C_41,A_42),k2_zfmisc_1(C_41,B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_480,plain,(
    ! [A_98,C_99,B_100,A_101] :
      ( r1_tarski(A_98,k2_zfmisc_1(C_99,B_100))
      | ~ r1_tarski(A_98,k2_zfmisc_1(C_99,A_101))
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_508,plain,(
    ! [B_102] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_102))
      | ~ r1_tarski('#skF_2',B_102) ) ),
    inference(resolution,[status(thm)],[c_64,c_480])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_232,plain,(
    ! [A_58,B_59,A_10] :
      ( k1_relset_1(A_58,B_59,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_20,c_224])).

tff(c_536,plain,(
    ! [B_103] :
      ( k1_relset_1('#skF_1',B_103,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_103) ) ),
    inference(resolution,[status(thm)],[c_508,c_232])).

tff(c_556,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_536])).

tff(c_1061,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_556])).

tff(c_150,plain,(
    ! [A_3,C_41,B_43,A_42] :
      ( r1_tarski(A_3,k2_zfmisc_1(C_41,B_43))
      | ~ r1_tarski(A_3,k2_zfmisc_1(C_41,A_42))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_561,plain,(
    ! [B_104,B_105] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_104))
      | ~ r1_tarski(B_105,B_104)
      | ~ r1_tarski('#skF_2',B_105) ) ),
    inference(resolution,[status(thm)],[c_508,c_150])).

tff(c_581,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_561])).

tff(c_593,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_581])).

tff(c_798,plain,(
    ! [B_114,C_115,A_116] :
      ( k1_xboole_0 = B_114
      | v1_funct_2(C_115,A_116,B_114)
      | k1_relset_1(A_116,B_114,C_115) != A_116
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1905,plain,(
    ! [B_172,A_173,A_174] :
      ( k1_xboole_0 = B_172
      | v1_funct_2(A_173,A_174,B_172)
      | k1_relset_1(A_174,B_172,A_173) != A_174
      | ~ r1_tarski(A_173,k2_zfmisc_1(A_174,B_172)) ) ),
    inference(resolution,[status(thm)],[c_20,c_798])).

tff(c_1932,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_593,c_1905])).

tff(c_1972,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1932])).

tff(c_1973,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1972])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_708,plain,(
    ! [B_110] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_110))
      | ~ r1_tarski('#skF_3',B_110) ) ),
    inference(resolution,[status(thm)],[c_593,c_150])).

tff(c_1379,plain,(
    ! [B_141,B_142] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_141))
      | ~ r1_tarski(B_142,B_141)
      | ~ r1_tarski('#skF_3',B_142) ) ),
    inference(resolution,[status(thm)],[c_708,c_150])).

tff(c_1435,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',A_6))
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_1379])).

tff(c_1471,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1435])).

tff(c_2003,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1471])).

tff(c_2022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2003])).

tff(c_2024,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1435])).

tff(c_70,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_2065,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2024,c_84])).

tff(c_590,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',A_6))
      | ~ r1_tarski('#skF_2',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_561])).

tff(c_625,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_2075,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2065,c_625])).

tff(c_2090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2075])).

tff(c_2092,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_2107,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2092,c_84])).

tff(c_2124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2107])).

tff(c_2125,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2140,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2132,c_2125])).

tff(c_2441,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2424,c_2140])).

tff(c_2452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2441])).

tff(c_2453,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2455,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2453,c_12])).

tff(c_2454,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2461,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2453,c_2454])).

tff(c_2470,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2461,c_48])).

tff(c_2472,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(A_233,B_234)
      | ~ m1_subset_1(A_233,k1_zfmisc_1(B_234)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2480,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2470,c_2472])).

tff(c_4496,plain,(
    ! [A_512,C_513,B_514] :
      ( r1_tarski(k2_zfmisc_1(A_512,C_513),k2_zfmisc_1(B_514,C_513))
      | ~ r1_tarski(A_512,B_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4660,plain,(
    ! [A_544,B_545,C_546,A_547] :
      ( r1_tarski(A_544,k2_zfmisc_1(B_545,C_546))
      | ~ r1_tarski(A_544,k2_zfmisc_1(A_547,C_546))
      | ~ r1_tarski(A_547,B_545) ) ),
    inference(resolution,[status(thm)],[c_4496,c_10])).

tff(c_4668,plain,(
    ! [B_545] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_545,'#skF_1'))
      | ~ r1_tarski('#skF_1',B_545) ) ),
    inference(resolution,[status(thm)],[c_2480,c_4660])).

tff(c_4682,plain,(
    ! [B_545] : r1_tarski('#skF_4',k2_zfmisc_1(B_545,'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_4668])).

tff(c_4486,plain,(
    ! [C_509,A_510,B_511] :
      ( r1_tarski(k2_zfmisc_1(C_509,A_510),k2_zfmisc_1(C_509,B_511))
      | ~ r1_tarski(A_510,B_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4818,plain,(
    ! [A_567,C_568,B_569,A_570] :
      ( r1_tarski(A_567,k2_zfmisc_1(C_568,B_569))
      | ~ r1_tarski(A_567,k2_zfmisc_1(C_568,A_570))
      | ~ r1_tarski(A_570,B_569) ) ),
    inference(resolution,[status(thm)],[c_4486,c_10])).

tff(c_4822,plain,(
    ! [B_545,B_569] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_545,B_569))
      | ~ r1_tarski('#skF_1',B_569) ) ),
    inference(resolution,[status(thm)],[c_4682,c_4818])).

tff(c_4838,plain,(
    ! [B_545,B_569] : r1_tarski('#skF_4',k2_zfmisc_1(B_545,B_569)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_4822])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2456,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2453,c_2])).

tff(c_2551,plain,(
    ! [C_250,A_251,B_252] :
      ( v1_partfun1(C_250,A_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ v1_xboole_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2558,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2470,c_2551])).

tff(c_2562,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2558])).

tff(c_2537,plain,(
    ! [C_244,A_245,B_246] :
      ( r1_tarski(k2_zfmisc_1(C_244,A_245),k2_zfmisc_1(C_244,B_246))
      | ~ r1_tarski(A_245,B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2726,plain,(
    ! [A_281,C_282,B_283,A_284] :
      ( r1_tarski(A_281,k2_zfmisc_1(C_282,B_283))
      | ~ r1_tarski(A_281,k2_zfmisc_1(C_282,A_284))
      | ~ r1_tarski(A_284,B_283) ) ),
    inference(resolution,[status(thm)],[c_2537,c_10])).

tff(c_2734,plain,(
    ! [B_283] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_283))
      | ~ r1_tarski('#skF_1',B_283) ) ),
    inference(resolution,[status(thm)],[c_2480,c_2726])).

tff(c_2748,plain,(
    ! [B_283] : r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_283)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_2734])).

tff(c_2544,plain,(
    ! [A_247,C_248,B_249] :
      ( r1_tarski(k2_zfmisc_1(A_247,C_248),k2_zfmisc_1(B_249,C_248))
      | ~ r1_tarski(A_247,B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2898,plain,(
    ! [A_303,B_304,C_305,A_306] :
      ( r1_tarski(A_303,k2_zfmisc_1(B_304,C_305))
      | ~ r1_tarski(A_303,k2_zfmisc_1(A_306,C_305))
      | ~ r1_tarski(A_306,B_304) ) ),
    inference(resolution,[status(thm)],[c_2544,c_10])).

tff(c_2902,plain,(
    ! [B_304,B_283] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_304,B_283))
      | ~ r1_tarski('#skF_1',B_304) ) ),
    inference(resolution,[status(thm)],[c_2748,c_2898])).

tff(c_2918,plain,(
    ! [B_304,B_283] : r1_tarski('#skF_4',k2_zfmisc_1(B_304,B_283)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_2902])).

tff(c_2993,plain,(
    ! [C_322,A_323,B_324] :
      ( v1_funct_2(C_322,A_323,B_324)
      | ~ v1_partfun1(C_322,A_323)
      | ~ v1_funct_1(C_322)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4383,plain,(
    ! [A_502,A_503,B_504] :
      ( v1_funct_2(A_502,A_503,B_504)
      | ~ v1_partfun1(A_502,A_503)
      | ~ v1_funct_1(A_502)
      | ~ r1_tarski(A_502,k2_zfmisc_1(A_503,B_504)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2993])).

tff(c_4413,plain,(
    ! [B_304,B_283] :
      ( v1_funct_2('#skF_4',B_304,B_283)
      | ~ v1_partfun1('#skF_4',B_304)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2918,c_4383])).

tff(c_4444,plain,(
    ! [B_505,B_506] :
      ( v1_funct_2('#skF_4',B_505,B_506)
      | ~ v1_partfun1('#skF_4',B_505) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4413])).

tff(c_2536,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4455,plain,(
    ~ v1_partfun1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4444,c_2536])).

tff(c_4464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_4455])).

tff(c_4465,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4470,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_4465])).

tff(c_4865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4838,c_4470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.27  
% 6.21/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.27  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.21/2.27  
% 6.21/2.27  %Foreground sorts:
% 6.21/2.27  
% 6.21/2.27  
% 6.21/2.27  %Background operators:
% 6.21/2.27  
% 6.21/2.27  
% 6.21/2.27  %Foreground operators:
% 6.21/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.21/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.21/2.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.21/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.21/2.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.21/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.21/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.21/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.21/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.21/2.27  
% 6.21/2.29  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 6.21/2.29  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.21/2.29  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 6.21/2.29  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.21/2.29  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.21/2.29  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.21/2.29  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.21/2.29  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.21/2.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.21/2.29  tff(f_71, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 6.21/2.29  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 6.21/2.29  tff(c_46, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.29  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.29  tff(c_2127, plain, (![A_175, B_176]: (r1_tarski(A_175, B_176) | ~m1_subset_1(A_175, k1_zfmisc_1(B_176)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.21/2.29  tff(c_2131, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_2127])).
% 6.21/2.29  tff(c_2208, plain, (![C_188, A_189, B_190]: (r1_tarski(k2_zfmisc_1(C_188, A_189), k2_zfmisc_1(C_188, B_190)) | ~r1_tarski(A_189, B_190))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.21/2.29  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.21/2.29  tff(c_2402, plain, (![A_225, C_226, B_227, A_228]: (r1_tarski(A_225, k2_zfmisc_1(C_226, B_227)) | ~r1_tarski(A_225, k2_zfmisc_1(C_226, A_228)) | ~r1_tarski(A_228, B_227))), inference(resolution, [status(thm)], [c_2208, c_10])).
% 6.21/2.29  tff(c_2424, plain, (![B_229]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_229)) | ~r1_tarski('#skF_2', B_229))), inference(resolution, [status(thm)], [c_2131, c_2402])).
% 6.21/2.29  tff(c_2132, plain, (![A_177, B_178]: (m1_subset_1(A_177, k1_zfmisc_1(B_178)) | ~r1_tarski(A_177, B_178))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.21/2.29  tff(c_44, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.29  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 6.21/2.29  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.21/2.29  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.29  tff(c_42, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.29  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 6.21/2.29  tff(c_59, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 6.21/2.29  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.29  tff(c_224, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.21/2.29  tff(c_233, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_224])).
% 6.21/2.29  tff(c_1046, plain, (![B_127, A_128, C_129]: (k1_xboole_0=B_127 | k1_relset_1(A_128, B_127, C_129)=A_128 | ~v1_funct_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.21/2.29  tff(c_1053, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_1046])).
% 6.21/2.29  tff(c_1057, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_233, c_1053])).
% 6.21/2.29  tff(c_1058, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_1057])).
% 6.21/2.29  tff(c_60, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.21/2.29  tff(c_64, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_60])).
% 6.21/2.29  tff(c_145, plain, (![C_41, A_42, B_43]: (r1_tarski(k2_zfmisc_1(C_41, A_42), k2_zfmisc_1(C_41, B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.21/2.29  tff(c_480, plain, (![A_98, C_99, B_100, A_101]: (r1_tarski(A_98, k2_zfmisc_1(C_99, B_100)) | ~r1_tarski(A_98, k2_zfmisc_1(C_99, A_101)) | ~r1_tarski(A_101, B_100))), inference(resolution, [status(thm)], [c_145, c_10])).
% 6.21/2.29  tff(c_508, plain, (![B_102]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_102)) | ~r1_tarski('#skF_2', B_102))), inference(resolution, [status(thm)], [c_64, c_480])).
% 6.21/2.29  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.21/2.29  tff(c_232, plain, (![A_58, B_59, A_10]: (k1_relset_1(A_58, B_59, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_58, B_59)))), inference(resolution, [status(thm)], [c_20, c_224])).
% 6.21/2.29  tff(c_536, plain, (![B_103]: (k1_relset_1('#skF_1', B_103, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_103))), inference(resolution, [status(thm)], [c_508, c_232])).
% 6.21/2.29  tff(c_556, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_536])).
% 6.21/2.29  tff(c_1061, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_556])).
% 6.21/2.29  tff(c_150, plain, (![A_3, C_41, B_43, A_42]: (r1_tarski(A_3, k2_zfmisc_1(C_41, B_43)) | ~r1_tarski(A_3, k2_zfmisc_1(C_41, A_42)) | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_145, c_10])).
% 6.21/2.29  tff(c_561, plain, (![B_104, B_105]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_104)) | ~r1_tarski(B_105, B_104) | ~r1_tarski('#skF_2', B_105))), inference(resolution, [status(thm)], [c_508, c_150])).
% 6.21/2.29  tff(c_581, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_561])).
% 6.21/2.29  tff(c_593, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_581])).
% 6.21/2.29  tff(c_798, plain, (![B_114, C_115, A_116]: (k1_xboole_0=B_114 | v1_funct_2(C_115, A_116, B_114) | k1_relset_1(A_116, B_114, C_115)!=A_116 | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_114))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.21/2.29  tff(c_1905, plain, (![B_172, A_173, A_174]: (k1_xboole_0=B_172 | v1_funct_2(A_173, A_174, B_172) | k1_relset_1(A_174, B_172, A_173)!=A_174 | ~r1_tarski(A_173, k2_zfmisc_1(A_174, B_172)))), inference(resolution, [status(thm)], [c_20, c_798])).
% 6.21/2.29  tff(c_1932, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_593, c_1905])).
% 6.21/2.29  tff(c_1972, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1932])).
% 6.21/2.29  tff(c_1973, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_59, c_1972])).
% 6.21/2.29  tff(c_12, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.21/2.29  tff(c_708, plain, (![B_110]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_110)) | ~r1_tarski('#skF_3', B_110))), inference(resolution, [status(thm)], [c_593, c_150])).
% 6.21/2.29  tff(c_1379, plain, (![B_141, B_142]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_141)) | ~r1_tarski(B_142, B_141) | ~r1_tarski('#skF_3', B_142))), inference(resolution, [status(thm)], [c_708, c_150])).
% 6.21/2.29  tff(c_1435, plain, (![A_6]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', A_6)) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1379])).
% 6.21/2.29  tff(c_1471, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1435])).
% 6.21/2.29  tff(c_2003, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1471])).
% 6.21/2.29  tff(c_2022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2003])).
% 6.21/2.29  tff(c_2024, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1435])).
% 6.21/2.29  tff(c_70, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.21/2.29  tff(c_84, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_70])).
% 6.21/2.29  tff(c_2065, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2024, c_84])).
% 6.21/2.29  tff(c_590, plain, (![A_6]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', A_6)) | ~r1_tarski('#skF_2', k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_561])).
% 6.21/2.29  tff(c_625, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_590])).
% 6.21/2.29  tff(c_2075, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2065, c_625])).
% 6.21/2.29  tff(c_2090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2075])).
% 6.21/2.29  tff(c_2092, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_590])).
% 6.21/2.29  tff(c_2107, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2092, c_84])).
% 6.21/2.29  tff(c_2124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2107])).
% 6.21/2.29  tff(c_2125, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_54])).
% 6.21/2.29  tff(c_2140, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_2132, c_2125])).
% 6.21/2.29  tff(c_2441, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2424, c_2140])).
% 6.21/2.29  tff(c_2452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2441])).
% 6.21/2.29  tff(c_2453, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_44])).
% 6.21/2.29  tff(c_2455, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2453, c_12])).
% 6.21/2.29  tff(c_2454, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 6.21/2.29  tff(c_2461, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2453, c_2454])).
% 6.21/2.29  tff(c_2470, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2461, c_48])).
% 6.21/2.29  tff(c_2472, plain, (![A_233, B_234]: (r1_tarski(A_233, B_234) | ~m1_subset_1(A_233, k1_zfmisc_1(B_234)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.21/2.29  tff(c_2480, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2470, c_2472])).
% 6.21/2.29  tff(c_4496, plain, (![A_512, C_513, B_514]: (r1_tarski(k2_zfmisc_1(A_512, C_513), k2_zfmisc_1(B_514, C_513)) | ~r1_tarski(A_512, B_514))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.21/2.29  tff(c_4660, plain, (![A_544, B_545, C_546, A_547]: (r1_tarski(A_544, k2_zfmisc_1(B_545, C_546)) | ~r1_tarski(A_544, k2_zfmisc_1(A_547, C_546)) | ~r1_tarski(A_547, B_545))), inference(resolution, [status(thm)], [c_4496, c_10])).
% 6.21/2.29  tff(c_4668, plain, (![B_545]: (r1_tarski('#skF_4', k2_zfmisc_1(B_545, '#skF_1')) | ~r1_tarski('#skF_1', B_545))), inference(resolution, [status(thm)], [c_2480, c_4660])).
% 6.21/2.29  tff(c_4682, plain, (![B_545]: (r1_tarski('#skF_4', k2_zfmisc_1(B_545, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_4668])).
% 6.21/2.29  tff(c_4486, plain, (![C_509, A_510, B_511]: (r1_tarski(k2_zfmisc_1(C_509, A_510), k2_zfmisc_1(C_509, B_511)) | ~r1_tarski(A_510, B_511))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.21/2.29  tff(c_4818, plain, (![A_567, C_568, B_569, A_570]: (r1_tarski(A_567, k2_zfmisc_1(C_568, B_569)) | ~r1_tarski(A_567, k2_zfmisc_1(C_568, A_570)) | ~r1_tarski(A_570, B_569))), inference(resolution, [status(thm)], [c_4486, c_10])).
% 6.21/2.29  tff(c_4822, plain, (![B_545, B_569]: (r1_tarski('#skF_4', k2_zfmisc_1(B_545, B_569)) | ~r1_tarski('#skF_1', B_569))), inference(resolution, [status(thm)], [c_4682, c_4818])).
% 6.21/2.29  tff(c_4838, plain, (![B_545, B_569]: (r1_tarski('#skF_4', k2_zfmisc_1(B_545, B_569)))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_4822])).
% 6.21/2.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.21/2.29  tff(c_2456, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2453, c_2])).
% 6.21/2.29  tff(c_2551, plain, (![C_250, A_251, B_252]: (v1_partfun1(C_250, A_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~v1_xboole_0(A_251))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.21/2.29  tff(c_2558, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2470, c_2551])).
% 6.21/2.29  tff(c_2562, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2558])).
% 6.21/2.29  tff(c_2537, plain, (![C_244, A_245, B_246]: (r1_tarski(k2_zfmisc_1(C_244, A_245), k2_zfmisc_1(C_244, B_246)) | ~r1_tarski(A_245, B_246))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.21/2.29  tff(c_2726, plain, (![A_281, C_282, B_283, A_284]: (r1_tarski(A_281, k2_zfmisc_1(C_282, B_283)) | ~r1_tarski(A_281, k2_zfmisc_1(C_282, A_284)) | ~r1_tarski(A_284, B_283))), inference(resolution, [status(thm)], [c_2537, c_10])).
% 6.21/2.29  tff(c_2734, plain, (![B_283]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_283)) | ~r1_tarski('#skF_1', B_283))), inference(resolution, [status(thm)], [c_2480, c_2726])).
% 6.21/2.29  tff(c_2748, plain, (![B_283]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_283)))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_2734])).
% 6.21/2.29  tff(c_2544, plain, (![A_247, C_248, B_249]: (r1_tarski(k2_zfmisc_1(A_247, C_248), k2_zfmisc_1(B_249, C_248)) | ~r1_tarski(A_247, B_249))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.21/2.29  tff(c_2898, plain, (![A_303, B_304, C_305, A_306]: (r1_tarski(A_303, k2_zfmisc_1(B_304, C_305)) | ~r1_tarski(A_303, k2_zfmisc_1(A_306, C_305)) | ~r1_tarski(A_306, B_304))), inference(resolution, [status(thm)], [c_2544, c_10])).
% 6.21/2.29  tff(c_2902, plain, (![B_304, B_283]: (r1_tarski('#skF_4', k2_zfmisc_1(B_304, B_283)) | ~r1_tarski('#skF_1', B_304))), inference(resolution, [status(thm)], [c_2748, c_2898])).
% 6.21/2.29  tff(c_2918, plain, (![B_304, B_283]: (r1_tarski('#skF_4', k2_zfmisc_1(B_304, B_283)))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_2902])).
% 6.21/2.29  tff(c_2993, plain, (![C_322, A_323, B_324]: (v1_funct_2(C_322, A_323, B_324) | ~v1_partfun1(C_322, A_323) | ~v1_funct_1(C_322) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.21/2.29  tff(c_4383, plain, (![A_502, A_503, B_504]: (v1_funct_2(A_502, A_503, B_504) | ~v1_partfun1(A_502, A_503) | ~v1_funct_1(A_502) | ~r1_tarski(A_502, k2_zfmisc_1(A_503, B_504)))), inference(resolution, [status(thm)], [c_20, c_2993])).
% 6.21/2.29  tff(c_4413, plain, (![B_304, B_283]: (v1_funct_2('#skF_4', B_304, B_283) | ~v1_partfun1('#skF_4', B_304) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2918, c_4383])).
% 6.21/2.29  tff(c_4444, plain, (![B_505, B_506]: (v1_funct_2('#skF_4', B_505, B_506) | ~v1_partfun1('#skF_4', B_505))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4413])).
% 6.21/2.29  tff(c_2536, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 6.21/2.29  tff(c_4455, plain, (~v1_partfun1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4444, c_2536])).
% 6.21/2.29  tff(c_4464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2562, c_4455])).
% 6.21/2.29  tff(c_4465, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_54])).
% 6.21/2.29  tff(c_4470, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_4465])).
% 6.21/2.29  tff(c_4865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4838, c_4470])).
% 6.21/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.29  
% 6.21/2.29  Inference rules
% 6.21/2.29  ----------------------
% 6.21/2.29  #Ref     : 0
% 6.21/2.29  #Sup     : 1082
% 6.21/2.29  #Fact    : 0
% 6.21/2.29  #Define  : 0
% 6.21/2.29  #Split   : 25
% 6.21/2.29  #Chain   : 0
% 6.21/2.29  #Close   : 0
% 6.21/2.29  
% 6.21/2.29  Ordering : KBO
% 6.21/2.29  
% 6.21/2.29  Simplification rules
% 6.21/2.29  ----------------------
% 6.21/2.29  #Subsume      : 310
% 6.21/2.29  #Demod        : 459
% 6.21/2.29  #Tautology    : 258
% 6.21/2.29  #SimpNegUnit  : 14
% 6.21/2.29  #BackRed      : 82
% 6.21/2.29  
% 6.21/2.29  #Partial instantiations: 0
% 6.21/2.29  #Strategies tried      : 1
% 6.21/2.29  
% 6.21/2.29  Timing (in seconds)
% 6.21/2.29  ----------------------
% 6.21/2.29  Preprocessing        : 0.34
% 6.21/2.29  Parsing              : 0.18
% 6.21/2.29  CNF conversion       : 0.02
% 6.21/2.29  Main loop            : 1.08
% 6.21/2.29  Inferencing          : 0.36
% 6.21/2.29  Reduction            : 0.32
% 6.21/2.29  Demodulation         : 0.21
% 6.21/2.29  BG Simplification    : 0.04
% 6.21/2.29  Subsumption          : 0.28
% 6.21/2.29  Abstraction          : 0.05
% 6.21/2.29  MUC search           : 0.00
% 6.21/2.30  Cooper               : 0.00
% 6.21/2.30  Total                : 1.47
% 6.21/2.30  Index Insertion      : 0.00
% 6.21/2.30  Index Deletion       : 0.00
% 6.21/2.30  Index Matching       : 0.00
% 6.21/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
