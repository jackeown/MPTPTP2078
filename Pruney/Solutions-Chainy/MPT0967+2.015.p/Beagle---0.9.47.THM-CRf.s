%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:15 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 374 expanded)
%              Number of leaves         :   30 ( 132 expanded)
%              Depth                    :    9
%              Number of atoms          :  223 (1197 expanded)
%              Number of equality atoms :   55 ( 348 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_73,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_1924,plain,(
    ! [C_216,B_217,A_218] :
      ( v5_relat_1(C_216,B_217)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_218,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1933,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1924])).

tff(c_2054,plain,(
    ! [B_244,A_245] :
      ( r1_tarski(k2_relat_1(B_244),A_245)
      | ~ v5_relat_1(B_244,A_245)
      | ~ v1_relat_1(B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1970,plain,(
    ! [A_229,C_230,B_231] :
      ( r1_tarski(A_229,C_230)
      | ~ r1_tarski(B_231,C_230)
      | ~ r1_tarski(A_229,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1982,plain,(
    ! [A_229] :
      ( r1_tarski(A_229,'#skF_3')
      | ~ r1_tarski(A_229,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_1970])).

tff(c_2091,plain,(
    ! [B_244] :
      ( r1_tarski(k2_relat_1(B_244),'#skF_3')
      | ~ v5_relat_1(B_244,'#skF_2')
      | ~ v1_relat_1(B_244) ) ),
    inference(resolution,[status(thm)],[c_2054,c_1982])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2350,plain,(
    ! [A_264,B_265,C_266] :
      ( k1_relset_1(A_264,B_265,C_266) = k1_relat_1(C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2359,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2350])).

tff(c_3497,plain,(
    ! [B_367,A_368,C_369] :
      ( k1_xboole_0 = B_367
      | k1_relset_1(A_368,B_367,C_369) = A_368
      | ~ v1_funct_2(C_369,A_368,B_367)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_368,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3507,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_3497])).

tff(c_3512,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2359,c_3507])).

tff(c_3513,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3512])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_24),A_23)))
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3521,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_23)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_23)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3513,c_40])).

tff(c_3601,plain,(
    ! [A_375] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_375)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_56,c_3521])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46])).

tff(c_130,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_279,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_288,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_279])).

tff(c_237,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k2_relat_1(B_63),A_64)
      | ~ v5_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_157,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,'#skF_3')
      | ~ r1_tarski(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_157])).

tff(c_270,plain,(
    ! [B_63] :
      ( r1_tarski(k2_relat_1(B_63),'#skF_3')
      | ~ v5_relat_1(B_63,'#skF_2')
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_237,c_169])).

tff(c_381,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_390,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_381])).

tff(c_1838,plain,(
    ! [B_209,A_210,C_211] :
      ( k1_xboole_0 = B_209
      | k1_relset_1(A_210,B_209,C_211) = A_210
      | ~ v1_funct_2(C_211,A_210,B_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1848,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1838])).

tff(c_1853,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_390,c_1848])).

tff(c_1854,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1853])).

tff(c_42,plain,(
    ! [B_24,A_23] :
      ( v1_funct_2(B_24,k1_relat_1(B_24),A_23)
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1865,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_4','#skF_1',A_23)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_23)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_42])).

tff(c_1879,plain,(
    ! [A_212] :
      ( v1_funct_2('#skF_4','#skF_1',A_212)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_56,c_1865])).

tff(c_1887,plain,
    ( v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_270,c_1879])).

tff(c_1905,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_288,c_1887])).

tff(c_1907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1905])).

tff(c_1908,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3638,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3601,c_1908])).

tff(c_3647,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2091,c_3638])).

tff(c_3657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1933,c_3647])).

tff(c_3658,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3659,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3665,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_3659])).

tff(c_3666,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3665,c_52])).

tff(c_5119,plain,(
    ! [C_527,A_528,B_529] :
      ( v1_relat_1(C_527)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_528,B_529))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5128,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3666,c_5119])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3660,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_10])).

tff(c_5284,plain,(
    ! [C_559,B_560,A_561] :
      ( v5_relat_1(C_559,B_560)
      | ~ m1_subset_1(C_559,k1_zfmisc_1(k2_zfmisc_1(A_561,B_560))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5293,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3666,c_5284])).

tff(c_5217,plain,(
    ! [B_545,A_546] :
      ( r1_tarski(k2_relat_1(B_545),A_546)
      | ~ v5_relat_1(B_545,A_546)
      | ~ v1_relat_1(B_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5145,plain,(
    ! [B_533,A_534] :
      ( B_533 = A_534
      | ~ r1_tarski(B_533,A_534)
      | ~ r1_tarski(A_534,B_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5153,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3660,c_5145])).

tff(c_5240,plain,(
    ! [B_545] :
      ( k2_relat_1(B_545) = '#skF_1'
      | ~ v5_relat_1(B_545,'#skF_1')
      | ~ v1_relat_1(B_545) ) ),
    inference(resolution,[status(thm)],[c_5217,c_5153])).

tff(c_5296,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5293,c_5240])).

tff(c_5299,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5128,c_5296])).

tff(c_3667,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3665,c_54])).

tff(c_5609,plain,(
    ! [A_587,B_588,C_589] :
      ( k1_relset_1(A_587,B_588,C_589) = k1_relat_1(C_589)
      | ~ m1_subset_1(C_589,k1_zfmisc_1(k2_zfmisc_1(A_587,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5618,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3666,c_5609])).

tff(c_36,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1(k1_xboole_0,B_21,C_22) = k1_xboole_0
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6891,plain,(
    ! [B_685,C_686] :
      ( k1_relset_1('#skF_1',B_685,C_686) = '#skF_1'
      | ~ v1_funct_2(C_686,'#skF_1',B_685)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_685))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_3658,c_3658,c_3658,c_36])).

tff(c_6898,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3666,c_6891])).

tff(c_6902,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3667,c_5618,c_6898])).

tff(c_6912,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_23)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_23)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6902,c_40])).

tff(c_6921,plain,(
    ! [A_23] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5128,c_56,c_3660,c_5299,c_6912])).

tff(c_3712,plain,(
    ! [C_384,A_385,B_386] :
      ( v1_relat_1(C_384)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3721,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3666,c_3712])).

tff(c_3796,plain,(
    ! [C_402,B_403,A_404] :
      ( v5_relat_1(C_402,B_403)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(A_404,B_403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3805,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3666,c_3796])).

tff(c_3806,plain,(
    ! [B_405,A_406] :
      ( r1_tarski(k2_relat_1(B_405),A_406)
      | ~ v5_relat_1(B_405,A_406)
      | ~ v1_relat_1(B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3686,plain,(
    ! [B_381,A_382] :
      ( B_381 = A_382
      | ~ r1_tarski(B_381,A_382)
      | ~ r1_tarski(A_382,B_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3694,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3660,c_3686])).

tff(c_3865,plain,(
    ! [B_414] :
      ( k2_relat_1(B_414) = '#skF_1'
      | ~ v5_relat_1(B_414,'#skF_1')
      | ~ v1_relat_1(B_414) ) ),
    inference(resolution,[status(thm)],[c_3806,c_3694])).

tff(c_3879,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3805,c_3865])).

tff(c_3889,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3721,c_3879])).

tff(c_4022,plain,(
    ! [A_430,B_431,C_432] :
      ( k1_relset_1(A_430,B_431,C_432) = k1_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4031,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3666,c_4022])).

tff(c_5082,plain,(
    ! [B_525,C_526] :
      ( k1_relset_1('#skF_1',B_525,C_526) = '#skF_1'
      | ~ v1_funct_2(C_526,'#skF_1',B_525)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_525))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_3658,c_3658,c_3658,c_36])).

tff(c_5089,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3666,c_5082])).

tff(c_5093,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3667,c_4031,c_5089])).

tff(c_5101,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_4','#skF_1',A_23)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_23)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5093,c_42])).

tff(c_5107,plain,(
    ! [A_23] : v1_funct_2('#skF_4','#skF_1',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3721,c_56,c_3660,c_3889,c_5101])).

tff(c_3685,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_5112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5107,c_3685])).

tff(c_5113,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_5113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.20  
% 6.21/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.20  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.21/2.20  
% 6.21/2.20  %Foreground sorts:
% 6.21/2.20  
% 6.21/2.20  
% 6.21/2.20  %Background operators:
% 6.21/2.20  
% 6.21/2.20  
% 6.21/2.20  %Foreground operators:
% 6.21/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.21/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.21/2.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.21/2.20  tff('#skF_2', type, '#skF_2': $i).
% 6.21/2.20  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.20  tff('#skF_1', type, '#skF_1': $i).
% 6.21/2.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.21/2.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.21/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.21/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.21/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.21/2.20  tff('#skF_4', type, '#skF_4': $i).
% 6.21/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.21/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.21/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.21/2.20  
% 6.21/2.22  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 6.21/2.22  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.21/2.22  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.21/2.22  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.21/2.22  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.21/2.22  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.21/2.22  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.21/2.22  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.21/2.22  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.21/2.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.21/2.22  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.21/2.22  tff(c_73, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.22  tff(c_82, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_73])).
% 6.21/2.22  tff(c_1924, plain, (![C_216, B_217, A_218]: (v5_relat_1(C_216, B_217) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_218, B_217))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.21/2.22  tff(c_1933, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_1924])).
% 6.21/2.22  tff(c_2054, plain, (![B_244, A_245]: (r1_tarski(k2_relat_1(B_244), A_245) | ~v5_relat_1(B_244, A_245) | ~v1_relat_1(B_244))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.21/2.22  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.21/2.22  tff(c_1970, plain, (![A_229, C_230, B_231]: (r1_tarski(A_229, C_230) | ~r1_tarski(B_231, C_230) | ~r1_tarski(A_229, B_231))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.21/2.22  tff(c_1982, plain, (![A_229]: (r1_tarski(A_229, '#skF_3') | ~r1_tarski(A_229, '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1970])).
% 6.21/2.22  tff(c_2091, plain, (![B_244]: (r1_tarski(k2_relat_1(B_244), '#skF_3') | ~v5_relat_1(B_244, '#skF_2') | ~v1_relat_1(B_244))), inference(resolution, [status(thm)], [c_2054, c_1982])).
% 6.21/2.22  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.21/2.22  tff(c_48, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.21/2.22  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 6.21/2.22  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.21/2.22  tff(c_2350, plain, (![A_264, B_265, C_266]: (k1_relset_1(A_264, B_265, C_266)=k1_relat_1(C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.21/2.22  tff(c_2359, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_2350])).
% 6.21/2.22  tff(c_3497, plain, (![B_367, A_368, C_369]: (k1_xboole_0=B_367 | k1_relset_1(A_368, B_367, C_369)=A_368 | ~v1_funct_2(C_369, A_368, B_367) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_368, B_367))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.21/2.22  tff(c_3507, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_3497])).
% 6.21/2.22  tff(c_3512, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2359, c_3507])).
% 6.21/2.22  tff(c_3513, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_3512])).
% 6.21/2.22  tff(c_40, plain, (![B_24, A_23]: (m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_24), A_23))) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.21/2.22  tff(c_3521, plain, (![A_23]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_23))) | ~r1_tarski(k2_relat_1('#skF_4'), A_23) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3513, c_40])).
% 6.21/2.22  tff(c_3601, plain, (![A_375]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_375))) | ~r1_tarski(k2_relat_1('#skF_4'), A_375))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_56, c_3521])).
% 6.21/2.22  tff(c_46, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.21/2.22  tff(c_58, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46])).
% 6.21/2.22  tff(c_130, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 6.21/2.22  tff(c_279, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.21/2.22  tff(c_288, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_279])).
% 6.21/2.22  tff(c_237, plain, (![B_63, A_64]: (r1_tarski(k2_relat_1(B_63), A_64) | ~v5_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.21/2.22  tff(c_157, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.21/2.22  tff(c_169, plain, (![A_48]: (r1_tarski(A_48, '#skF_3') | ~r1_tarski(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_157])).
% 6.21/2.22  tff(c_270, plain, (![B_63]: (r1_tarski(k2_relat_1(B_63), '#skF_3') | ~v5_relat_1(B_63, '#skF_2') | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_237, c_169])).
% 6.21/2.22  tff(c_381, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.21/2.22  tff(c_390, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_381])).
% 6.21/2.22  tff(c_1838, plain, (![B_209, A_210, C_211]: (k1_xboole_0=B_209 | k1_relset_1(A_210, B_209, C_211)=A_210 | ~v1_funct_2(C_211, A_210, B_209) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.21/2.22  tff(c_1848, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_1838])).
% 6.21/2.22  tff(c_1853, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_390, c_1848])).
% 6.21/2.22  tff(c_1854, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_1853])).
% 6.21/2.22  tff(c_42, plain, (![B_24, A_23]: (v1_funct_2(B_24, k1_relat_1(B_24), A_23) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.21/2.22  tff(c_1865, plain, (![A_23]: (v1_funct_2('#skF_4', '#skF_1', A_23) | ~r1_tarski(k2_relat_1('#skF_4'), A_23) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_42])).
% 6.21/2.22  tff(c_1879, plain, (![A_212]: (v1_funct_2('#skF_4', '#skF_1', A_212) | ~r1_tarski(k2_relat_1('#skF_4'), A_212))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_56, c_1865])).
% 6.21/2.22  tff(c_1887, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_270, c_1879])).
% 6.21/2.22  tff(c_1905, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_288, c_1887])).
% 6.21/2.22  tff(c_1907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_1905])).
% 6.21/2.22  tff(c_1908, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_58])).
% 6.21/2.22  tff(c_3638, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_3601, c_1908])).
% 6.21/2.22  tff(c_3647, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2091, c_3638])).
% 6.21/2.22  tff(c_3657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1933, c_3647])).
% 6.21/2.22  tff(c_3658, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 6.21/2.22  tff(c_3659, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 6.21/2.22  tff(c_3665, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_3659])).
% 6.21/2.22  tff(c_3666, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3665, c_52])).
% 6.21/2.22  tff(c_5119, plain, (![C_527, A_528, B_529]: (v1_relat_1(C_527) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_528, B_529))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.22  tff(c_5128, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3666, c_5119])).
% 6.21/2.22  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.21/2.22  tff(c_3660, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_10])).
% 6.21/2.22  tff(c_5284, plain, (![C_559, B_560, A_561]: (v5_relat_1(C_559, B_560) | ~m1_subset_1(C_559, k1_zfmisc_1(k2_zfmisc_1(A_561, B_560))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.21/2.22  tff(c_5293, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3666, c_5284])).
% 6.21/2.22  tff(c_5217, plain, (![B_545, A_546]: (r1_tarski(k2_relat_1(B_545), A_546) | ~v5_relat_1(B_545, A_546) | ~v1_relat_1(B_545))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.21/2.22  tff(c_5145, plain, (![B_533, A_534]: (B_533=A_534 | ~r1_tarski(B_533, A_534) | ~r1_tarski(A_534, B_533))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.22  tff(c_5153, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_3660, c_5145])).
% 6.21/2.22  tff(c_5240, plain, (![B_545]: (k2_relat_1(B_545)='#skF_1' | ~v5_relat_1(B_545, '#skF_1') | ~v1_relat_1(B_545))), inference(resolution, [status(thm)], [c_5217, c_5153])).
% 6.21/2.22  tff(c_5296, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5293, c_5240])).
% 6.21/2.22  tff(c_5299, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5128, c_5296])).
% 6.21/2.22  tff(c_3667, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3665, c_54])).
% 6.21/2.22  tff(c_5609, plain, (![A_587, B_588, C_589]: (k1_relset_1(A_587, B_588, C_589)=k1_relat_1(C_589) | ~m1_subset_1(C_589, k1_zfmisc_1(k2_zfmisc_1(A_587, B_588))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.21/2.22  tff(c_5618, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3666, c_5609])).
% 6.21/2.22  tff(c_36, plain, (![B_21, C_22]: (k1_relset_1(k1_xboole_0, B_21, C_22)=k1_xboole_0 | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.21/2.22  tff(c_6891, plain, (![B_685, C_686]: (k1_relset_1('#skF_1', B_685, C_686)='#skF_1' | ~v1_funct_2(C_686, '#skF_1', B_685) | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_685))))), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_3658, c_3658, c_3658, c_36])).
% 6.21/2.22  tff(c_6898, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3666, c_6891])).
% 6.21/2.22  tff(c_6902, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3667, c_5618, c_6898])).
% 6.21/2.22  tff(c_6912, plain, (![A_23]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_23))) | ~r1_tarski(k2_relat_1('#skF_4'), A_23) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6902, c_40])).
% 6.21/2.22  tff(c_6921, plain, (![A_23]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_5128, c_56, c_3660, c_5299, c_6912])).
% 6.21/2.22  tff(c_3712, plain, (![C_384, A_385, B_386]: (v1_relat_1(C_384) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.22  tff(c_3721, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3666, c_3712])).
% 6.21/2.22  tff(c_3796, plain, (![C_402, B_403, A_404]: (v5_relat_1(C_402, B_403) | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(A_404, B_403))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.21/2.22  tff(c_3805, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3666, c_3796])).
% 6.21/2.22  tff(c_3806, plain, (![B_405, A_406]: (r1_tarski(k2_relat_1(B_405), A_406) | ~v5_relat_1(B_405, A_406) | ~v1_relat_1(B_405))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.21/2.22  tff(c_3686, plain, (![B_381, A_382]: (B_381=A_382 | ~r1_tarski(B_381, A_382) | ~r1_tarski(A_382, B_381))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.22  tff(c_3694, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_3660, c_3686])).
% 6.21/2.22  tff(c_3865, plain, (![B_414]: (k2_relat_1(B_414)='#skF_1' | ~v5_relat_1(B_414, '#skF_1') | ~v1_relat_1(B_414))), inference(resolution, [status(thm)], [c_3806, c_3694])).
% 6.21/2.22  tff(c_3879, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3805, c_3865])).
% 6.21/2.22  tff(c_3889, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3721, c_3879])).
% 6.21/2.22  tff(c_4022, plain, (![A_430, B_431, C_432]: (k1_relset_1(A_430, B_431, C_432)=k1_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.21/2.22  tff(c_4031, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3666, c_4022])).
% 6.21/2.22  tff(c_5082, plain, (![B_525, C_526]: (k1_relset_1('#skF_1', B_525, C_526)='#skF_1' | ~v1_funct_2(C_526, '#skF_1', B_525) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_525))))), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_3658, c_3658, c_3658, c_36])).
% 6.21/2.22  tff(c_5089, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3666, c_5082])).
% 6.21/2.22  tff(c_5093, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3667, c_4031, c_5089])).
% 6.21/2.22  tff(c_5101, plain, (![A_23]: (v1_funct_2('#skF_4', '#skF_1', A_23) | ~r1_tarski(k2_relat_1('#skF_4'), A_23) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5093, c_42])).
% 6.21/2.22  tff(c_5107, plain, (![A_23]: (v1_funct_2('#skF_4', '#skF_1', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_3721, c_56, c_3660, c_3889, c_5101])).
% 6.21/2.22  tff(c_3685, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 6.21/2.22  tff(c_5112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5107, c_3685])).
% 6.21/2.22  tff(c_5113, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_58])).
% 6.21/2.22  tff(c_6935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6921, c_5113])).
% 6.21/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.22  
% 6.21/2.22  Inference rules
% 6.21/2.22  ----------------------
% 6.21/2.22  #Ref     : 0
% 6.21/2.22  #Sup     : 1365
% 6.21/2.22  #Fact    : 0
% 6.21/2.22  #Define  : 0
% 6.21/2.22  #Split   : 12
% 6.21/2.22  #Chain   : 0
% 6.21/2.22  #Close   : 0
% 6.21/2.22  
% 6.21/2.22  Ordering : KBO
% 6.21/2.22  
% 6.21/2.22  Simplification rules
% 6.21/2.22  ----------------------
% 6.21/2.22  #Subsume      : 211
% 6.21/2.22  #Demod        : 1767
% 6.21/2.22  #Tautology    : 682
% 6.21/2.22  #SimpNegUnit  : 5
% 6.21/2.22  #BackRed      : 11
% 6.21/2.22  
% 6.21/2.22  #Partial instantiations: 0
% 6.21/2.22  #Strategies tried      : 1
% 6.21/2.22  
% 6.21/2.22  Timing (in seconds)
% 6.21/2.22  ----------------------
% 6.21/2.22  Preprocessing        : 0.33
% 6.21/2.22  Parsing              : 0.18
% 6.21/2.22  CNF conversion       : 0.02
% 6.21/2.22  Main loop            : 1.11
% 6.21/2.22  Inferencing          : 0.39
% 6.21/2.22  Reduction            : 0.40
% 6.21/2.22  Demodulation         : 0.30
% 6.21/2.22  BG Simplification    : 0.03
% 6.21/2.22  Subsumption          : 0.20
% 6.21/2.22  Abstraction          : 0.04
% 6.21/2.22  MUC search           : 0.00
% 6.21/2.22  Cooper               : 0.00
% 6.21/2.22  Total                : 1.48
% 6.21/2.22  Index Insertion      : 0.00
% 6.21/2.22  Index Deletion       : 0.00
% 6.21/2.22  Index Matching       : 0.00
% 6.21/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
