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
% DateTime   : Thu Dec  3 10:15:01 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 264 expanded)
%              Number of leaves         :   47 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 525 expanded)
%              Number of equality atoms :   38 ( 113 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_36,plain,(
    ! [A_42,B_43] : v1_relat_1(k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_125,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_131,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_125])).

tff(c_138,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_131])).

tff(c_50,plain,(
    ! [B_52,A_51] :
      ( r1_tarski(k7_relat_1(B_52,A_51),B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(A_32,k1_zfmisc_1(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_192,plain,(
    ! [A_86,B_87] :
      ( v1_relat_1(A_86)
      | ~ v1_relat_1(B_87)
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_26,c_125])).

tff(c_210,plain,(
    ! [B_52,A_51] :
      ( v1_relat_1(k7_relat_1(B_52,A_51))
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_50,c_192])).

tff(c_38,plain,(
    ! [B_45,A_44] :
      ( k2_relat_1(k7_relat_1(B_45,A_44)) = k9_relat_1(B_45,A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1267,plain,(
    ! [A_250,B_251] :
      ( r1_tarski(k2_relat_1(A_250),k2_relat_1(B_251))
      | ~ r1_tarski(A_250,B_251)
      | ~ v1_relat_1(B_251)
      | ~ v1_relat_1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2502,plain,(
    ! [B_399,A_400,B_401] :
      ( r1_tarski(k9_relat_1(B_399,A_400),k2_relat_1(B_401))
      | ~ r1_tarski(k7_relat_1(B_399,A_400),B_401)
      | ~ v1_relat_1(B_401)
      | ~ v1_relat_1(k7_relat_1(B_399,A_400))
      | ~ v1_relat_1(B_399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1267])).

tff(c_48,plain,(
    ! [A_50] :
      ( k1_relat_1(A_50) != k1_xboole_0
      | k1_xboole_0 = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_146,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_138,c_48])).

tff(c_164,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1472,plain,(
    ! [B_282,A_283] :
      ( k1_tarski(k1_funct_1(B_282,A_283)) = k2_relat_1(B_282)
      | k1_tarski(A_283) != k1_relat_1(B_282)
      | ~ v1_funct_1(B_282)
      | ~ v1_relat_1(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1442,plain,(
    ! [A_274,B_275,C_276,D_277] :
      ( k7_relset_1(A_274,B_275,C_276,D_277) = k9_relat_1(C_276,D_277)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1452,plain,(
    ! [D_277] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_277) = k9_relat_1('#skF_4',D_277) ),
    inference(resolution,[status(thm)],[c_64,c_1442])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1462,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_60])).

tff(c_1478,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1472,c_1462])).

tff(c_1493,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_68,c_1478])).

tff(c_1495,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1493])).

tff(c_245,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_258,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_245])).

tff(c_222,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v4_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [B_30,A_29] :
      ( k1_tarski(B_30) = A_29
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1603,plain,(
    ! [B_310,B_311] :
      ( k1_tarski(B_310) = k1_relat_1(B_311)
      | k1_relat_1(B_311) = k1_xboole_0
      | ~ v4_relat_1(B_311,k1_tarski(B_310))
      | ~ v1_relat_1(B_311) ) ),
    inference(resolution,[status(thm)],[c_222,c_16])).

tff(c_1613,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_258,c_1603])).

tff(c_1621,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1613])).

tff(c_1623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_1495,c_1621])).

tff(c_1624,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1493])).

tff(c_2509,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2502,c_1624])).

tff(c_2526,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2509])).

tff(c_2532,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2526])).

tff(c_2535,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_210,c_2532])).

tff(c_2539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2535])).

tff(c_2540,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2526])).

tff(c_2560,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2540])).

tff(c_2564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2560])).

tff(c_2565,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_22,plain,(
    ! [A_31] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_110,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [A_31] : r1_tarski(k1_xboole_0,A_31) ),
    inference(resolution,[status(thm)],[c_22,c_110])).

tff(c_2568,plain,(
    ! [A_31] : r1_tarski('#skF_4',A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_122])).

tff(c_40,plain,(
    ! [A_46] : k9_relat_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2572,plain,(
    ! [A_46] : k9_relat_1('#skF_4',A_46) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2565,c_40])).

tff(c_2571,plain,(
    ! [A_31] : m1_subset_1('#skF_4',k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_22])).

tff(c_3067,plain,(
    ! [A_499,B_500,C_501,D_502] :
      ( k7_relset_1(A_499,B_500,C_501,D_502) = k9_relat_1(C_501,D_502)
      | ~ m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1(A_499,B_500))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3070,plain,(
    ! [A_499,B_500,D_502] : k7_relset_1(A_499,B_500,'#skF_4',D_502) = k9_relat_1('#skF_4',D_502) ),
    inference(resolution,[status(thm)],[c_2571,c_3067])).

tff(c_3075,plain,(
    ! [A_499,B_500,D_502] : k7_relset_1(A_499,B_500,'#skF_4',D_502) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2572,c_3070])).

tff(c_3077,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_60])).

tff(c_3080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2568,c_3077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:22:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.92  
% 5.29/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.92  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.29/1.92  
% 5.29/1.92  %Foreground sorts:
% 5.29/1.92  
% 5.29/1.92  
% 5.29/1.92  %Background operators:
% 5.29/1.92  
% 5.29/1.92  
% 5.29/1.92  %Foreground operators:
% 5.29/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.29/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.29/1.92  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.29/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.29/1.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.29/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.29/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.29/1.92  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.29/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.29/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.29/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.29/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.29/1.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.29/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.29/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.29/1.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.29/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.29/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/1.92  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.29/1.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.29/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.29/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.29/1.92  tff('#skF_4', type, '#skF_4': $i).
% 5.29/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.29/1.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.29/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.29/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/1.93  
% 5.29/1.94  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.29/1.94  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.29/1.94  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.29/1.94  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 5.29/1.94  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.29/1.94  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.29/1.94  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.29/1.94  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.29/1.94  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.29/1.94  tff(f_119, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.29/1.94  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.29/1.94  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.29/1.94  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.29/1.94  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.29/1.94  tff(f_78, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 5.29/1.94  tff(c_36, plain, (![A_42, B_43]: (v1_relat_1(k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.29/1.94  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.29/1.94  tff(c_125, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.29/1.94  tff(c_131, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_125])).
% 5.29/1.94  tff(c_138, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_131])).
% 5.29/1.94  tff(c_50, plain, (![B_52, A_51]: (r1_tarski(k7_relat_1(B_52, A_51), B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.29/1.94  tff(c_26, plain, (![A_32, B_33]: (m1_subset_1(A_32, k1_zfmisc_1(B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.29/1.94  tff(c_192, plain, (![A_86, B_87]: (v1_relat_1(A_86) | ~v1_relat_1(B_87) | ~r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_26, c_125])).
% 5.29/1.94  tff(c_210, plain, (![B_52, A_51]: (v1_relat_1(k7_relat_1(B_52, A_51)) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_50, c_192])).
% 5.29/1.94  tff(c_38, plain, (![B_45, A_44]: (k2_relat_1(k7_relat_1(B_45, A_44))=k9_relat_1(B_45, A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.29/1.94  tff(c_1267, plain, (![A_250, B_251]: (r1_tarski(k2_relat_1(A_250), k2_relat_1(B_251)) | ~r1_tarski(A_250, B_251) | ~v1_relat_1(B_251) | ~v1_relat_1(A_250))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.29/1.94  tff(c_2502, plain, (![B_399, A_400, B_401]: (r1_tarski(k9_relat_1(B_399, A_400), k2_relat_1(B_401)) | ~r1_tarski(k7_relat_1(B_399, A_400), B_401) | ~v1_relat_1(B_401) | ~v1_relat_1(k7_relat_1(B_399, A_400)) | ~v1_relat_1(B_399))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1267])).
% 5.29/1.94  tff(c_48, plain, (![A_50]: (k1_relat_1(A_50)!=k1_xboole_0 | k1_xboole_0=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.29/1.94  tff(c_146, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_138, c_48])).
% 5.29/1.94  tff(c_164, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 5.29/1.94  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.29/1.94  tff(c_1472, plain, (![B_282, A_283]: (k1_tarski(k1_funct_1(B_282, A_283))=k2_relat_1(B_282) | k1_tarski(A_283)!=k1_relat_1(B_282) | ~v1_funct_1(B_282) | ~v1_relat_1(B_282))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.29/1.94  tff(c_1442, plain, (![A_274, B_275, C_276, D_277]: (k7_relset_1(A_274, B_275, C_276, D_277)=k9_relat_1(C_276, D_277) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.29/1.94  tff(c_1452, plain, (![D_277]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_277)=k9_relat_1('#skF_4', D_277))), inference(resolution, [status(thm)], [c_64, c_1442])).
% 5.29/1.94  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.29/1.94  tff(c_1462, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_60])).
% 5.29/1.94  tff(c_1478, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1472, c_1462])).
% 5.29/1.94  tff(c_1493, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_68, c_1478])).
% 5.29/1.94  tff(c_1495, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1493])).
% 5.29/1.94  tff(c_245, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.29/1.94  tff(c_258, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_245])).
% 5.29/1.94  tff(c_222, plain, (![B_92, A_93]: (r1_tarski(k1_relat_1(B_92), A_93) | ~v4_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.29/1.94  tff(c_16, plain, (![B_30, A_29]: (k1_tarski(B_30)=A_29 | k1_xboole_0=A_29 | ~r1_tarski(A_29, k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.29/1.94  tff(c_1603, plain, (![B_310, B_311]: (k1_tarski(B_310)=k1_relat_1(B_311) | k1_relat_1(B_311)=k1_xboole_0 | ~v4_relat_1(B_311, k1_tarski(B_310)) | ~v1_relat_1(B_311))), inference(resolution, [status(thm)], [c_222, c_16])).
% 5.29/1.94  tff(c_1613, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_258, c_1603])).
% 5.29/1.94  tff(c_1621, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1613])).
% 5.29/1.94  tff(c_1623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_1495, c_1621])).
% 5.29/1.94  tff(c_1624, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1493])).
% 5.29/1.94  tff(c_2509, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2502, c_1624])).
% 5.29/1.94  tff(c_2526, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_2509])).
% 5.29/1.94  tff(c_2532, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2526])).
% 5.29/1.94  tff(c_2535, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_210, c_2532])).
% 5.29/1.94  tff(c_2539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_2535])).
% 5.29/1.94  tff(c_2540, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_2526])).
% 5.29/1.94  tff(c_2560, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2540])).
% 5.29/1.94  tff(c_2564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_2560])).
% 5.29/1.94  tff(c_2565, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_146])).
% 5.29/1.94  tff(c_22, plain, (![A_31]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.29/1.94  tff(c_110, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.29/1.94  tff(c_122, plain, (![A_31]: (r1_tarski(k1_xboole_0, A_31))), inference(resolution, [status(thm)], [c_22, c_110])).
% 5.29/1.94  tff(c_2568, plain, (![A_31]: (r1_tarski('#skF_4', A_31))), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_122])).
% 5.29/1.94  tff(c_40, plain, (![A_46]: (k9_relat_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.29/1.94  tff(c_2572, plain, (![A_46]: (k9_relat_1('#skF_4', A_46)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2565, c_40])).
% 5.29/1.94  tff(c_2571, plain, (![A_31]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_22])).
% 5.29/1.94  tff(c_3067, plain, (![A_499, B_500, C_501, D_502]: (k7_relset_1(A_499, B_500, C_501, D_502)=k9_relat_1(C_501, D_502) | ~m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1(A_499, B_500))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.29/1.94  tff(c_3070, plain, (![A_499, B_500, D_502]: (k7_relset_1(A_499, B_500, '#skF_4', D_502)=k9_relat_1('#skF_4', D_502))), inference(resolution, [status(thm)], [c_2571, c_3067])).
% 5.29/1.94  tff(c_3075, plain, (![A_499, B_500, D_502]: (k7_relset_1(A_499, B_500, '#skF_4', D_502)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2572, c_3070])).
% 5.29/1.94  tff(c_3077, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_60])).
% 5.29/1.94  tff(c_3080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2568, c_3077])).
% 5.29/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.94  
% 5.29/1.94  Inference rules
% 5.29/1.94  ----------------------
% 5.29/1.94  #Ref     : 0
% 5.29/1.94  #Sup     : 613
% 5.29/1.94  #Fact    : 2
% 5.29/1.94  #Define  : 0
% 5.29/1.94  #Split   : 15
% 5.29/1.94  #Chain   : 0
% 5.29/1.94  #Close   : 0
% 5.29/1.94  
% 5.29/1.94  Ordering : KBO
% 5.29/1.94  
% 5.29/1.94  Simplification rules
% 5.29/1.94  ----------------------
% 5.29/1.94  #Subsume      : 114
% 5.29/1.94  #Demod        : 548
% 5.29/1.94  #Tautology    : 258
% 5.29/1.94  #SimpNegUnit  : 71
% 5.29/1.94  #BackRed      : 57
% 5.29/1.94  
% 5.29/1.94  #Partial instantiations: 0
% 5.29/1.94  #Strategies tried      : 1
% 5.29/1.94  
% 5.29/1.94  Timing (in seconds)
% 5.29/1.94  ----------------------
% 5.29/1.94  Preprocessing        : 0.34
% 5.29/1.94  Parsing              : 0.18
% 5.29/1.94  CNF conversion       : 0.02
% 5.29/1.94  Main loop            : 0.84
% 5.29/1.94  Inferencing          : 0.30
% 5.29/1.94  Reduction            : 0.26
% 5.29/1.94  Demodulation         : 0.18
% 5.29/1.94  BG Simplification    : 0.03
% 5.29/1.94  Subsumption          : 0.17
% 5.29/1.94  Abstraction          : 0.04
% 5.29/1.94  MUC search           : 0.00
% 5.29/1.94  Cooper               : 0.00
% 5.29/1.95  Total                : 1.22
% 5.29/1.95  Index Insertion      : 0.00
% 5.29/1.95  Index Deletion       : 0.00
% 5.29/1.95  Index Matching       : 0.00
% 5.29/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
