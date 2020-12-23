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
% DateTime   : Thu Dec  3 10:12:51 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  179 (1769 expanded)
%              Number of leaves         :   35 ( 602 expanded)
%              Depth                    :   15
%              Number of atoms          :  352 (5996 expanded)
%              Number of equality atoms :  107 (1835 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_93,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_96,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_93])).

tff(c_99,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_22,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2697,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2700,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2697])).

tff(c_2704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_2700])).

tff(c_2705,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5411,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2705])).

tff(c_5477,plain,(
    ! [A_295,B_296,C_297] :
      ( k1_relset_1(A_295,B_296,C_297) = k1_relat_1(C_297)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5490,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_5477])).

tff(c_7503,plain,(
    ! [B_388,A_389,C_390] :
      ( k1_xboole_0 = B_388
      | k1_relset_1(A_389,B_388,C_390) = A_389
      | ~ v1_funct_2(C_390,A_389,B_388)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_389,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7521,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_7503])).

tff(c_7535,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5490,c_7521])).

tff(c_7536,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7535])).

tff(c_32,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5499,plain,(
    ! [A_298,B_299,C_300] :
      ( k2_relset_1(A_298,B_299,C_300) = k2_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5508,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_5499])).

tff(c_5513,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5508])).

tff(c_5426,plain,(
    ! [A_293] :
      ( k1_relat_1(k2_funct_1(A_293)) = k2_relat_1(A_293)
      | ~ v2_funct_1(A_293)
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [B_38,A_39] :
      ( v4_relat_1(B_38,A_39)
      | ~ r1_tarski(k1_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [B_38] :
      ( v4_relat_1(B_38,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_5666,plain,(
    ! [A_311] :
      ( v4_relat_1(k2_funct_1(A_311),k2_relat_1(A_311))
      | ~ v1_relat_1(k2_funct_1(A_311))
      | ~ v2_funct_1(A_311)
      | ~ v1_funct_1(A_311)
      | ~ v1_relat_1(A_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5426,c_132])).

tff(c_5669,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5513,c_5666])).

tff(c_5677,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_68,c_5669])).

tff(c_5680,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5677])).

tff(c_5683,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_5680])).

tff(c_5687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_5683])).

tff(c_5689,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5677])).

tff(c_2706,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5688,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5677])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7982,plain,(
    ! [A_414,A_415] :
      ( r1_tarski(k2_relat_1(A_414),A_415)
      | ~ v4_relat_1(k2_funct_1(A_414),A_415)
      | ~ v1_relat_1(k2_funct_1(A_414))
      | ~ v2_funct_1(A_414)
      | ~ v1_funct_1(A_414)
      | ~ v1_relat_1(A_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5426,c_14])).

tff(c_8049,plain,(
    ! [A_418] :
      ( r1_tarski(k2_relat_1(A_418),k1_relat_1(k2_funct_1(A_418)))
      | ~ v2_funct_1(A_418)
      | ~ v1_funct_1(A_418)
      | ~ v1_relat_1(A_418)
      | ~ v1_relat_1(k2_funct_1(A_418)) ) ),
    inference(resolution,[status(thm)],[c_132,c_7982])).

tff(c_8064,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5513,c_8049])).

tff(c_8081,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_99,c_74,c_68,c_8064])).

tff(c_2713,plain,(
    ! [B_164,A_165] :
      ( r1_tarski(k1_relat_1(B_164),A_165)
      | ~ v4_relat_1(B_164,A_165)
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2728,plain,(
    ! [B_164,A_165] :
      ( k1_relat_1(B_164) = A_165
      | ~ r1_tarski(A_165,k1_relat_1(B_164))
      | ~ v4_relat_1(B_164,A_165)
      | ~ v1_relat_1(B_164) ) ),
    inference(resolution,[status(thm)],[c_2713,c_2])).

tff(c_8093,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8081,c_2728])).

tff(c_8103,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_5688,c_8093])).

tff(c_52,plain,(
    ! [A_23] :
      ( m1_subset_1(A_23,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_23),k2_relat_1(A_23))))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8146,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8103,c_52])).

tff(c_8184,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_2706,c_8146])).

tff(c_8304,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8184])).

tff(c_8318,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_68,c_7536,c_8304])).

tff(c_8320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5411,c_8318])).

tff(c_8321,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7535])).

tff(c_42,plain,(
    ! [C_22,A_20] :
      ( k1_xboole_0 = C_22
      | ~ v1_funct_2(C_22,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8713,plain,(
    ! [C_433,A_434] :
      ( C_433 = '#skF_2'
      | ~ v1_funct_2(C_433,A_434,'#skF_2')
      | A_434 = '#skF_2'
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(A_434,'#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8321,c_8321,c_8321,c_8321,c_42])).

tff(c_8727,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_70,c_8713])).

tff(c_8738,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8727])).

tff(c_8739,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8738])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8350,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8321,c_8321,c_20])).

tff(c_8762,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8739,c_8739,c_8350])).

tff(c_8322,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7535])).

tff(c_54,plain,(
    ! [A_23] :
      ( v1_funct_2(A_23,k1_relat_1(A_23),k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5520,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5513,c_54])).

tff(c_5526,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_5520])).

tff(c_5517,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5513,c_52])).

tff(c_5524,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_5517])).

tff(c_8724,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5524,c_8713])).

tff(c_8735,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_8724])).

tff(c_9129,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8739,c_8739,c_8735])).

tff(c_9130,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_8322,c_9129])).

tff(c_9138,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9130,c_8322])).

tff(c_9152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8762,c_9138])).

tff(c_9153,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8738])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8348,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8321,c_8])).

tff(c_9175,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9153,c_8348])).

tff(c_9177,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9153,c_9153,c_8350])).

tff(c_8438,plain,(
    ! [A_422] : r1_tarski('#skF_2',A_422) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8321,c_8])).

tff(c_8447,plain,(
    ! [A_423] :
      ( A_423 = '#skF_2'
      | ~ r1_tarski(A_423,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8438,c_2])).

tff(c_8534,plain,(
    ! [B_427] :
      ( k1_relat_1(B_427) = '#skF_2'
      | ~ v4_relat_1(B_427,'#skF_2')
      | ~ v1_relat_1(B_427) ) ),
    inference(resolution,[status(thm)],[c_14,c_8447])).

tff(c_8545,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5688,c_8534])).

tff(c_8554,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_8545])).

tff(c_58,plain,(
    ! [B_25,A_24] :
      ( m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_25),A_24)))
      | ~ r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8558,plain,(
    ! [A_24] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_24)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_24)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8554,c_58])).

tff(c_8595,plain,(
    ! [A_24] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_24)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5689,c_2706,c_8558])).

tff(c_9748,plain,(
    ! [A_476] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_476)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9153,c_8595])).

tff(c_9188,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9153,c_5411])).

tff(c_9778,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_9748,c_9188])).

tff(c_9792,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_9778])).

tff(c_9795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_68,c_9175,c_9177,c_9792])).

tff(c_9796,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2705])).

tff(c_9839,plain,(
    ! [A_479,B_480,C_481] :
      ( k1_relset_1(A_479,B_480,C_481) = k1_relat_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_479,B_480))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9847,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_9839])).

tff(c_10285,plain,(
    ! [B_512,A_513,C_514] :
      ( k1_xboole_0 = B_512
      | k1_relset_1(A_513,B_512,C_514) = A_513
      | ~ v1_funct_2(C_514,A_513,B_512)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_513,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10303,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_10285])).

tff(c_10316,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9847,c_10303])).

tff(c_10317,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10316])).

tff(c_9797,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2705])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( v1_relat_1(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9802,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_9797,c_10])).

tff(c_9805,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_9802])).

tff(c_9898,plain,(
    ! [A_483,B_484,C_485] :
      ( k2_relset_1(A_483,B_484,C_485) = k2_relat_1(C_485)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(A_483,B_484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9910,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_9898])).

tff(c_9916,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9910])).

tff(c_34,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9846,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9797,c_9839])).

tff(c_10414,plain,(
    ! [B_518,C_519,A_520] :
      ( k1_xboole_0 = B_518
      | v1_funct_2(C_519,A_520,B_518)
      | k1_relset_1(A_520,B_518,C_519) != A_520
      | ~ m1_subset_1(C_519,k1_zfmisc_1(k2_zfmisc_1(A_520,B_518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10426,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_9797,c_10414])).

tff(c_10436,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9846,c_10426])).

tff(c_10437,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_9796,c_10436])).

tff(c_10441,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10437])).

tff(c_10444,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10441])).

tff(c_10447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_68,c_9916,c_10444])).

tff(c_10449,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10437])).

tff(c_10498,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10449,c_54])).

tff(c_10528,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9805,c_2706,c_10498])).

tff(c_10733,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10528])).

tff(c_10735,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_68,c_10317,c_10733])).

tff(c_10737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9796,c_10735])).

tff(c_10739,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10316])).

tff(c_10738,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10316])).

tff(c_46,plain,(
    ! [B_21,C_22,A_20] :
      ( k1_xboole_0 = B_21
      | v1_funct_2(C_22,A_20,B_21)
      | k1_relset_1(A_20,B_21,C_22) != A_20
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10801,plain,(
    ! [B_531,C_532,A_533] :
      ( B_531 = '#skF_2'
      | v1_funct_2(C_532,A_533,B_531)
      | k1_relset_1(A_533,B_531,C_532) != A_533
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_533,B_531))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10738,c_46])).

tff(c_10813,plain,
    ( '#skF_2' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_9797,c_10801])).

tff(c_10824,plain,
    ( '#skF_2' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9846,c_10813])).

tff(c_10825,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_9796,c_10824])).

tff(c_10896,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10825])).

tff(c_10901,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10896])).

tff(c_10904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_74,c_68,c_9916,c_10901])).

tff(c_10905,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10825])).

tff(c_10930,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10905,c_72])).

tff(c_10925,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10905,c_9847])).

tff(c_10928,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10905,c_70])).

tff(c_48,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1(k1_xboole_0,B_21,C_22) = k1_xboole_0
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10742,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1('#skF_2',B_21,C_22) = '#skF_2'
      | ~ v1_funct_2(C_22,'#skF_2',B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_21))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10738,c_10738,c_10738,c_10738,c_48])).

tff(c_11281,plain,(
    ! [B_547,C_548] :
      ( k1_relset_1('#skF_1',B_547,C_548) = '#skF_1'
      | ~ v1_funct_2(C_548,'#skF_1',B_547)
      | ~ m1_subset_1(C_548,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_547))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10905,c_10905,c_10905,c_10905,c_10742])).

tff(c_11284,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10928,c_11281])).

tff(c_11290,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10930,c_10925,c_11284])).

tff(c_11292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10739,c_11290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.64  
% 7.49/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.64  %$ v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.49/2.64  
% 7.49/2.64  %Foreground sorts:
% 7.49/2.64  
% 7.49/2.64  
% 7.49/2.64  %Background operators:
% 7.49/2.64  
% 7.49/2.64  
% 7.49/2.64  %Foreground operators:
% 7.49/2.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.49/2.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.49/2.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.49/2.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.49/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.49/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.49/2.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.49/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.49/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.64  tff('#skF_1', type, '#skF_1': $i).
% 7.49/2.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.49/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.49/2.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.49/2.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.49/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.64  
% 7.71/2.66  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.71/2.66  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.71/2.66  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.71/2.66  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.71/2.66  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.71/2.66  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.71/2.66  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.71/2.66  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.71/2.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.71/2.66  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.71/2.66  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.71/2.66  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.71/2.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.71/2.66  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 7.71/2.66  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.71/2.66  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.71/2.66  tff(c_93, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.71/2.66  tff(c_96, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_93])).
% 7.71/2.66  tff(c_99, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96])).
% 7.71/2.66  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.71/2.66  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.71/2.66  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.71/2.66  tff(c_22, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.71/2.66  tff(c_64, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.71/2.66  tff(c_2697, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 7.71/2.66  tff(c_2700, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2697])).
% 7.71/2.66  tff(c_2704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_2700])).
% 7.71/2.66  tff(c_2705, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 7.71/2.66  tff(c_5411, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2705])).
% 7.71/2.66  tff(c_5477, plain, (![A_295, B_296, C_297]: (k1_relset_1(A_295, B_296, C_297)=k1_relat_1(C_297) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.71/2.66  tff(c_5490, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_5477])).
% 7.71/2.66  tff(c_7503, plain, (![B_388, A_389, C_390]: (k1_xboole_0=B_388 | k1_relset_1(A_389, B_388, C_390)=A_389 | ~v1_funct_2(C_390, A_389, B_388) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_389, B_388))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.71/2.66  tff(c_7521, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_7503])).
% 7.71/2.66  tff(c_7535, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5490, c_7521])).
% 7.71/2.66  tff(c_7536, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_7535])).
% 7.71/2.66  tff(c_32, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.71/2.66  tff(c_24, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.71/2.66  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.71/2.66  tff(c_5499, plain, (![A_298, B_299, C_300]: (k2_relset_1(A_298, B_299, C_300)=k2_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.71/2.66  tff(c_5508, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_5499])).
% 7.71/2.66  tff(c_5513, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5508])).
% 7.71/2.66  tff(c_5426, plain, (![A_293]: (k1_relat_1(k2_funct_1(A_293))=k2_relat_1(A_293) | ~v2_funct_1(A_293) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.71/2.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.71/2.66  tff(c_124, plain, (![B_38, A_39]: (v4_relat_1(B_38, A_39) | ~r1_tarski(k1_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.71/2.66  tff(c_132, plain, (![B_38]: (v4_relat_1(B_38, k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_6, c_124])).
% 7.71/2.66  tff(c_5666, plain, (![A_311]: (v4_relat_1(k2_funct_1(A_311), k2_relat_1(A_311)) | ~v1_relat_1(k2_funct_1(A_311)) | ~v2_funct_1(A_311) | ~v1_funct_1(A_311) | ~v1_relat_1(A_311))), inference(superposition, [status(thm), theory('equality')], [c_5426, c_132])).
% 7.71/2.66  tff(c_5669, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5513, c_5666])).
% 7.71/2.66  tff(c_5677, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_68, c_5669])).
% 7.71/2.66  tff(c_5680, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5677])).
% 7.71/2.66  tff(c_5683, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_5680])).
% 7.71/2.66  tff(c_5687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_5683])).
% 7.71/2.66  tff(c_5689, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5677])).
% 7.71/2.66  tff(c_2706, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 7.71/2.66  tff(c_5688, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_5677])).
% 7.71/2.66  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.71/2.66  tff(c_7982, plain, (![A_414, A_415]: (r1_tarski(k2_relat_1(A_414), A_415) | ~v4_relat_1(k2_funct_1(A_414), A_415) | ~v1_relat_1(k2_funct_1(A_414)) | ~v2_funct_1(A_414) | ~v1_funct_1(A_414) | ~v1_relat_1(A_414))), inference(superposition, [status(thm), theory('equality')], [c_5426, c_14])).
% 7.71/2.66  tff(c_8049, plain, (![A_418]: (r1_tarski(k2_relat_1(A_418), k1_relat_1(k2_funct_1(A_418))) | ~v2_funct_1(A_418) | ~v1_funct_1(A_418) | ~v1_relat_1(A_418) | ~v1_relat_1(k2_funct_1(A_418)))), inference(resolution, [status(thm)], [c_132, c_7982])).
% 7.71/2.66  tff(c_8064, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5513, c_8049])).
% 7.71/2.66  tff(c_8081, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_99, c_74, c_68, c_8064])).
% 7.71/2.66  tff(c_2713, plain, (![B_164, A_165]: (r1_tarski(k1_relat_1(B_164), A_165) | ~v4_relat_1(B_164, A_165) | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.71/2.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.71/2.66  tff(c_2728, plain, (![B_164, A_165]: (k1_relat_1(B_164)=A_165 | ~r1_tarski(A_165, k1_relat_1(B_164)) | ~v4_relat_1(B_164, A_165) | ~v1_relat_1(B_164))), inference(resolution, [status(thm)], [c_2713, c_2])).
% 7.71/2.66  tff(c_8093, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8081, c_2728])).
% 7.71/2.66  tff(c_8103, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_5688, c_8093])).
% 7.71/2.66  tff(c_52, plain, (![A_23]: (m1_subset_1(A_23, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_23), k2_relat_1(A_23)))) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.71/2.66  tff(c_8146, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8103, c_52])).
% 7.71/2.66  tff(c_8184, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_2706, c_8146])).
% 7.71/2.66  tff(c_8304, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_8184])).
% 7.71/2.66  tff(c_8318, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_68, c_7536, c_8304])).
% 7.71/2.66  tff(c_8320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5411, c_8318])).
% 7.71/2.66  tff(c_8321, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7535])).
% 7.71/2.66  tff(c_42, plain, (![C_22, A_20]: (k1_xboole_0=C_22 | ~v1_funct_2(C_22, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.71/2.66  tff(c_8713, plain, (![C_433, A_434]: (C_433='#skF_2' | ~v1_funct_2(C_433, A_434, '#skF_2') | A_434='#skF_2' | ~m1_subset_1(C_433, k1_zfmisc_1(k2_zfmisc_1(A_434, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_8321, c_8321, c_8321, c_8321, c_42])).
% 7.71/2.66  tff(c_8727, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_70, c_8713])).
% 7.71/2.66  tff(c_8738, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8727])).
% 7.71/2.66  tff(c_8739, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_8738])).
% 7.71/2.66  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.71/2.66  tff(c_8350, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8321, c_8321, c_20])).
% 7.71/2.66  tff(c_8762, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8739, c_8739, c_8350])).
% 7.71/2.66  tff(c_8322, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_7535])).
% 7.71/2.66  tff(c_54, plain, (![A_23]: (v1_funct_2(A_23, k1_relat_1(A_23), k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.71/2.66  tff(c_5520, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5513, c_54])).
% 7.71/2.66  tff(c_5526, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_5520])).
% 7.71/2.66  tff(c_5517, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5513, c_52])).
% 7.71/2.66  tff(c_5524, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_5517])).
% 7.71/2.66  tff(c_8724, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_5524, c_8713])).
% 7.71/2.66  tff(c_8735, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5526, c_8724])).
% 7.71/2.66  tff(c_9129, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8739, c_8739, c_8735])).
% 7.71/2.66  tff(c_9130, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_8322, c_9129])).
% 7.71/2.66  tff(c_9138, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9130, c_8322])).
% 7.71/2.66  tff(c_9152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8762, c_9138])).
% 7.71/2.66  tff(c_9153, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_8738])).
% 7.71/2.66  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.71/2.66  tff(c_8348, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8321, c_8])).
% 7.71/2.66  tff(c_9175, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9153, c_8348])).
% 7.71/2.66  tff(c_9177, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9153, c_9153, c_8350])).
% 7.71/2.66  tff(c_8438, plain, (![A_422]: (r1_tarski('#skF_2', A_422))), inference(demodulation, [status(thm), theory('equality')], [c_8321, c_8])).
% 7.71/2.66  tff(c_8447, plain, (![A_423]: (A_423='#skF_2' | ~r1_tarski(A_423, '#skF_2'))), inference(resolution, [status(thm)], [c_8438, c_2])).
% 7.71/2.66  tff(c_8534, plain, (![B_427]: (k1_relat_1(B_427)='#skF_2' | ~v4_relat_1(B_427, '#skF_2') | ~v1_relat_1(B_427))), inference(resolution, [status(thm)], [c_14, c_8447])).
% 7.71/2.66  tff(c_8545, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5688, c_8534])).
% 7.71/2.66  tff(c_8554, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_8545])).
% 7.71/2.66  tff(c_58, plain, (![B_25, A_24]: (m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_25), A_24))) | ~r1_tarski(k2_relat_1(B_25), A_24) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.71/2.66  tff(c_8558, plain, (![A_24]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_24))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_24) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8554, c_58])).
% 7.71/2.66  tff(c_8595, plain, (![A_24]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_24))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_5689, c_2706, c_8558])).
% 7.71/2.66  tff(c_9748, plain, (![A_476]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_476))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_476))), inference(demodulation, [status(thm), theory('equality')], [c_9153, c_8595])).
% 7.71/2.66  tff(c_9188, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9153, c_5411])).
% 7.71/2.66  tff(c_9778, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_9748, c_9188])).
% 7.71/2.66  tff(c_9792, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_9778])).
% 7.71/2.66  tff(c_9795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_68, c_9175, c_9177, c_9792])).
% 7.71/2.66  tff(c_9796, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_2705])).
% 7.71/2.66  tff(c_9839, plain, (![A_479, B_480, C_481]: (k1_relset_1(A_479, B_480, C_481)=k1_relat_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_479, B_480))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.71/2.66  tff(c_9847, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_9839])).
% 7.71/2.66  tff(c_10285, plain, (![B_512, A_513, C_514]: (k1_xboole_0=B_512 | k1_relset_1(A_513, B_512, C_514)=A_513 | ~v1_funct_2(C_514, A_513, B_512) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_513, B_512))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.71/2.66  tff(c_10303, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_10285])).
% 7.71/2.66  tff(c_10316, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9847, c_10303])).
% 7.71/2.66  tff(c_10317, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_10316])).
% 7.71/2.66  tff(c_9797, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_2705])).
% 7.71/2.66  tff(c_10, plain, (![B_6, A_4]: (v1_relat_1(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.71/2.66  tff(c_9802, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_9797, c_10])).
% 7.71/2.66  tff(c_9805, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_9802])).
% 7.71/2.66  tff(c_9898, plain, (![A_483, B_484, C_485]: (k2_relset_1(A_483, B_484, C_485)=k2_relat_1(C_485) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(A_483, B_484))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.71/2.66  tff(c_9910, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_9898])).
% 7.71/2.66  tff(c_9916, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9910])).
% 7.71/2.66  tff(c_34, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.71/2.66  tff(c_9846, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9797, c_9839])).
% 7.71/2.66  tff(c_10414, plain, (![B_518, C_519, A_520]: (k1_xboole_0=B_518 | v1_funct_2(C_519, A_520, B_518) | k1_relset_1(A_520, B_518, C_519)!=A_520 | ~m1_subset_1(C_519, k1_zfmisc_1(k2_zfmisc_1(A_520, B_518))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.71/2.66  tff(c_10426, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_9797, c_10414])).
% 7.71/2.66  tff(c_10436, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9846, c_10426])).
% 7.71/2.66  tff(c_10437, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_9796, c_10436])).
% 7.71/2.66  tff(c_10441, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_10437])).
% 7.71/2.66  tff(c_10444, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_10441])).
% 7.71/2.66  tff(c_10447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_68, c_9916, c_10444])).
% 7.71/2.66  tff(c_10449, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_10437])).
% 7.71/2.66  tff(c_10498, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10449, c_54])).
% 7.71/2.66  tff(c_10528, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9805, c_2706, c_10498])).
% 7.71/2.66  tff(c_10733, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_10528])).
% 7.71/2.66  tff(c_10735, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_68, c_10317, c_10733])).
% 7.71/2.66  tff(c_10737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9796, c_10735])).
% 7.71/2.66  tff(c_10739, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_10316])).
% 7.71/2.66  tff(c_10738, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_10316])).
% 7.71/2.66  tff(c_46, plain, (![B_21, C_22, A_20]: (k1_xboole_0=B_21 | v1_funct_2(C_22, A_20, B_21) | k1_relset_1(A_20, B_21, C_22)!=A_20 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.71/2.66  tff(c_10801, plain, (![B_531, C_532, A_533]: (B_531='#skF_2' | v1_funct_2(C_532, A_533, B_531) | k1_relset_1(A_533, B_531, C_532)!=A_533 | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_533, B_531))))), inference(demodulation, [status(thm), theory('equality')], [c_10738, c_46])).
% 7.71/2.66  tff(c_10813, plain, ('#skF_2'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_9797, c_10801])).
% 7.71/2.66  tff(c_10824, plain, ('#skF_2'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9846, c_10813])).
% 7.71/2.66  tff(c_10825, plain, ('#skF_2'='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_9796, c_10824])).
% 7.71/2.66  tff(c_10896, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_10825])).
% 7.71/2.66  tff(c_10901, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_10896])).
% 7.71/2.66  tff(c_10904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_74, c_68, c_9916, c_10901])).
% 7.71/2.66  tff(c_10905, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_10825])).
% 7.71/2.66  tff(c_10930, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10905, c_72])).
% 7.71/2.66  tff(c_10925, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10905, c_9847])).
% 7.71/2.66  tff(c_10928, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10905, c_70])).
% 7.71/2.66  tff(c_48, plain, (![B_21, C_22]: (k1_relset_1(k1_xboole_0, B_21, C_22)=k1_xboole_0 | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.71/2.66  tff(c_10742, plain, (![B_21, C_22]: (k1_relset_1('#skF_2', B_21, C_22)='#skF_2' | ~v1_funct_2(C_22, '#skF_2', B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_21))))), inference(demodulation, [status(thm), theory('equality')], [c_10738, c_10738, c_10738, c_10738, c_48])).
% 7.71/2.66  tff(c_11281, plain, (![B_547, C_548]: (k1_relset_1('#skF_1', B_547, C_548)='#skF_1' | ~v1_funct_2(C_548, '#skF_1', B_547) | ~m1_subset_1(C_548, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_547))))), inference(demodulation, [status(thm), theory('equality')], [c_10905, c_10905, c_10905, c_10905, c_10742])).
% 7.71/2.66  tff(c_11284, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10928, c_11281])).
% 7.71/2.66  tff(c_11290, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10930, c_10925, c_11284])).
% 7.71/2.66  tff(c_11292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10739, c_11290])).
% 7.71/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.66  
% 7.71/2.66  Inference rules
% 7.71/2.66  ----------------------
% 7.71/2.66  #Ref     : 0
% 7.71/2.66  #Sup     : 2239
% 7.71/2.66  #Fact    : 0
% 7.71/2.66  #Define  : 0
% 7.71/2.66  #Split   : 36
% 7.71/2.66  #Chain   : 0
% 7.71/2.66  #Close   : 0
% 7.71/2.66  
% 7.71/2.66  Ordering : KBO
% 7.71/2.66  
% 7.71/2.66  Simplification rules
% 7.71/2.66  ----------------------
% 7.71/2.66  #Subsume      : 347
% 7.71/2.66  #Demod        : 4613
% 7.71/2.66  #Tautology    : 1267
% 7.71/2.66  #SimpNegUnit  : 20
% 7.71/2.66  #BackRed      : 570
% 7.71/2.66  
% 7.71/2.66  #Partial instantiations: 0
% 7.71/2.66  #Strategies tried      : 1
% 7.71/2.66  
% 7.71/2.66  Timing (in seconds)
% 7.71/2.66  ----------------------
% 7.71/2.67  Preprocessing        : 0.34
% 7.71/2.67  Parsing              : 0.18
% 7.71/2.67  CNF conversion       : 0.02
% 7.71/2.67  Main loop            : 1.53
% 7.71/2.67  Inferencing          : 0.50
% 7.71/2.67  Reduction            : 0.59
% 7.71/2.67  Demodulation         : 0.44
% 7.71/2.67  BG Simplification    : 0.06
% 7.71/2.67  Subsumption          : 0.25
% 7.71/2.67  Abstraction          : 0.07
% 7.71/2.67  MUC search           : 0.00
% 7.71/2.67  Cooper               : 0.00
% 7.71/2.67  Total                : 1.93
% 7.71/2.67  Index Insertion      : 0.00
% 7.71/2.67  Index Deletion       : 0.00
% 7.71/2.67  Index Matching       : 0.00
% 7.71/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
