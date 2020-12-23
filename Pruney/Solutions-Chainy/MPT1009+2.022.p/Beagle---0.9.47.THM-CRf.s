%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:45 EST 2020

% Result     : Theorem 4.49s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 345 expanded)
%              Number of leaves         :   40 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 759 expanded)
%              Number of equality atoms :   40 ( 176 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_147,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_163,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_147])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1794,plain,(
    ! [B_212,A_213] :
      ( k1_tarski(k1_funct_1(B_212,A_213)) = k2_relat_1(B_212)
      | k1_tarski(A_213) != k1_relat_1(B_212)
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1803,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1794,c_58])).

tff(c_1809,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_66,c_1803])).

tff(c_1849,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1809])).

tff(c_316,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_334,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_316])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_400,plain,(
    ! [B_84,A_85] :
      ( k1_tarski(B_84) = A_85
      | k1_xboole_0 = A_85
      | ~ r1_tarski(A_85,k1_tarski(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2571,plain,(
    ! [B_294,B_295] :
      ( k1_tarski(B_294) = k1_relat_1(B_295)
      | k1_relat_1(B_295) = k1_xboole_0
      | ~ v4_relat_1(B_295,k1_tarski(B_294))
      | ~ v1_relat_1(B_295) ) ),
    inference(resolution,[status(thm)],[c_34,c_400])).

tff(c_2601,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_334,c_2571])).

tff(c_2620,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_2601])).

tff(c_2621,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1849,c_2620])).

tff(c_52,plain,(
    ! [B_33,A_32] :
      ( m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33),A_32)))
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2650,plain,(
    ! [A_32] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_32)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_32)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2621,c_52])).

tff(c_2692,plain,(
    ! [A_32] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_66,c_22,c_2650])).

tff(c_2809,plain,(
    ! [A_300] : ~ r1_tarski(k2_relat_1('#skF_4'),A_300) ),
    inference(splitLeft,[status(thm)],[c_2692])).

tff(c_2819,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_2809])).

tff(c_2820,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_2692])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2845,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2820,c_26])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_24,c_121])).

tff(c_191,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_129,c_191])).

tff(c_2868,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2845,c_199])).

tff(c_2915,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_129])).

tff(c_165,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_147])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_246,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k9_relat_1(B_62,A_63),k2_relat_1(B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_251,plain,(
    ! [A_63] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_63),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_246])).

tff(c_255,plain,(
    ! [A_64] : r1_tarski(k9_relat_1(k1_xboole_0,A_64),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_251])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_260,plain,(
    ! [A_64] :
      ( k9_relat_1(k1_xboole_0,A_64) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_64)) ) ),
    inference(resolution,[status(thm)],[c_255,c_2])).

tff(c_267,plain,(
    ! [A_64] : k9_relat_1(k1_xboole_0,A_64) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_260])).

tff(c_2909,plain,(
    ! [A_64] : k9_relat_1('#skF_4',A_64) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_2868,c_267])).

tff(c_1881,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k7_relset_1(A_229,B_230,C_231,D_232) = k9_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1894,plain,(
    ! [D_232] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_232) = k9_relat_1('#skF_4',D_232) ),
    inference(resolution,[status(thm)],[c_62,c_1881])).

tff(c_1905,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_58])).

tff(c_3069,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2909,c_1905])).

tff(c_3073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2915,c_3069])).

tff(c_3075,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_3081,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_62])).

tff(c_50,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( k7_relset_1(A_28,B_29,C_30,D_31) = k9_relat_1(C_30,D_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3146,plain,(
    ! [D_31] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_31) = k9_relat_1('#skF_4',D_31) ),
    inference(resolution,[status(thm)],[c_3081,c_50])).

tff(c_3074,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_3170,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_3074])).

tff(c_3221,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_3170])).

tff(c_3233,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3221])).

tff(c_3237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_3233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:39:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.81  
% 4.49/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.49/1.81  
% 4.49/1.81  %Foreground sorts:
% 4.49/1.81  
% 4.49/1.81  
% 4.49/1.81  %Background operators:
% 4.49/1.81  
% 4.49/1.81  
% 4.49/1.81  %Foreground operators:
% 4.49/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.49/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.49/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.49/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.49/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.49/1.81  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.49/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.49/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.49/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.49/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.49/1.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.49/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.49/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.49/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.49/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.49/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.49/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.49/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.49/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.49/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.49/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.49/1.81  
% 4.72/1.83  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.72/1.83  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.72/1.83  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.72/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.72/1.83  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.72/1.83  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.72/1.83  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.72/1.83  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.72/1.83  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.72/1.83  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.72/1.83  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.72/1.83  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.72/1.83  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.72/1.83  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.72/1.83  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.72/1.83  tff(c_147, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.72/1.83  tff(c_163, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_147])).
% 4.72/1.83  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.83  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.72/1.83  tff(c_22, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.72/1.83  tff(c_1794, plain, (![B_212, A_213]: (k1_tarski(k1_funct_1(B_212, A_213))=k2_relat_1(B_212) | k1_tarski(A_213)!=k1_relat_1(B_212) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.72/1.83  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.72/1.83  tff(c_1803, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1794, c_58])).
% 4.72/1.83  tff(c_1809, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_66, c_1803])).
% 4.72/1.83  tff(c_1849, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1809])).
% 4.72/1.83  tff(c_316, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.72/1.83  tff(c_334, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_316])).
% 4.72/1.83  tff(c_34, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.72/1.83  tff(c_400, plain, (![B_84, A_85]: (k1_tarski(B_84)=A_85 | k1_xboole_0=A_85 | ~r1_tarski(A_85, k1_tarski(B_84)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.72/1.83  tff(c_2571, plain, (![B_294, B_295]: (k1_tarski(B_294)=k1_relat_1(B_295) | k1_relat_1(B_295)=k1_xboole_0 | ~v4_relat_1(B_295, k1_tarski(B_294)) | ~v1_relat_1(B_295))), inference(resolution, [status(thm)], [c_34, c_400])).
% 4.72/1.83  tff(c_2601, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_334, c_2571])).
% 4.72/1.83  tff(c_2620, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_163, c_2601])).
% 4.72/1.83  tff(c_2621, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1849, c_2620])).
% 4.72/1.83  tff(c_52, plain, (![B_33, A_32]: (m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33), A_32))) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.72/1.83  tff(c_2650, plain, (![A_32]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_32))) | ~r1_tarski(k2_relat_1('#skF_4'), A_32) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2621, c_52])).
% 4.72/1.83  tff(c_2692, plain, (![A_32]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_66, c_22, c_2650])).
% 4.72/1.83  tff(c_2809, plain, (![A_300]: (~r1_tarski(k2_relat_1('#skF_4'), A_300))), inference(splitLeft, [status(thm)], [c_2692])).
% 4.72/1.83  tff(c_2819, plain, $false, inference(resolution, [status(thm)], [c_6, c_2809])).
% 4.72/1.83  tff(c_2820, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_2692])).
% 4.72/1.83  tff(c_26, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.72/1.83  tff(c_2845, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_2820, c_26])).
% 4.72/1.83  tff(c_24, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.72/1.83  tff(c_121, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.72/1.83  tff(c_129, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_24, c_121])).
% 4.72/1.83  tff(c_191, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.83  tff(c_199, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_129, c_191])).
% 4.72/1.83  tff(c_2868, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2845, c_199])).
% 4.72/1.83  tff(c_2915, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2868, c_129])).
% 4.72/1.83  tff(c_165, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_147])).
% 4.72/1.83  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.72/1.83  tff(c_246, plain, (![B_62, A_63]: (r1_tarski(k9_relat_1(B_62, A_63), k2_relat_1(B_62)) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.83  tff(c_251, plain, (![A_63]: (r1_tarski(k9_relat_1(k1_xboole_0, A_63), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_246])).
% 4.72/1.83  tff(c_255, plain, (![A_64]: (r1_tarski(k9_relat_1(k1_xboole_0, A_64), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_251])).
% 4.72/1.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.83  tff(c_260, plain, (![A_64]: (k9_relat_1(k1_xboole_0, A_64)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_64)))), inference(resolution, [status(thm)], [c_255, c_2])).
% 4.72/1.83  tff(c_267, plain, (![A_64]: (k9_relat_1(k1_xboole_0, A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_260])).
% 4.72/1.83  tff(c_2909, plain, (![A_64]: (k9_relat_1('#skF_4', A_64)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2868, c_2868, c_267])).
% 4.72/1.83  tff(c_1881, plain, (![A_229, B_230, C_231, D_232]: (k7_relset_1(A_229, B_230, C_231, D_232)=k9_relat_1(C_231, D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.72/1.83  tff(c_1894, plain, (![D_232]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_232)=k9_relat_1('#skF_4', D_232))), inference(resolution, [status(thm)], [c_62, c_1881])).
% 4.72/1.83  tff(c_1905, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_58])).
% 4.72/1.83  tff(c_3069, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2909, c_1905])).
% 4.72/1.83  tff(c_3073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2915, c_3069])).
% 4.72/1.83  tff(c_3075, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1809])).
% 4.72/1.83  tff(c_3081, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_62])).
% 4.72/1.83  tff(c_50, plain, (![A_28, B_29, C_30, D_31]: (k7_relset_1(A_28, B_29, C_30, D_31)=k9_relat_1(C_30, D_31) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.72/1.83  tff(c_3146, plain, (![D_31]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_31)=k9_relat_1('#skF_4', D_31))), inference(resolution, [status(thm)], [c_3081, c_50])).
% 4.72/1.83  tff(c_3074, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1809])).
% 4.72/1.83  tff(c_3170, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_3074])).
% 4.72/1.83  tff(c_3221, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_3170])).
% 4.72/1.83  tff(c_3233, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3221])).
% 4.72/1.83  tff(c_3237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_3233])).
% 4.72/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.83  
% 4.72/1.83  Inference rules
% 4.72/1.83  ----------------------
% 4.72/1.83  #Ref     : 0
% 4.72/1.83  #Sup     : 656
% 4.72/1.83  #Fact    : 0
% 4.72/1.83  #Define  : 0
% 4.72/1.83  #Split   : 6
% 4.72/1.83  #Chain   : 0
% 4.72/1.83  #Close   : 0
% 4.72/1.83  
% 4.72/1.83  Ordering : KBO
% 4.72/1.83  
% 4.72/1.83  Simplification rules
% 4.72/1.83  ----------------------
% 4.72/1.83  #Subsume      : 71
% 4.72/1.83  #Demod        : 977
% 4.72/1.83  #Tautology    : 374
% 4.72/1.83  #SimpNegUnit  : 2
% 4.72/1.83  #BackRed      : 117
% 4.72/1.83  
% 4.72/1.83  #Partial instantiations: 0
% 4.72/1.83  #Strategies tried      : 1
% 4.72/1.83  
% 4.72/1.83  Timing (in seconds)
% 4.72/1.83  ----------------------
% 4.72/1.83  Preprocessing        : 0.33
% 4.72/1.83  Parsing              : 0.18
% 4.72/1.83  CNF conversion       : 0.02
% 4.72/1.83  Main loop            : 0.72
% 4.72/1.83  Inferencing          : 0.24
% 4.72/1.83  Reduction            : 0.26
% 4.72/1.83  Demodulation         : 0.19
% 4.72/1.83  BG Simplification    : 0.03
% 4.72/1.83  Subsumption          : 0.13
% 4.72/1.83  Abstraction          : 0.04
% 4.72/1.83  MUC search           : 0.00
% 4.72/1.83  Cooper               : 0.00
% 4.72/1.83  Total                : 1.09
% 4.72/1.83  Index Insertion      : 0.00
% 4.72/1.83  Index Deletion       : 0.00
% 4.72/1.83  Index Matching       : 0.00
% 4.72/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
