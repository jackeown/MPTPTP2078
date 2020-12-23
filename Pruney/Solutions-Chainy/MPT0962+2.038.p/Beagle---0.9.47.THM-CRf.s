%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:56 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.70s
% Verified   : 
% Statistics : Number of formulae       :  140 (1191 expanded)
%              Number of leaves         :   27 ( 391 expanded)
%              Depth                    :   13
%              Number of atoms          :  260 (2781 expanded)
%              Number of equality atoms :   67 ( 742 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6576,plain,(
    ! [C_362,A_363,B_364] :
      ( m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364)))
      | ~ r1_tarski(k2_relat_1(C_362),B_364)
      | ~ r1_tarski(k1_relat_1(C_362),A_363)
      | ~ v1_relat_1(C_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46])).

tff(c_79,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_24,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_relat_1(A_11),k1_relat_1(B_13))
      | ~ r1_tarski(A_11,B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_369,plain,(
    ! [C_60,A_61,B_62] :
      ( m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ r1_tarski(k2_relat_1(C_60),B_62)
      | ~ r1_tarski(k1_relat_1(C_60),A_61)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_697,plain,(
    ! [C_105,A_106,B_107] :
      ( r1_tarski(C_105,k2_zfmisc_1(A_106,B_107))
      | ~ r1_tarski(k2_relat_1(C_105),B_107)
      | ~ r1_tarski(k1_relat_1(C_105),A_106)
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_369,c_14])).

tff(c_703,plain,(
    ! [A_106] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_106,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_106)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_697])).

tff(c_718,plain,(
    ! [A_108] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_108,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_703])).

tff(c_726,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1(B_13),'#skF_1'))
      | ~ r1_tarski('#skF_2',B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_718])).

tff(c_737,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1(B_13),'#skF_1'))
      | ~ r1_tarski('#skF_2',B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_726])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_565,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1518,plain,(
    ! [B_129,A_130,A_131] :
      ( k1_xboole_0 = B_129
      | k1_relset_1(A_130,B_129,A_131) = A_130
      | ~ v1_funct_2(A_131,A_130,B_129)
      | ~ r1_tarski(A_131,k2_zfmisc_1(A_130,B_129)) ) ),
    inference(resolution,[status(thm)],[c_16,c_565])).

tff(c_1550,plain,(
    ! [B_13] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1(k1_relat_1(B_13),'#skF_1','#skF_2') = k1_relat_1(B_13)
      | ~ v1_funct_2('#skF_2',k1_relat_1(B_13),'#skF_1')
      | ~ r1_tarski('#skF_2',B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_737,c_1518])).

tff(c_2065,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1550])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [A_28,B_29] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_28,B_29)),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,(
    ! [A_3] : r1_tarski(k1_relat_1(k1_xboole_0),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_98])).

tff(c_106,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_2111,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2065,c_106])).

tff(c_125,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_160,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_2123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_160])).

tff(c_2125,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1550])).

tff(c_738,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_718])).

tff(c_232,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_243,plain,(
    ! [A_45,B_46,A_5] :
      ( k1_relset_1(A_45,B_46,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_16,c_232])).

tff(c_744,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_738,c_243])).

tff(c_503,plain,(
    ! [B_79,C_80,A_81] :
      ( k1_xboole_0 = B_79
      | v1_funct_2(C_80,A_81,B_79)
      | k1_relset_1(A_81,B_79,C_80) != A_81
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2491,plain,(
    ! [B_156,A_157,A_158] :
      ( k1_xboole_0 = B_156
      | v1_funct_2(A_157,A_158,B_156)
      | k1_relset_1(A_158,B_156,A_157) != A_158
      | ~ r1_tarski(A_157,k2_zfmisc_1(A_158,B_156)) ) ),
    inference(resolution,[status(thm)],[c_16,c_503])).

tff(c_2503,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_738,c_2491])).

tff(c_2528,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_2503])).

tff(c_2530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_2125,c_2528])).

tff(c_2531,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_3138,plain,(
    ! [C_221,A_222,B_223] :
      ( m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ r1_tarski(k2_relat_1(C_221),B_223)
      | ~ r1_tarski(k1_relat_1(C_221),A_222)
      | ~ v1_relat_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3234,plain,(
    ! [C_232,A_233,B_234] :
      ( r1_tarski(C_232,k2_zfmisc_1(A_233,B_234))
      | ~ r1_tarski(k2_relat_1(C_232),B_234)
      | ~ r1_tarski(k1_relat_1(C_232),A_233)
      | ~ v1_relat_1(C_232) ) ),
    inference(resolution,[status(thm)],[c_3138,c_14])).

tff(c_3274,plain,(
    ! [C_238,A_239] :
      ( r1_tarski(C_238,k2_zfmisc_1(A_239,k2_relat_1(C_238)))
      | ~ r1_tarski(k1_relat_1(C_238),A_239)
      | ~ v1_relat_1(C_238) ) ),
    inference(resolution,[status(thm)],[c_6,c_3234])).

tff(c_3289,plain,(
    ! [A_239] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_239,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_239)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2531,c_3274])).

tff(c_3324,plain,(
    ! [A_241] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_241,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3289])).

tff(c_3349,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_3324])).

tff(c_2607,plain,(
    ! [A_166,B_167,C_168] :
      ( k1_relset_1(A_166,B_167,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2618,plain,(
    ! [A_166,B_167,A_5] :
      ( k1_relset_1(A_166,B_167,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_166,B_167)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2607])).

tff(c_3383,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3349,c_2618])).

tff(c_3257,plain,(
    ! [B_235,C_236,A_237] :
      ( k1_xboole_0 = B_235
      | v1_funct_2(C_236,A_237,B_235)
      | k1_relset_1(A_237,B_235,C_236) != A_237
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5506,plain,(
    ! [B_291,A_292,A_293] :
      ( k1_xboole_0 = B_291
      | v1_funct_2(A_292,A_293,B_291)
      | k1_relset_1(A_293,B_291,A_292) != A_293
      | ~ r1_tarski(A_292,k2_zfmisc_1(A_293,B_291)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3257])).

tff(c_5524,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3349,c_5506])).

tff(c_5552,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_5524])).

tff(c_5553,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_5552])).

tff(c_3221,plain,(
    ! [C_230,A_231] :
      ( m1_subset_1(C_230,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_230),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_230),A_231)
      | ~ v1_relat_1(C_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3138])).

tff(c_3225,plain,(
    ! [A_231] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_231)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2531,c_3221])).

tff(c_3230,plain,(
    ! [A_231] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3225])).

tff(c_3233,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3230])).

tff(c_5575,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_3233])).

tff(c_5615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5575])).

tff(c_5617,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3230])).

tff(c_134,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_106,c_125])).

tff(c_5637,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5617,c_134])).

tff(c_70,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2660,plain,(
    ! [A_171,B_172] :
      ( r1_tarski(k2_relat_1(A_171),k2_relat_1(B_172))
      | ~ r1_tarski(A_171,B_172)
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2674,plain,(
    ! [A_171] :
      ( r1_tarski(k2_relat_1(A_171),k1_xboole_0)
      | ~ r1_tarski(A_171,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2660])).

tff(c_2684,plain,(
    ! [A_173] :
      ( r1_tarski(k2_relat_1(A_173),k1_xboole_0)
      | ~ r1_tarski(A_173,k1_xboole_0)
      | ~ v1_relat_1(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2674])).

tff(c_2695,plain,
    ( r1_tarski('#skF_1',k1_xboole_0)
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2531,c_2684])).

tff(c_2705,plain,
    ( r1_tarski('#skF_1',k1_xboole_0)
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2695])).

tff(c_2708,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2705])).

tff(c_5665,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5637,c_2708])).

tff(c_5616,plain,(
    ! [A_231] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_231)
      | m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_3230])).

tff(c_5684,plain,(
    ! [A_231] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_231)
      | m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5637,c_5616])).

tff(c_5782,plain,(
    ! [A_298] : ~ r1_tarski(k1_relat_1('#skF_2'),A_298) ),
    inference(splitLeft,[status(thm)],[c_5684])).

tff(c_5794,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_5782])).

tff(c_5795,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5684])).

tff(c_5873,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_5795,c_14])).

tff(c_5877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5665,c_5873])).

tff(c_5878,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2705])).

tff(c_5896,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5878,c_134])).

tff(c_5914,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5896,c_28])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_34])).

tff(c_2540,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_2557,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_2540])).

tff(c_2561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2557])).

tff(c_2563,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_5906,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5896,c_2563])).

tff(c_2617,plain,(
    ! [A_3,C_168] :
      ( k1_relset_1(A_3,k1_xboole_0,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2607])).

tff(c_6263,plain,(
    ! [A_326,C_327] :
      ( k1_relset_1(A_326,'#skF_1',C_327) = k1_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5896,c_2617])).

tff(c_6265,plain,(
    ! [A_326] : k1_relset_1(A_326,'#skF_1','#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5906,c_6263])).

tff(c_6270,plain,(
    ! [A_326] : k1_relset_1(A_326,'#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5914,c_6265])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_6090,plain,(
    ! [C_310,B_311] :
      ( v1_funct_2(C_310,'#skF_1',B_311)
      | k1_relset_1('#skF_1',B_311,C_310) != '#skF_1'
      | ~ m1_subset_1(C_310,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5896,c_5896,c_5896,c_56])).

tff(c_6234,plain,(
    ! [B_322] :
      ( v1_funct_2('#skF_1','#skF_1',B_322)
      | k1_relset_1('#skF_1',B_322,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_5906,c_6090])).

tff(c_5879,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2705])).

tff(c_5930,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5879])).

tff(c_6048,plain,(
    ! [A_309] :
      ( A_309 = '#skF_1'
      | ~ r1_tarski(A_309,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5896,c_134])).

tff(c_6070,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5930,c_6048])).

tff(c_6078,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6070,c_6070,c_79])).

tff(c_6083,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5914,c_6078])).

tff(c_6240,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_6234,c_6083])).

tff(c_6274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6270,c_6240])).

tff(c_6275,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6582,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6576,c_6275])).

tff(c_6596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_48,c_6582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.33  
% 6.43/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.33  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.43/2.33  
% 6.43/2.33  %Foreground sorts:
% 6.43/2.33  
% 6.43/2.33  
% 6.43/2.33  %Background operators:
% 6.43/2.33  
% 6.43/2.33  
% 6.43/2.33  %Foreground operators:
% 6.43/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.43/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.43/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.43/2.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.43/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.43/2.33  tff('#skF_1', type, '#skF_1': $i).
% 6.43/2.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.43/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.43/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.43/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.43/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.43/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.43/2.33  
% 6.70/2.36  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.70/2.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.70/2.36  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 6.70/2.36  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.70/2.36  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.70/2.36  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.70/2.36  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.70/2.36  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.70/2.36  tff(f_45, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 6.70/2.36  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.70/2.36  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.70/2.36  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.70/2.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.70/2.36  tff(c_48, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.70/2.36  tff(c_6576, plain, (![C_362, A_363, B_364]: (m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))) | ~r1_tarski(k2_relat_1(C_362), B_364) | ~r1_tarski(k1_relat_1(C_362), A_363) | ~v1_relat_1(C_362))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.70/2.36  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.70/2.36  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.70/2.36  tff(c_54, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46])).
% 6.70/2.36  tff(c_79, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 6.70/2.36  tff(c_24, plain, (![A_11, B_13]: (r1_tarski(k1_relat_1(A_11), k1_relat_1(B_13)) | ~r1_tarski(A_11, B_13) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.70/2.36  tff(c_369, plain, (![C_60, A_61, B_62]: (m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~r1_tarski(k2_relat_1(C_60), B_62) | ~r1_tarski(k1_relat_1(C_60), A_61) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.70/2.36  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.70/2.36  tff(c_697, plain, (![C_105, A_106, B_107]: (r1_tarski(C_105, k2_zfmisc_1(A_106, B_107)) | ~r1_tarski(k2_relat_1(C_105), B_107) | ~r1_tarski(k1_relat_1(C_105), A_106) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_369, c_14])).
% 6.70/2.36  tff(c_703, plain, (![A_106]: (r1_tarski('#skF_2', k2_zfmisc_1(A_106, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_106) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_697])).
% 6.70/2.36  tff(c_718, plain, (![A_108]: (r1_tarski('#skF_2', k2_zfmisc_1(A_108, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_108))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_703])).
% 6.70/2.36  tff(c_726, plain, (![B_13]: (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1(B_13), '#skF_1')) | ~r1_tarski('#skF_2', B_13) | ~v1_relat_1(B_13) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_718])).
% 6.70/2.36  tff(c_737, plain, (![B_13]: (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1(B_13), '#skF_1')) | ~r1_tarski('#skF_2', B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_726])).
% 6.70/2.36  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.70/2.36  tff(c_565, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.70/2.36  tff(c_1518, plain, (![B_129, A_130, A_131]: (k1_xboole_0=B_129 | k1_relset_1(A_130, B_129, A_131)=A_130 | ~v1_funct_2(A_131, A_130, B_129) | ~r1_tarski(A_131, k2_zfmisc_1(A_130, B_129)))), inference(resolution, [status(thm)], [c_16, c_565])).
% 6.70/2.36  tff(c_1550, plain, (![B_13]: (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1(B_13), '#skF_1', '#skF_2')=k1_relat_1(B_13) | ~v1_funct_2('#skF_2', k1_relat_1(B_13), '#skF_1') | ~r1_tarski('#skF_2', B_13) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_737, c_1518])).
% 6.70/2.36  tff(c_2065, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1550])).
% 6.70/2.36  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.70/2.36  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.70/2.36  tff(c_98, plain, (![A_28, B_29]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_28, B_29)), A_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.70/2.36  tff(c_104, plain, (![A_3]: (r1_tarski(k1_relat_1(k1_xboole_0), A_3))), inference(superposition, [status(thm), theory('equality')], [c_10, c_98])).
% 6.70/2.36  tff(c_106, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_104])).
% 6.70/2.36  tff(c_2111, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2065, c_106])).
% 6.70/2.36  tff(c_125, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.70/2.36  tff(c_136, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_125])).
% 6.70/2.36  tff(c_160, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_136])).
% 6.70/2.36  tff(c_2123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2111, c_160])).
% 6.70/2.36  tff(c_2125, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1550])).
% 6.70/2.36  tff(c_738, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_718])).
% 6.70/2.36  tff(c_232, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.70/2.36  tff(c_243, plain, (![A_45, B_46, A_5]: (k1_relset_1(A_45, B_46, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_45, B_46)))), inference(resolution, [status(thm)], [c_16, c_232])).
% 6.70/2.36  tff(c_744, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_738, c_243])).
% 6.70/2.36  tff(c_503, plain, (![B_79, C_80, A_81]: (k1_xboole_0=B_79 | v1_funct_2(C_80, A_81, B_79) | k1_relset_1(A_81, B_79, C_80)!=A_81 | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_79))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.70/2.36  tff(c_2491, plain, (![B_156, A_157, A_158]: (k1_xboole_0=B_156 | v1_funct_2(A_157, A_158, B_156) | k1_relset_1(A_158, B_156, A_157)!=A_158 | ~r1_tarski(A_157, k2_zfmisc_1(A_158, B_156)))), inference(resolution, [status(thm)], [c_16, c_503])).
% 6.70/2.36  tff(c_2503, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_738, c_2491])).
% 6.70/2.36  tff(c_2528, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_744, c_2503])).
% 6.70/2.36  tff(c_2530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_2125, c_2528])).
% 6.70/2.36  tff(c_2531, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_136])).
% 6.70/2.36  tff(c_3138, plain, (![C_221, A_222, B_223]: (m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~r1_tarski(k2_relat_1(C_221), B_223) | ~r1_tarski(k1_relat_1(C_221), A_222) | ~v1_relat_1(C_221))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.70/2.36  tff(c_3234, plain, (![C_232, A_233, B_234]: (r1_tarski(C_232, k2_zfmisc_1(A_233, B_234)) | ~r1_tarski(k2_relat_1(C_232), B_234) | ~r1_tarski(k1_relat_1(C_232), A_233) | ~v1_relat_1(C_232))), inference(resolution, [status(thm)], [c_3138, c_14])).
% 6.70/2.36  tff(c_3274, plain, (![C_238, A_239]: (r1_tarski(C_238, k2_zfmisc_1(A_239, k2_relat_1(C_238))) | ~r1_tarski(k1_relat_1(C_238), A_239) | ~v1_relat_1(C_238))), inference(resolution, [status(thm)], [c_6, c_3234])).
% 6.70/2.36  tff(c_3289, plain, (![A_239]: (r1_tarski('#skF_2', k2_zfmisc_1(A_239, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_239) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2531, c_3274])).
% 6.70/2.36  tff(c_3324, plain, (![A_241]: (r1_tarski('#skF_2', k2_zfmisc_1(A_241, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_241))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3289])).
% 6.70/2.36  tff(c_3349, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_3324])).
% 6.70/2.36  tff(c_2607, plain, (![A_166, B_167, C_168]: (k1_relset_1(A_166, B_167, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.70/2.36  tff(c_2618, plain, (![A_166, B_167, A_5]: (k1_relset_1(A_166, B_167, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_166, B_167)))), inference(resolution, [status(thm)], [c_16, c_2607])).
% 6.70/2.36  tff(c_3383, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3349, c_2618])).
% 6.70/2.36  tff(c_3257, plain, (![B_235, C_236, A_237]: (k1_xboole_0=B_235 | v1_funct_2(C_236, A_237, B_235) | k1_relset_1(A_237, B_235, C_236)!=A_237 | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_235))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.70/2.36  tff(c_5506, plain, (![B_291, A_292, A_293]: (k1_xboole_0=B_291 | v1_funct_2(A_292, A_293, B_291) | k1_relset_1(A_293, B_291, A_292)!=A_293 | ~r1_tarski(A_292, k2_zfmisc_1(A_293, B_291)))), inference(resolution, [status(thm)], [c_16, c_3257])).
% 6.70/2.36  tff(c_5524, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3349, c_5506])).
% 6.70/2.36  tff(c_5552, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_5524])).
% 6.70/2.36  tff(c_5553, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_5552])).
% 6.70/2.36  tff(c_3221, plain, (![C_230, A_231]: (m1_subset_1(C_230, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_230), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_230), A_231) | ~v1_relat_1(C_230))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3138])).
% 6.70/2.36  tff(c_3225, plain, (![A_231]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_231) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2531, c_3221])).
% 6.70/2.36  tff(c_3230, plain, (![A_231]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_231))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3225])).
% 6.70/2.36  tff(c_3233, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3230])).
% 6.70/2.36  tff(c_5575, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_3233])).
% 6.70/2.36  tff(c_5615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5575])).
% 6.70/2.36  tff(c_5617, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3230])).
% 6.70/2.36  tff(c_134, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_106, c_125])).
% 6.70/2.36  tff(c_5637, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_5617, c_134])).
% 6.70/2.36  tff(c_70, plain, (![A_26]: (k2_zfmisc_1(A_26, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.70/2.36  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.70/2.36  tff(c_74, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_18])).
% 6.70/2.36  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.70/2.36  tff(c_2660, plain, (![A_171, B_172]: (r1_tarski(k2_relat_1(A_171), k2_relat_1(B_172)) | ~r1_tarski(A_171, B_172) | ~v1_relat_1(B_172) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.70/2.36  tff(c_2674, plain, (![A_171]: (r1_tarski(k2_relat_1(A_171), k1_xboole_0) | ~r1_tarski(A_171, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_171))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2660])).
% 6.70/2.36  tff(c_2684, plain, (![A_173]: (r1_tarski(k2_relat_1(A_173), k1_xboole_0) | ~r1_tarski(A_173, k1_xboole_0) | ~v1_relat_1(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2674])).
% 6.70/2.36  tff(c_2695, plain, (r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2531, c_2684])).
% 6.70/2.36  tff(c_2705, plain, (r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2695])).
% 6.70/2.36  tff(c_2708, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2705])).
% 6.70/2.36  tff(c_5665, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5637, c_2708])).
% 6.70/2.36  tff(c_5616, plain, (![A_231]: (~r1_tarski(k1_relat_1('#skF_2'), A_231) | m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_3230])).
% 6.70/2.36  tff(c_5684, plain, (![A_231]: (~r1_tarski(k1_relat_1('#skF_2'), A_231) | m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5637, c_5616])).
% 6.70/2.36  tff(c_5782, plain, (![A_298]: (~r1_tarski(k1_relat_1('#skF_2'), A_298))), inference(splitLeft, [status(thm)], [c_5684])).
% 6.70/2.36  tff(c_5794, plain, $false, inference(resolution, [status(thm)], [c_6, c_5782])).
% 6.70/2.36  tff(c_5795, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_5684])).
% 6.70/2.36  tff(c_5873, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_5795, c_14])).
% 6.70/2.36  tff(c_5877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5665, c_5873])).
% 6.70/2.36  tff(c_5878, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2705])).
% 6.70/2.36  tff(c_5896, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_5878, c_134])).
% 6.70/2.36  tff(c_5914, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5896, c_28])).
% 6.70/2.36  tff(c_34, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.70/2.36  tff(c_57, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_34])).
% 6.70/2.36  tff(c_2540, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_57])).
% 6.70/2.36  tff(c_2557, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_2540])).
% 6.70/2.36  tff(c_2561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_2557])).
% 6.70/2.36  tff(c_2563, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_57])).
% 6.70/2.36  tff(c_5906, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5896, c_2563])).
% 6.70/2.36  tff(c_2617, plain, (![A_3, C_168]: (k1_relset_1(A_3, k1_xboole_0, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2607])).
% 6.70/2.36  tff(c_6263, plain, (![A_326, C_327]: (k1_relset_1(A_326, '#skF_1', C_327)=k1_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5896, c_2617])).
% 6.70/2.36  tff(c_6265, plain, (![A_326]: (k1_relset_1(A_326, '#skF_1', '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_5906, c_6263])).
% 6.70/2.36  tff(c_6270, plain, (![A_326]: (k1_relset_1(A_326, '#skF_1', '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5914, c_6265])).
% 6.70/2.36  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.70/2.36  tff(c_38, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.70/2.36  tff(c_56, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 6.70/2.36  tff(c_6090, plain, (![C_310, B_311]: (v1_funct_2(C_310, '#skF_1', B_311) | k1_relset_1('#skF_1', B_311, C_310)!='#skF_1' | ~m1_subset_1(C_310, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5896, c_5896, c_5896, c_56])).
% 6.70/2.36  tff(c_6234, plain, (![B_322]: (v1_funct_2('#skF_1', '#skF_1', B_322) | k1_relset_1('#skF_1', B_322, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_5906, c_6090])).
% 6.70/2.36  tff(c_5879, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2705])).
% 6.70/2.36  tff(c_5930, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5879])).
% 6.70/2.36  tff(c_6048, plain, (![A_309]: (A_309='#skF_1' | ~r1_tarski(A_309, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5896, c_134])).
% 6.70/2.36  tff(c_6070, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_5930, c_6048])).
% 6.70/2.36  tff(c_6078, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6070, c_6070, c_79])).
% 6.70/2.36  tff(c_6083, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5914, c_6078])).
% 6.70/2.36  tff(c_6240, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_6234, c_6083])).
% 6.70/2.36  tff(c_6274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6270, c_6240])).
% 6.70/2.36  tff(c_6275, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 6.70/2.36  tff(c_6582, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6576, c_6275])).
% 6.70/2.36  tff(c_6596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_48, c_6582])).
% 6.70/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.36  
% 6.70/2.36  Inference rules
% 6.70/2.36  ----------------------
% 6.70/2.36  #Ref     : 0
% 6.70/2.36  #Sup     : 1309
% 6.70/2.36  #Fact    : 0
% 6.70/2.36  #Define  : 0
% 6.70/2.36  #Split   : 15
% 6.70/2.36  #Chain   : 0
% 6.70/2.36  #Close   : 0
% 6.70/2.36  
% 6.70/2.36  Ordering : KBO
% 6.70/2.36  
% 6.70/2.36  Simplification rules
% 6.70/2.36  ----------------------
% 6.70/2.36  #Subsume      : 235
% 6.70/2.36  #Demod        : 2139
% 6.70/2.36  #Tautology    : 547
% 6.70/2.36  #SimpNegUnit  : 30
% 6.70/2.36  #BackRed      : 167
% 6.70/2.36  
% 6.70/2.36  #Partial instantiations: 0
% 6.70/2.36  #Strategies tried      : 1
% 6.70/2.36  
% 6.70/2.36  Timing (in seconds)
% 6.70/2.36  ----------------------
% 6.70/2.36  Preprocessing        : 0.32
% 6.70/2.36  Parsing              : 0.17
% 6.70/2.36  CNF conversion       : 0.02
% 6.70/2.36  Main loop            : 1.25
% 6.70/2.36  Inferencing          : 0.39
% 6.70/2.36  Reduction            : 0.46
% 6.70/2.36  Demodulation         : 0.35
% 6.70/2.36  BG Simplification    : 0.05
% 6.70/2.36  Subsumption          : 0.25
% 6.70/2.36  Abstraction          : 0.07
% 6.70/2.36  MUC search           : 0.00
% 6.70/2.36  Cooper               : 0.00
% 6.70/2.36  Total                : 1.63
% 6.70/2.36  Index Insertion      : 0.00
% 6.70/2.36  Index Deletion       : 0.00
% 6.70/2.36  Index Matching       : 0.00
% 6.70/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
