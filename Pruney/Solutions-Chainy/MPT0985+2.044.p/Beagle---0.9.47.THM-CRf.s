%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:32 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  140 (1433 expanded)
%              Number of leaves         :   41 ( 481 expanded)
%              Depth                    :   16
%              Number of atoms          :  222 (4225 expanded)
%              Number of equality atoms :   68 ( 981 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_119,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_89,plain,(
    ! [A_43] :
      ( v1_funct_1(k2_funct_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_79,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_92,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_79])).

tff(c_95,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_92])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_101,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_113,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_107])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_113])).

tff(c_116,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_118,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_134,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_134])).

tff(c_146,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_140])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_217,plain,(
    ! [A_68] :
      ( k4_relat_1(A_68) = k2_funct_1(A_68)
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_220,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_217])).

tff(c_223,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_62,c_220])).

tff(c_238,plain,(
    ! [A_73,B_74,C_75] :
      ( k3_relset_1(A_73,B_74,C_75) = k4_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_244,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_238])).

tff(c_248,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_244])).

tff(c_268,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1(k3_relset_1(A_80,B_81,C_82),k1_zfmisc_1(k2_zfmisc_1(B_81,A_80)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_290,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_268])).

tff(c_303,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_290])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_303])).

tff(c_306,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_323,plain,(
    ! [B_90,A_91] :
      ( v1_relat_1(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91))
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_332,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_323])).

tff(c_341,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_332])).

tff(c_428,plain,(
    ! [A_102] :
      ( k4_relat_1(A_102) = k2_funct_1(A_102)
      | ~ v2_funct_1(A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_431,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_428])).

tff(c_434,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_62,c_431])).

tff(c_965,plain,(
    ! [A_148,B_149,C_150] :
      ( k3_relset_1(A_148,B_149,C_150) = k4_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_974,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_965])).

tff(c_979,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_974])).

tff(c_2089,plain,(
    ! [B_232,A_233,C_234] :
      ( k1_relset_1(B_232,A_233,k3_relset_1(A_233,B_232,C_234)) = k2_relset_1(A_233,B_232,C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_233,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2101,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2089])).

tff(c_2111,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_979,c_2101])).

tff(c_307,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_2181,plain,(
    ! [B_242,C_243,A_244] :
      ( k1_xboole_0 = B_242
      | v1_funct_2(C_243,A_244,B_242)
      | k1_relset_1(A_244,B_242,C_243) != A_244
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2193,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_307,c_2181])).

tff(c_2206,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_2193])).

tff(c_2207,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_2206])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_23,B_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_461,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_partfun1(C_105,A_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_472,plain,(
    ! [A_23] :
      ( v1_partfun1(k1_xboole_0,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_32,c_461])).

tff(c_1268,plain,(
    ! [B_175,A_176,C_177] :
      ( k1_relset_1(B_175,A_176,k3_relset_1(A_176,B_175,C_177)) = k2_relset_1(A_176,B_175,C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1280,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1268])).

tff(c_1290,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_54,c_1280])).

tff(c_1348,plain,(
    ! [B_181,C_182,A_183] :
      ( k1_xboole_0 = B_181
      | v1_funct_2(C_182,A_183,B_181)
      | k1_relset_1(A_183,B_181,C_182) != A_183
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1360,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_307,c_1348])).

tff(c_1374,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_1360])).

tff(c_1375,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_1374])).

tff(c_1002,plain,(
    ! [C_155,A_156,B_157] :
      ( v1_funct_2(C_155,A_156,B_157)
      | ~ v1_partfun1(C_155,A_156)
      | ~ v1_funct_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1016,plain,(
    ! [A_23,B_24] :
      ( v1_funct_2(k1_xboole_0,A_23,B_24)
      | ~ v1_partfun1(k1_xboole_0,A_23)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_1002])).

tff(c_1020,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1016])).

tff(c_1389,plain,(
    ~ v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1375,c_1020])).

tff(c_8,plain,(
    ! [A_6] :
      ( k7_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_8])).

tff(c_1399,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1375,c_1375,c_349])).

tff(c_362,plain,(
    ! [C_92,A_93,B_94] :
      ( v4_relat_1(C_92,A_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_374,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_362])).

tff(c_380,plain,(
    ! [B_96,A_97] :
      ( k7_relat_1(B_96,A_97) = B_96
      | ~ v4_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_386,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_380])).

tff(c_395,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_386])).

tff(c_1412,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_395])).

tff(c_1456,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_62])).

tff(c_1459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1389,c_1456])).

tff(c_1460,plain,(
    ! [A_23,B_24] :
      ( v1_funct_2(k1_xboole_0,A_23,B_24)
      | ~ v1_partfun1(k1_xboole_0,A_23) ) ),
    inference(splitRight,[status(thm)],[c_1016])).

tff(c_1603,plain,(
    ! [B_192,C_193] :
      ( k1_relset_1(k1_xboole_0,B_192,C_193) = k1_xboole_0
      | ~ v1_funct_2(C_193,k1_xboole_0,B_192)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2063,plain,(
    ! [B_231] :
      ( k1_relset_1(k1_xboole_0,B_231,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_231) ) ),
    inference(resolution,[status(thm)],[c_32,c_1603])).

tff(c_2076,plain,(
    ! [B_24] :
      ( k1_relset_1(k1_xboole_0,B_24,k1_xboole_0) = k1_xboole_0
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1460,c_2063])).

tff(c_2079,plain,(
    ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2076])).

tff(c_2082,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_472,c_2079])).

tff(c_2086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2082])).

tff(c_2087,plain,(
    ! [B_24] : k1_relset_1(k1_xboole_0,B_24,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2076])).

tff(c_1463,plain,(
    ! [C_186,B_187] :
      ( v1_funct_2(C_186,k1_xboole_0,B_187)
      | k1_relset_1(k1_xboole_0,B_187,C_186) != k1_xboole_0
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1468,plain,(
    ! [B_24] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_1463])).

tff(c_2114,plain,(
    ! [B_24] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2087,c_1468])).

tff(c_2214,plain,(
    ! [B_24] : v1_funct_2('#skF_1','#skF_1',B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_2207,c_2114])).

tff(c_40,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_64,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_2532,plain,(
    ! [A_264] :
      ( v1_funct_2('#skF_1',A_264,'#skF_1')
      | A_264 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_2207,c_2207,c_64])).

tff(c_12,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2237,plain,(
    k4_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_2207,c_12])).

tff(c_2231,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_2207,c_349])).

tff(c_2244,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2231,c_395])).

tff(c_2272,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_2244,c_434])).

tff(c_2340,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2272])).

tff(c_2280,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_306])).

tff(c_2443,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2340,c_2280])).

tff(c_2536,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2532,c_2443])).

tff(c_2538,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2536,c_2443])).

tff(c_2545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2214,c_2538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.80  
% 4.57/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.57/1.81  
% 4.57/1.81  %Foreground sorts:
% 4.57/1.81  
% 4.57/1.81  
% 4.57/1.81  %Background operators:
% 4.57/1.81  
% 4.57/1.81  
% 4.57/1.81  %Foreground operators:
% 4.57/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.57/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.57/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.57/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.57/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.57/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.57/1.81  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 4.57/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.57/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.57/1.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.57/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.57/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.57/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.57/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.57/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.57/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.57/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.57/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.57/1.81  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.57/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.81  
% 4.75/1.83  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.75/1.83  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.75/1.83  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.75/1.83  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.75/1.83  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 4.75/1.83  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 4.75/1.83  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 4.75/1.83  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relset_1)).
% 4.75/1.83  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.75/1.83  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.75/1.83  tff(f_84, axiom, (![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relset_1)).
% 4.75/1.83  tff(f_101, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 4.75/1.83  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 4.75/1.83  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 4.75/1.83  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.75/1.83  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.75/1.83  tff(f_46, axiom, (k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 4.75/1.83  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.75/1.83  tff(c_89, plain, (![A_43]: (v1_funct_1(k2_funct_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.75/1.83  tff(c_52, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.75/1.83  tff(c_79, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 4.75/1.83  tff(c_92, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_89, c_79])).
% 4.75/1.83  tff(c_95, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_92])).
% 4.75/1.83  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.75/1.83  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.75/1.83  tff(c_101, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.83  tff(c_107, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_101])).
% 4.75/1.83  tff(c_113, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_107])).
% 4.75/1.83  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_113])).
% 4.75/1.83  tff(c_116, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_52])).
% 4.75/1.83  tff(c_118, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_116])).
% 4.75/1.83  tff(c_134, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.83  tff(c_140, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_134])).
% 4.75/1.83  tff(c_146, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_140])).
% 4.75/1.83  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.75/1.83  tff(c_217, plain, (![A_68]: (k4_relat_1(A_68)=k2_funct_1(A_68) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.75/1.83  tff(c_220, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_217])).
% 4.75/1.83  tff(c_223, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_62, c_220])).
% 4.75/1.83  tff(c_238, plain, (![A_73, B_74, C_75]: (k3_relset_1(A_73, B_74, C_75)=k4_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.83  tff(c_244, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_238])).
% 4.75/1.83  tff(c_248, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_244])).
% 4.75/1.83  tff(c_268, plain, (![A_80, B_81, C_82]: (m1_subset_1(k3_relset_1(A_80, B_81, C_82), k1_zfmisc_1(k2_zfmisc_1(B_81, A_80))) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.75/1.83  tff(c_290, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_248, c_268])).
% 4.75/1.83  tff(c_303, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_290])).
% 4.75/1.83  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_303])).
% 4.75/1.83  tff(c_306, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_116])).
% 4.75/1.83  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.75/1.83  tff(c_323, plain, (![B_90, A_91]: (v1_relat_1(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.83  tff(c_332, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_323])).
% 4.75/1.83  tff(c_341, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_332])).
% 4.75/1.83  tff(c_428, plain, (![A_102]: (k4_relat_1(A_102)=k2_funct_1(A_102) | ~v2_funct_1(A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.75/1.83  tff(c_431, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_428])).
% 4.75/1.83  tff(c_434, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_62, c_431])).
% 4.75/1.83  tff(c_965, plain, (![A_148, B_149, C_150]: (k3_relset_1(A_148, B_149, C_150)=k4_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.83  tff(c_974, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_965])).
% 4.75/1.83  tff(c_979, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_974])).
% 4.75/1.83  tff(c_2089, plain, (![B_232, A_233, C_234]: (k1_relset_1(B_232, A_233, k3_relset_1(A_233, B_232, C_234))=k2_relset_1(A_233, B_232, C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_233, B_232))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.75/1.83  tff(c_2101, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_2089])).
% 4.75/1.83  tff(c_2111, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_979, c_2101])).
% 4.75/1.83  tff(c_307, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_116])).
% 4.75/1.83  tff(c_2181, plain, (![B_242, C_243, A_244]: (k1_xboole_0=B_242 | v1_funct_2(C_243, A_244, B_242) | k1_relset_1(A_244, B_242, C_243)!=A_244 | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_242))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.75/1.83  tff(c_2193, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_307, c_2181])).
% 4.75/1.83  tff(c_2206, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2111, c_2193])).
% 4.75/1.83  tff(c_2207, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_306, c_2206])).
% 4.75/1.83  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.75/1.83  tff(c_32, plain, (![A_23, B_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.75/1.83  tff(c_461, plain, (![C_105, A_106, B_107]: (v1_partfun1(C_105, A_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.75/1.83  tff(c_472, plain, (![A_23]: (v1_partfun1(k1_xboole_0, A_23) | ~v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_32, c_461])).
% 4.75/1.83  tff(c_1268, plain, (![B_175, A_176, C_177]: (k1_relset_1(B_175, A_176, k3_relset_1(A_176, B_175, C_177))=k2_relset_1(A_176, B_175, C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.75/1.83  tff(c_1280, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_1268])).
% 4.75/1.83  tff(c_1290, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_979, c_54, c_1280])).
% 4.75/1.83  tff(c_1348, plain, (![B_181, C_182, A_183]: (k1_xboole_0=B_181 | v1_funct_2(C_182, A_183, B_181) | k1_relset_1(A_183, B_181, C_182)!=A_183 | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_181))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.75/1.83  tff(c_1360, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_307, c_1348])).
% 4.75/1.83  tff(c_1374, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_1360])).
% 4.75/1.83  tff(c_1375, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_306, c_1374])).
% 4.75/1.83  tff(c_1002, plain, (![C_155, A_156, B_157]: (v1_funct_2(C_155, A_156, B_157) | ~v1_partfun1(C_155, A_156) | ~v1_funct_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.75/1.83  tff(c_1016, plain, (![A_23, B_24]: (v1_funct_2(k1_xboole_0, A_23, B_24) | ~v1_partfun1(k1_xboole_0, A_23) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_1002])).
% 4.75/1.83  tff(c_1020, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1016])).
% 4.75/1.83  tff(c_1389, plain, (~v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1375, c_1020])).
% 4.75/1.83  tff(c_8, plain, (![A_6]: (k7_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.75/1.83  tff(c_349, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_341, c_8])).
% 4.75/1.83  tff(c_1399, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1375, c_1375, c_349])).
% 4.75/1.83  tff(c_362, plain, (![C_92, A_93, B_94]: (v4_relat_1(C_92, A_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.75/1.83  tff(c_374, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_362])).
% 4.75/1.83  tff(c_380, plain, (![B_96, A_97]: (k7_relat_1(B_96, A_97)=B_96 | ~v4_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.75/1.83  tff(c_386, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_374, c_380])).
% 4.75/1.83  tff(c_395, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_341, c_386])).
% 4.75/1.83  tff(c_1412, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1399, c_395])).
% 4.75/1.83  tff(c_1456, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_62])).
% 4.75/1.83  tff(c_1459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1389, c_1456])).
% 4.75/1.83  tff(c_1460, plain, (![A_23, B_24]: (v1_funct_2(k1_xboole_0, A_23, B_24) | ~v1_partfun1(k1_xboole_0, A_23))), inference(splitRight, [status(thm)], [c_1016])).
% 4.75/1.83  tff(c_1603, plain, (![B_192, C_193]: (k1_relset_1(k1_xboole_0, B_192, C_193)=k1_xboole_0 | ~v1_funct_2(C_193, k1_xboole_0, B_192) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_192))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.75/1.83  tff(c_2063, plain, (![B_231]: (k1_relset_1(k1_xboole_0, B_231, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_231))), inference(resolution, [status(thm)], [c_32, c_1603])).
% 4.75/1.83  tff(c_2076, plain, (![B_24]: (k1_relset_1(k1_xboole_0, B_24, k1_xboole_0)=k1_xboole_0 | ~v1_partfun1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_1460, c_2063])).
% 4.75/1.83  tff(c_2079, plain, (~v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2076])).
% 4.75/1.83  tff(c_2082, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_472, c_2079])).
% 4.75/1.83  tff(c_2086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2082])).
% 4.75/1.83  tff(c_2087, plain, (![B_24]: (k1_relset_1(k1_xboole_0, B_24, k1_xboole_0)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_2076])).
% 4.75/1.83  tff(c_1463, plain, (![C_186, B_187]: (v1_funct_2(C_186, k1_xboole_0, B_187) | k1_relset_1(k1_xboole_0, B_187, C_186)!=k1_xboole_0 | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_187))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.75/1.83  tff(c_1468, plain, (![B_24]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1463])).
% 4.75/1.83  tff(c_2114, plain, (![B_24]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_24))), inference(demodulation, [status(thm), theory('equality')], [c_2087, c_1468])).
% 4.75/1.83  tff(c_2214, plain, (![B_24]: (v1_funct_2('#skF_1', '#skF_1', B_24))), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_2207, c_2114])).
% 4.75/1.83  tff(c_40, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.75/1.83  tff(c_64, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 4.75/1.83  tff(c_2532, plain, (![A_264]: (v1_funct_2('#skF_1', A_264, '#skF_1') | A_264='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_2207, c_2207, c_64])).
% 4.75/1.83  tff(c_12, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.75/1.83  tff(c_2237, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_2207, c_12])).
% 4.75/1.83  tff(c_2231, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_2207, c_349])).
% 4.75/1.83  tff(c_2244, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2231, c_395])).
% 4.75/1.83  tff(c_2272, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_2244, c_434])).
% 4.75/1.83  tff(c_2340, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2272])).
% 4.75/1.83  tff(c_2280, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_306])).
% 4.75/1.83  tff(c_2443, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2340, c_2280])).
% 4.75/1.83  tff(c_2536, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_2532, c_2443])).
% 4.75/1.83  tff(c_2538, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2536, c_2443])).
% 4.75/1.83  tff(c_2545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2214, c_2538])).
% 4.75/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.83  
% 4.75/1.83  Inference rules
% 4.75/1.83  ----------------------
% 4.75/1.83  #Ref     : 0
% 4.75/1.83  #Sup     : 534
% 4.75/1.83  #Fact    : 0
% 4.75/1.83  #Define  : 0
% 4.75/1.83  #Split   : 15
% 4.75/1.83  #Chain   : 0
% 4.75/1.83  #Close   : 0
% 4.75/1.83  
% 4.75/1.83  Ordering : KBO
% 4.75/1.83  
% 4.75/1.83  Simplification rules
% 4.75/1.83  ----------------------
% 4.75/1.83  #Subsume      : 9
% 4.75/1.83  #Demod        : 719
% 4.75/1.83  #Tautology    : 317
% 4.75/1.83  #SimpNegUnit  : 10
% 4.75/1.83  #BackRed      : 255
% 4.75/1.83  
% 4.75/1.83  #Partial instantiations: 0
% 4.75/1.83  #Strategies tried      : 1
% 4.75/1.83  
% 4.75/1.83  Timing (in seconds)
% 4.75/1.83  ----------------------
% 4.75/1.83  Preprocessing        : 0.34
% 4.75/1.83  Parsing              : 0.18
% 4.75/1.83  CNF conversion       : 0.02
% 4.75/1.83  Main loop            : 0.71
% 4.75/1.83  Inferencing          : 0.24
% 4.75/1.83  Reduction            : 0.25
% 4.75/1.83  Demodulation         : 0.18
% 4.75/1.83  BG Simplification    : 0.03
% 4.75/1.83  Subsumption          : 0.11
% 4.75/1.83  Abstraction          : 0.03
% 4.75/1.83  MUC search           : 0.00
% 4.75/1.83  Cooper               : 0.00
% 4.75/1.83  Total                : 1.10
% 4.75/1.83  Index Insertion      : 0.00
% 4.75/1.83  Index Deletion       : 0.00
% 4.75/1.83  Index Matching       : 0.00
% 4.75/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
