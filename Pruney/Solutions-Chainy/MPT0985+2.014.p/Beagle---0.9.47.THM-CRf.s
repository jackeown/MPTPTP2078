%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:27 EST 2020

% Result     : Theorem 8.61s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :  252 (1941 expanded)
%              Number of leaves         :   50 ( 620 expanded)
%              Depth                    :   15
%              Number of atoms          :  427 (5050 expanded)
%              Number of equality atoms :  128 (1614 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_193,negated_conjecture,(
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

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_164,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_154,axiom,(
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

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_176,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_104,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_285,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_297,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_104,c_285])).

tff(c_108,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_102,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_100,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_5925,plain,(
    ! [A_297,B_298,C_299] :
      ( k2_relset_1(A_297,B_298,C_299) = k2_relat_1(C_299)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5934,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_104,c_5925])).

tff(c_5948,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5934])).

tff(c_58,plain,(
    ! [A_37] :
      ( k1_relat_1(k2_funct_1(A_37)) = k2_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_320,plain,(
    ! [A_87] :
      ( k4_relat_1(A_87) = k2_funct_1(A_87)
      | ~ v2_funct_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_326,plain,
    ( k4_relat_1('#skF_7') = k2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_320])).

tff(c_330,plain,(
    k4_relat_1('#skF_7') = k2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_326])).

tff(c_36,plain,(
    ! [A_32] :
      ( v1_xboole_0(k4_relat_1(A_32))
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_340,plain,
    ( v1_xboole_0(k2_funct_1('#skF_7'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_36])).

tff(c_348,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1267,plain,(
    ! [A_156,B_157] :
      ( r2_hidden(k4_tarski('#skF_2'(A_156,B_157),'#skF_1'(A_156,B_157)),A_156)
      | r2_hidden('#skF_3'(A_156,B_157),B_157)
      | k2_relat_1(A_156) = B_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_309,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ v1_xboole_0(C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_315,plain,(
    ! [A_5,A_82] :
      ( ~ v1_xboole_0(A_5)
      | ~ r2_hidden(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_309])).

tff(c_316,plain,(
    ! [A_82] : ~ r2_hidden(A_82,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_1274,plain,(
    ! [B_157] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_157),B_157)
      | k2_relat_1(k1_xboole_0) = B_157 ) ),
    inference(resolution,[status(thm)],[c_1267,c_316])).

tff(c_1277,plain,(
    ! [B_157] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_157),B_157)
      | k1_xboole_0 = B_157 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1274])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_36] :
      ( v1_funct_1(k2_funct_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_98,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5')))
    | ~ v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5')
    | ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_260,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_263,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_260])).

tff(c_266,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_263])).

tff(c_267,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_270,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_104,c_267])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_270])).

tff(c_283,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5')
    | ~ m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_308,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_481,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_484,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_104,c_481])).

tff(c_496,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_484])).

tff(c_54,plain,(
    ! [A_36] :
      ( v1_relat_1(k2_funct_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_284,plain,(
    v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_380,plain,(
    ! [A_94] :
      ( k1_relat_1(k2_funct_1(A_94)) = k2_relat_1(A_94)
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_88,plain,(
    ! [A_51] :
      ( v1_funct_2(A_51,k1_relat_1(A_51),k2_relat_1(A_51))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_4249,plain,(
    ! [A_238] :
      ( v1_funct_2(k2_funct_1(A_238),k2_relat_1(A_238),k2_relat_1(k2_funct_1(A_238)))
      | ~ v1_funct_1(k2_funct_1(A_238))
      | ~ v1_relat_1(k2_funct_1(A_238))
      | ~ v2_funct_1(A_238)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_88])).

tff(c_4297,plain,
    ( v1_funct_2(k2_funct_1('#skF_7'),'#skF_6',k2_relat_1(k2_funct_1('#skF_7')))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_4249])).

tff(c_4320,plain,
    ( v1_funct_2(k2_funct_1('#skF_7'),'#skF_6',k2_relat_1(k2_funct_1('#skF_7')))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_102,c_284,c_4297])).

tff(c_4327,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4320])).

tff(c_4330,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_4327])).

tff(c_4334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_4330])).

tff(c_4336,plain,(
    v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4320])).

tff(c_106,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_428,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_442,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_104,c_428])).

tff(c_1300,plain,(
    ! [B_160,A_161,C_162] :
      ( k1_xboole_0 = B_160
      | k1_relset_1(A_161,B_160,C_162) = A_161
      | ~ v1_funct_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1312,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_1300])).

tff(c_1330,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_442,c_1312])).

tff(c_1334,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1330])).

tff(c_56,plain,(
    ! [A_37] :
      ( k2_relat_1(k2_funct_1(A_37)) = k1_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_527,plain,(
    ! [A_116] :
      ( m1_subset_1(A_116,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_116),k2_relat_1(A_116))))
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5094,plain,(
    ! [A_250] :
      ( m1_subset_1(k2_funct_1(A_250),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_250)),k1_relat_1(A_250))))
      | ~ v1_funct_1(k2_funct_1(A_250))
      | ~ v1_relat_1(k2_funct_1(A_250))
      | ~ v2_funct_1(A_250)
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_527])).

tff(c_5140,plain,
    ( m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_7')),'#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_5094])).

tff(c_5184,plain,(
    m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_7')),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_102,c_4336,c_284,c_5140])).

tff(c_5216,plain,
    ( m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_7'),'#skF_5')))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_5184])).

tff(c_5229,plain,(
    m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_102,c_496,c_5216])).

tff(c_5231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_5229])).

tff(c_5232,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1330])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5269,plain,(
    ! [A_2] : r1_tarski('#skF_6',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5232,c_6])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_888,plain,(
    ! [B_139,A_140] :
      ( m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_139),A_140)))
      | ~ r1_tarski(k2_relat_1(B_139),A_140)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1285,plain,(
    ! [B_159] :
      ( m1_subset_1(B_159,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_159),k1_xboole_0)
      | ~ v1_funct_1(B_159)
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_888])).

tff(c_1288,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_6',k1_xboole_0)
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_1285])).

tff(c_1296,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_1288])).

tff(c_1299,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_5235,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5232,c_1299])).

tff(c_5384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5269,c_5235])).

tff(c_5385,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_18,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5400,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_9,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5385,c_18])).

tff(c_5418,plain,(
    ! [A_255] : ~ r2_hidden(A_255,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5400])).

tff(c_5435,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1277,c_5418])).

tff(c_5477,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5435,c_2])).

tff(c_5483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_5477])).

tff(c_5485,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_5503,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5485,c_4])).

tff(c_5524,plain,(
    ! [A_5] : m1_subset_1('#skF_7',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5503,c_14])).

tff(c_170,plain,(
    ! [A_63] :
      ( v1_xboole_0(k4_relat_1(A_63))
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_182,plain,(
    ! [A_63] :
      ( k4_relat_1(A_63) = k1_xboole_0
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_5498,plain,(
    k4_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5485,c_182])).

tff(c_5552,plain,(
    k4_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5503,c_5498])).

tff(c_5553,plain,(
    k2_funct_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5552,c_330])).

tff(c_5576,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_308])).

tff(c_5694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5524,c_5576])).

tff(c_5695,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_5698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5695,c_2])).

tff(c_5699,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_5700,plain,(
    m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_5873,plain,(
    ! [A_288,B_289,C_290] :
      ( k1_relset_1(A_288,B_289,C_290) = k1_relat_1(C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5894,plain,(
    k1_relset_1('#skF_6','#skF_5',k2_funct_1('#skF_7')) = k1_relat_1(k2_funct_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_5700,c_5873])).

tff(c_7748,plain,(
    ! [B_368,C_369,A_370] :
      ( k1_xboole_0 = B_368
      | v1_funct_2(C_369,A_370,B_368)
      | k1_relset_1(A_370,B_368,C_369) != A_370
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_370,B_368))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_7757,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5')
    | k1_relset_1('#skF_6','#skF_5',k2_funct_1('#skF_7')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_5700,c_7748])).

tff(c_7774,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_5')
    | k1_relat_1(k2_funct_1('#skF_7')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5894,c_7757])).

tff(c_7775,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_7')) != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_5699,c_7774])).

tff(c_7782,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7775])).

tff(c_7785,plain,
    ( k2_relat_1('#skF_7') != '#skF_6'
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_7782])).

tff(c_7788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_102,c_5948,c_7785])).

tff(c_7789,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7775])).

tff(c_7830,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7789,c_2])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7823,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_5',B_4) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7789,c_7789,c_12])).

tff(c_5705,plain,(
    ! [C_268,B_269,A_270] :
      ( ~ v1_xboole_0(C_268)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(C_268))
      | ~ r2_hidden(A_270,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5713,plain,(
    ! [A_270] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_270,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_104,c_5705])).

tff(c_5718,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5713])).

tff(c_8100,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7823,c_5718])).

tff(c_8104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7830,c_8100])).

tff(c_8106,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5713])).

tff(c_8123,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8106,c_4])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8139,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_8123,c_8])).

tff(c_8151,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_8139])).

tff(c_8127,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8123,c_104])).

tff(c_8152,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_8127])).

tff(c_8162,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_5',B_4) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_8151,c_12])).

tff(c_8508,plain,(
    ! [A_403,B_404,C_405] :
      ( k2_relset_1(A_403,B_404,C_405) = k2_relat_1(C_405)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_403,B_404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8582,plain,(
    ! [B_417,C_418] :
      ( k2_relset_1('#skF_5',B_417,C_418) = k2_relat_1(C_418)
      | ~ m1_subset_1(C_418,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8162,c_8508])).

tff(c_8594,plain,(
    ! [B_419] : k2_relset_1('#skF_5',B_419,'#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_8152,c_8582])).

tff(c_8601,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_8594,c_100])).

tff(c_8161,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_8151,c_10])).

tff(c_8287,plain,(
    m1_subset_1(k2_funct_1('#skF_7'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_5700])).

tff(c_8551,plain,(
    ! [A_411,B_412,C_413] :
      ( k1_relset_1(A_411,B_412,C_413) = k1_relat_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_9084,plain,(
    ! [B_457,C_458] :
      ( k1_relset_1('#skF_5',B_457,C_458) = k1_relat_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8162,c_8551])).

tff(c_9092,plain,(
    ! [B_457] : k1_relset_1('#skF_5',B_457,k2_funct_1('#skF_7')) = k1_relat_1(k2_funct_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_8287,c_9084])).

tff(c_78,plain,(
    ! [C_50,B_49] :
      ( v1_funct_2(C_50,k1_xboole_0,B_49)
      | k1_relset_1(k1_xboole_0,B_49,C_50) != k1_xboole_0
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_112,plain,(
    ! [C_50,B_49] :
      ( v1_funct_2(C_50,k1_xboole_0,B_49)
      | k1_relset_1(k1_xboole_0,B_49,C_50) != k1_xboole_0
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_78])).

tff(c_8654,plain,(
    ! [C_422,B_423] :
      ( v1_funct_2(C_422,'#skF_5',B_423)
      | k1_relset_1('#skF_5',B_423,C_422) != '#skF_5'
      | ~ m1_subset_1(C_422,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_8151,c_8151,c_8151,c_112])).

tff(c_8662,plain,(
    ! [B_423] :
      ( v1_funct_2(k2_funct_1('#skF_7'),'#skF_5',B_423)
      | k1_relset_1('#skF_5',B_423,k2_funct_1('#skF_7')) != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_8287,c_8654])).

tff(c_9210,plain,(
    ! [B_423] :
      ( v1_funct_2(k2_funct_1('#skF_7'),'#skF_5',B_423)
      | k1_relat_1(k2_funct_1('#skF_7')) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9092,c_8662])).

tff(c_9226,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9210])).

tff(c_9229,plain,
    ( k2_relat_1('#skF_7') != '#skF_5'
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_9226])).

tff(c_9231,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_102,c_8601,c_9229])).

tff(c_8165,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_8151,c_38])).

tff(c_9978,plain,(
    ! [A_502,B_503] :
      ( r2_hidden(k4_tarski('#skF_2'(A_502,B_503),'#skF_1'(A_502,B_503)),A_502)
      | r2_hidden('#skF_3'(A_502,B_503),B_503)
      | k2_relat_1(A_502) = B_503 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5714,plain,(
    ! [A_5,A_270] :
      ( ~ v1_xboole_0(A_5)
      | ~ r2_hidden(A_270,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_5705])).

tff(c_5716,plain,(
    ! [A_270] : ~ r2_hidden(A_270,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5714])).

tff(c_8154,plain,(
    ! [A_270] : ~ r2_hidden(A_270,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_5716])).

tff(c_10074,plain,(
    ! [B_503] :
      ( r2_hidden('#skF_3'('#skF_5',B_503),B_503)
      | k2_relat_1('#skF_5') = B_503 ) ),
    inference(resolution,[status(thm)],[c_9978,c_8154])).

tff(c_10110,plain,(
    ! [B_504] :
      ( r2_hidden('#skF_3'('#skF_5',B_504),B_504)
      | B_504 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8165,c_10074])).

tff(c_8753,plain,(
    ! [A_431,C_432] :
      ( r2_hidden(k4_tarski('#skF_4'(A_431,k2_relat_1(A_431),C_432),C_432),A_431)
      | ~ r2_hidden(C_432,k2_relat_1(A_431)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8105,plain,(
    ! [A_270] : ~ r2_hidden(A_270,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_5713])).

tff(c_8765,plain,(
    ! [C_432] : ~ r2_hidden(C_432,k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_8753,c_8105])).

tff(c_8782,plain,(
    ! [C_432] : ~ r2_hidden(C_432,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8601,c_8765])).

tff(c_10198,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10110,c_8782])).

tff(c_10235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9231,c_10198])).

tff(c_10237,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9210])).

tff(c_10249,plain,
    ( k2_relat_1('#skF_7') = '#skF_5'
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10237,c_58])).

tff(c_10263,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_102,c_8601,c_10249])).

tff(c_10236,plain,(
    ! [B_423] : v1_funct_2(k2_funct_1('#skF_7'),'#skF_5',B_423) ),
    inference(splitRight,[status(thm)],[c_9210])).

tff(c_10634,plain,(
    ! [B_423] : v1_funct_2(k2_funct_1('#skF_7'),'#skF_6',B_423) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10263,c_10236])).

tff(c_10311,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_7'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10263,c_5699])).

tff(c_10637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10634,c_10311])).

tff(c_10638,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8139])).

tff(c_60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10658,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_60])).

tff(c_64,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10659,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_64])).

tff(c_10656,plain,(
    ! [A_2] : r1_tarski('#skF_6',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_6])).

tff(c_10653,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_10638,c_38])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10655,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_10638,c_40])).

tff(c_11591,plain,(
    ! [B_594,A_595] :
      ( v1_funct_2(B_594,k1_relat_1(B_594),A_595)
      | ~ r1_tarski(k2_relat_1(B_594),A_595)
      | ~ v1_funct_1(B_594)
      | ~ v1_relat_1(B_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_11600,plain,(
    ! [A_595] :
      ( v1_funct_2('#skF_6','#skF_6',A_595)
      | ~ r1_tarski(k2_relat_1('#skF_6'),A_595)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10655,c_11591])).

tff(c_11603,plain,(
    ! [A_595] : v1_funct_2('#skF_6','#skF_6',A_595) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10658,c_10659,c_10656,c_10653,c_11600])).

tff(c_184,plain,(
    ! [A_65] :
      ( k4_relat_1(A_65) = k1_xboole_0
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_192,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_184])).

tff(c_10647,plain,(
    k4_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_10638,c_192])).

tff(c_10657,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_2])).

tff(c_10639,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8139])).

tff(c_10665,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_10639])).

tff(c_10640,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_8127])).

tff(c_76,plain,(
    ! [C_50,A_48] :
      ( k1_xboole_0 = C_50
      | ~ v1_funct_2(C_50,A_48,k1_xboole_0)
      | k1_xboole_0 = A_48
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_113,plain,(
    ! [C_50,A_48] :
      ( k1_xboole_0 = C_50
      | ~ v1_funct_2(C_50,A_48,k1_xboole_0)
      | k1_xboole_0 = A_48
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_76])).

tff(c_11144,plain,(
    ! [C_560,A_561] :
      ( C_560 = '#skF_6'
      | ~ v1_funct_2(C_560,A_561,'#skF_6')
      | A_561 = '#skF_6'
      | ~ m1_subset_1(C_560,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_10638,c_10638,c_10638,c_113])).

tff(c_11152,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_106,c_11144])).

tff(c_11166,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10640,c_11152])).

tff(c_11167,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_10665,c_11166])).

tff(c_10805,plain,(
    ! [A_533] :
      ( k4_relat_1(A_533) = k2_funct_1(A_533)
      | ~ v2_funct_1(A_533)
      | ~ v1_funct_1(A_533)
      | ~ v1_relat_1(A_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10811,plain,
    ( k4_relat_1('#skF_7') = k2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_10805])).

tff(c_10815,plain,(
    k4_relat_1('#skF_7') = k2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_108,c_10811])).

tff(c_10822,plain,
    ( v1_xboole_0(k2_funct_1('#skF_7'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10815,c_36])).

tff(c_10831,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10822])).

tff(c_11176,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11167,c_10831])).

tff(c_11197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10657,c_11176])).

tff(c_11199,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_10822])).

tff(c_10652,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_4])).

tff(c_11221,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_11199,c_10652])).

tff(c_11227,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11221,c_11221,c_10815])).

tff(c_11239,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10647,c_11227])).

tff(c_11231,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11221,c_5699])).

tff(c_11328,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11239,c_11231])).

tff(c_11613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11603,c_11328])).

tff(c_11614,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitRight,[status(thm)],[c_5714])).

tff(c_11617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11614,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.61/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/2.91  
% 8.61/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/2.92  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 8.61/2.92  
% 8.61/2.92  %Foreground sorts:
% 8.61/2.92  
% 8.61/2.92  
% 8.61/2.92  %Background operators:
% 8.61/2.92  
% 8.61/2.92  
% 8.61/2.92  %Foreground operators:
% 8.61/2.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.61/2.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.61/2.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.61/2.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.61/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.61/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.61/2.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.61/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.61/2.92  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.61/2.92  tff('#skF_7', type, '#skF_7': $i).
% 8.61/2.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.61/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.61/2.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.61/2.92  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 8.61/2.92  tff('#skF_5', type, '#skF_5': $i).
% 8.61/2.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.61/2.92  tff('#skF_6', type, '#skF_6': $i).
% 8.61/2.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.61/2.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.61/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.61/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.61/2.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.61/2.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.61/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.61/2.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.61/2.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.61/2.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.61/2.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.61/2.92  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.61/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.61/2.92  
% 8.91/2.94  tff(f_193, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.91/2.94  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.91/2.94  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.91/2.94  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.91/2.94  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 8.91/2.94  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 8.91/2.94  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.91/2.94  tff(f_65, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.91/2.94  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.91/2.94  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.91/2.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.91/2.94  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.91/2.94  tff(f_164, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 8.91/2.94  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.91/2.94  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.91/2.94  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.91/2.94  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.91/2.94  tff(f_176, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 8.91/2.94  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.91/2.94  tff(f_124, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 8.91/2.94  tff(c_104, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 8.91/2.94  tff(c_285, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.91/2.94  tff(c_297, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_104, c_285])).
% 8.91/2.94  tff(c_108, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 8.91/2.94  tff(c_102, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 8.91/2.94  tff(c_100, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_193])).
% 8.91/2.94  tff(c_5925, plain, (![A_297, B_298, C_299]: (k2_relset_1(A_297, B_298, C_299)=k2_relat_1(C_299) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.91/2.94  tff(c_5934, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_104, c_5925])).
% 8.91/2.94  tff(c_5948, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5934])).
% 8.91/2.94  tff(c_58, plain, (![A_37]: (k1_relat_1(k2_funct_1(A_37))=k2_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.91/2.94  tff(c_320, plain, (![A_87]: (k4_relat_1(A_87)=k2_funct_1(A_87) | ~v2_funct_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.91/2.94  tff(c_326, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_102, c_320])).
% 8.91/2.94  tff(c_330, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_326])).
% 8.91/2.94  tff(c_36, plain, (![A_32]: (v1_xboole_0(k4_relat_1(A_32)) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.91/2.94  tff(c_340, plain, (v1_xboole_0(k2_funct_1('#skF_7')) | ~v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_330, c_36])).
% 8.91/2.94  tff(c_348, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_340])).
% 8.91/2.94  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.91/2.94  tff(c_1267, plain, (![A_156, B_157]: (r2_hidden(k4_tarski('#skF_2'(A_156, B_157), '#skF_1'(A_156, B_157)), A_156) | r2_hidden('#skF_3'(A_156, B_157), B_157) | k2_relat_1(A_156)=B_157)), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.91/2.94  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.91/2.94  tff(c_309, plain, (![C_80, B_81, A_82]: (~v1_xboole_0(C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.91/2.94  tff(c_315, plain, (![A_5, A_82]: (~v1_xboole_0(A_5) | ~r2_hidden(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_309])).
% 8.91/2.94  tff(c_316, plain, (![A_82]: (~r2_hidden(A_82, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_315])).
% 8.91/2.94  tff(c_1274, plain, (![B_157]: (r2_hidden('#skF_3'(k1_xboole_0, B_157), B_157) | k2_relat_1(k1_xboole_0)=B_157)), inference(resolution, [status(thm)], [c_1267, c_316])).
% 8.91/2.94  tff(c_1277, plain, (![B_157]: (r2_hidden('#skF_3'(k1_xboole_0, B_157), B_157) | k1_xboole_0=B_157)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1274])).
% 8.91/2.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.91/2.94  tff(c_52, plain, (![A_36]: (v1_funct_1(k2_funct_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.91/2.94  tff(c_98, plain, (~m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5'))) | ~v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5') | ~v1_funct_1(k2_funct_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 8.91/2.94  tff(c_260, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_98])).
% 8.91/2.94  tff(c_263, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_260])).
% 8.91/2.94  tff(c_266, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_263])).
% 8.91/2.94  tff(c_267, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.91/2.94  tff(c_270, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_104, c_267])).
% 8.91/2.94  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_270])).
% 8.91/2.94  tff(c_283, plain, (~v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5') | ~m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(splitRight, [status(thm)], [c_98])).
% 8.91/2.94  tff(c_308, plain, (~m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(splitLeft, [status(thm)], [c_283])).
% 8.91/2.94  tff(c_481, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.91/2.94  tff(c_484, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_104, c_481])).
% 8.91/2.94  tff(c_496, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_484])).
% 8.91/2.94  tff(c_54, plain, (![A_36]: (v1_relat_1(k2_funct_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.91/2.94  tff(c_284, plain, (v1_funct_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_98])).
% 8.91/2.94  tff(c_380, plain, (![A_94]: (k1_relat_1(k2_funct_1(A_94))=k2_relat_1(A_94) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.91/2.94  tff(c_88, plain, (![A_51]: (v1_funct_2(A_51, k1_relat_1(A_51), k2_relat_1(A_51)) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.91/2.94  tff(c_4249, plain, (![A_238]: (v1_funct_2(k2_funct_1(A_238), k2_relat_1(A_238), k2_relat_1(k2_funct_1(A_238))) | ~v1_funct_1(k2_funct_1(A_238)) | ~v1_relat_1(k2_funct_1(A_238)) | ~v2_funct_1(A_238) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(superposition, [status(thm), theory('equality')], [c_380, c_88])).
% 8.91/2.94  tff(c_4297, plain, (v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', k2_relat_1(k2_funct_1('#skF_7'))) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_496, c_4249])).
% 8.91/2.94  tff(c_4320, plain, (v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', k2_relat_1(k2_funct_1('#skF_7'))) | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_102, c_284, c_4297])).
% 8.91/2.94  tff(c_4327, plain, (~v1_relat_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_4320])).
% 8.91/2.94  tff(c_4330, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_4327])).
% 8.91/2.94  tff(c_4334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_4330])).
% 8.91/2.94  tff(c_4336, plain, (v1_relat_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_4320])).
% 8.91/2.94  tff(c_106, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_193])).
% 8.91/2.94  tff(c_428, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.91/2.94  tff(c_442, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_104, c_428])).
% 8.91/2.94  tff(c_1300, plain, (![B_160, A_161, C_162]: (k1_xboole_0=B_160 | k1_relset_1(A_161, B_160, C_162)=A_161 | ~v1_funct_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.91/2.94  tff(c_1312, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_104, c_1300])).
% 8.91/2.94  tff(c_1330, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_442, c_1312])).
% 8.91/2.94  tff(c_1334, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1330])).
% 8.91/2.94  tff(c_56, plain, (![A_37]: (k2_relat_1(k2_funct_1(A_37))=k1_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.91/2.94  tff(c_527, plain, (![A_116]: (m1_subset_1(A_116, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_116), k2_relat_1(A_116)))) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.91/2.94  tff(c_5094, plain, (![A_250]: (m1_subset_1(k2_funct_1(A_250), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_250)), k1_relat_1(A_250)))) | ~v1_funct_1(k2_funct_1(A_250)) | ~v1_relat_1(k2_funct_1(A_250)) | ~v2_funct_1(A_250) | ~v1_funct_1(A_250) | ~v1_relat_1(A_250))), inference(superposition, [status(thm), theory('equality')], [c_56, c_527])).
% 8.91/2.94  tff(c_5140, plain, (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_7')), '#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1334, c_5094])).
% 8.91/2.94  tff(c_5184, plain, (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_7')), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_102, c_4336, c_284, c_5140])).
% 8.91/2.94  tff(c_5216, plain, (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_7'), '#skF_5'))) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58, c_5184])).
% 8.91/2.94  tff(c_5229, plain, (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_102, c_496, c_5216])).
% 8.91/2.94  tff(c_5231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_5229])).
% 8.91/2.94  tff(c_5232, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1330])).
% 8.91/2.94  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.91/2.94  tff(c_5269, plain, (![A_2]: (r1_tarski('#skF_6', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_5232, c_6])).
% 8.91/2.94  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.91/2.94  tff(c_888, plain, (![B_139, A_140]: (m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_139), A_140))) | ~r1_tarski(k2_relat_1(B_139), A_140) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.91/2.94  tff(c_1285, plain, (![B_159]: (m1_subset_1(B_159, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_159), k1_xboole_0) | ~v1_funct_1(B_159) | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_10, c_888])).
% 8.91/2.94  tff(c_1288, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_6', k1_xboole_0) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_496, c_1285])).
% 8.91/2.94  tff(c_1296, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_1288])).
% 8.91/2.94  tff(c_1299, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1296])).
% 8.91/2.94  tff(c_5235, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5232, c_1299])).
% 8.91/2.94  tff(c_5384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5269, c_5235])).
% 8.91/2.94  tff(c_5385, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1296])).
% 8.91/2.94  tff(c_18, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.91/2.94  tff(c_5400, plain, (![A_9]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_9, '#skF_7'))), inference(resolution, [status(thm)], [c_5385, c_18])).
% 8.91/2.94  tff(c_5418, plain, (![A_255]: (~r2_hidden(A_255, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5400])).
% 8.91/2.94  tff(c_5435, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1277, c_5418])).
% 8.91/2.94  tff(c_5477, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5435, c_2])).
% 8.91/2.94  tff(c_5483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_5477])).
% 8.91/2.94  tff(c_5485, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_340])).
% 8.91/2.94  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.91/2.94  tff(c_5503, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_5485, c_4])).
% 8.91/2.94  tff(c_5524, plain, (![A_5]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_5503, c_14])).
% 8.91/2.94  tff(c_170, plain, (![A_63]: (v1_xboole_0(k4_relat_1(A_63)) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.91/2.94  tff(c_182, plain, (![A_63]: (k4_relat_1(A_63)=k1_xboole_0 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_170, c_4])).
% 8.91/2.94  tff(c_5498, plain, (k4_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_5485, c_182])).
% 8.91/2.94  tff(c_5552, plain, (k4_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5503, c_5498])).
% 8.91/2.94  tff(c_5553, plain, (k2_funct_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5552, c_330])).
% 8.91/2.94  tff(c_5576, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_308])).
% 8.91/2.94  tff(c_5694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5524, c_5576])).
% 8.91/2.94  tff(c_5695, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitRight, [status(thm)], [c_315])).
% 8.91/2.94  tff(c_5698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5695, c_2])).
% 8.91/2.94  tff(c_5699, plain, (~v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_283])).
% 8.91/2.94  tff(c_5700, plain, (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(splitRight, [status(thm)], [c_283])).
% 8.91/2.94  tff(c_5873, plain, (![A_288, B_289, C_290]: (k1_relset_1(A_288, B_289, C_290)=k1_relat_1(C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.91/2.94  tff(c_5894, plain, (k1_relset_1('#skF_6', '#skF_5', k2_funct_1('#skF_7'))=k1_relat_1(k2_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_5700, c_5873])).
% 8.91/2.94  tff(c_7748, plain, (![B_368, C_369, A_370]: (k1_xboole_0=B_368 | v1_funct_2(C_369, A_370, B_368) | k1_relset_1(A_370, B_368, C_369)!=A_370 | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_370, B_368))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.91/2.94  tff(c_7757, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5') | k1_relset_1('#skF_6', '#skF_5', k2_funct_1('#skF_7'))!='#skF_6'), inference(resolution, [status(thm)], [c_5700, c_7748])).
% 8.91/2.94  tff(c_7774, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_5') | k1_relat_1(k2_funct_1('#skF_7'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5894, c_7757])).
% 8.91/2.94  tff(c_7775, plain, (k1_xboole_0='#skF_5' | k1_relat_1(k2_funct_1('#skF_7'))!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_5699, c_7774])).
% 8.91/2.94  tff(c_7782, plain, (k1_relat_1(k2_funct_1('#skF_7'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_7775])).
% 8.91/2.94  tff(c_7785, plain, (k2_relat_1('#skF_7')!='#skF_6' | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58, c_7782])).
% 8.91/2.94  tff(c_7788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_102, c_5948, c_7785])).
% 8.91/2.94  tff(c_7789, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_7775])).
% 8.91/2.94  tff(c_7830, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7789, c_2])).
% 8.91/2.94  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.91/2.94  tff(c_7823, plain, (![B_4]: (k2_zfmisc_1('#skF_5', B_4)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7789, c_7789, c_12])).
% 8.91/2.94  tff(c_5705, plain, (![C_268, B_269, A_270]: (~v1_xboole_0(C_268) | ~m1_subset_1(B_269, k1_zfmisc_1(C_268)) | ~r2_hidden(A_270, B_269))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.91/2.94  tff(c_5713, plain, (![A_270]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_270, '#skF_7'))), inference(resolution, [status(thm)], [c_104, c_5705])).
% 8.91/2.94  tff(c_5718, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_5713])).
% 8.91/2.94  tff(c_8100, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7823, c_5718])).
% 8.91/2.94  tff(c_8104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7830, c_8100])).
% 8.91/2.94  tff(c_8106, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_5713])).
% 8.91/2.94  tff(c_8123, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_8106, c_4])).
% 8.91/2.94  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.91/2.94  tff(c_8139, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_8123, c_8])).
% 8.91/2.94  tff(c_8151, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_8139])).
% 8.91/2.94  tff(c_8127, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8123, c_104])).
% 8.91/2.94  tff(c_8152, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_8127])).
% 8.91/2.94  tff(c_8162, plain, (![B_4]: (k2_zfmisc_1('#skF_5', B_4)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_8151, c_12])).
% 8.91/2.94  tff(c_8508, plain, (![A_403, B_404, C_405]: (k2_relset_1(A_403, B_404, C_405)=k2_relat_1(C_405) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_403, B_404))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.91/2.94  tff(c_8582, plain, (![B_417, C_418]: (k2_relset_1('#skF_5', B_417, C_418)=k2_relat_1(C_418) | ~m1_subset_1(C_418, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8162, c_8508])).
% 8.91/2.94  tff(c_8594, plain, (![B_419]: (k2_relset_1('#skF_5', B_419, '#skF_7')=k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_8152, c_8582])).
% 8.91/2.94  tff(c_8601, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_8594, c_100])).
% 8.91/2.94  tff(c_8161, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_8151, c_10])).
% 8.91/2.94  tff(c_8287, plain, (m1_subset_1(k2_funct_1('#skF_7'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8161, c_5700])).
% 8.91/2.94  tff(c_8551, plain, (![A_411, B_412, C_413]: (k1_relset_1(A_411, B_412, C_413)=k1_relat_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.91/2.94  tff(c_9084, plain, (![B_457, C_458]: (k1_relset_1('#skF_5', B_457, C_458)=k1_relat_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8162, c_8551])).
% 8.91/2.94  tff(c_9092, plain, (![B_457]: (k1_relset_1('#skF_5', B_457, k2_funct_1('#skF_7'))=k1_relat_1(k2_funct_1('#skF_7')))), inference(resolution, [status(thm)], [c_8287, c_9084])).
% 8.91/2.94  tff(c_78, plain, (![C_50, B_49]: (v1_funct_2(C_50, k1_xboole_0, B_49) | k1_relset_1(k1_xboole_0, B_49, C_50)!=k1_xboole_0 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_49))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.91/2.94  tff(c_112, plain, (![C_50, B_49]: (v1_funct_2(C_50, k1_xboole_0, B_49) | k1_relset_1(k1_xboole_0, B_49, C_50)!=k1_xboole_0 | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_78])).
% 8.91/2.94  tff(c_8654, plain, (![C_422, B_423]: (v1_funct_2(C_422, '#skF_5', B_423) | k1_relset_1('#skF_5', B_423, C_422)!='#skF_5' | ~m1_subset_1(C_422, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_8151, c_8151, c_8151, c_112])).
% 8.91/2.94  tff(c_8662, plain, (![B_423]: (v1_funct_2(k2_funct_1('#skF_7'), '#skF_5', B_423) | k1_relset_1('#skF_5', B_423, k2_funct_1('#skF_7'))!='#skF_5')), inference(resolution, [status(thm)], [c_8287, c_8654])).
% 8.91/2.94  tff(c_9210, plain, (![B_423]: (v1_funct_2(k2_funct_1('#skF_7'), '#skF_5', B_423) | k1_relat_1(k2_funct_1('#skF_7'))!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9092, c_8662])).
% 8.91/2.94  tff(c_9226, plain, (k1_relat_1(k2_funct_1('#skF_7'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_9210])).
% 8.91/2.94  tff(c_9229, plain, (k2_relat_1('#skF_7')!='#skF_5' | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58, c_9226])).
% 8.91/2.94  tff(c_9231, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_102, c_8601, c_9229])).
% 8.91/2.94  tff(c_8165, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_8151, c_38])).
% 8.91/2.94  tff(c_9978, plain, (![A_502, B_503]: (r2_hidden(k4_tarski('#skF_2'(A_502, B_503), '#skF_1'(A_502, B_503)), A_502) | r2_hidden('#skF_3'(A_502, B_503), B_503) | k2_relat_1(A_502)=B_503)), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.91/2.94  tff(c_5714, plain, (![A_5, A_270]: (~v1_xboole_0(A_5) | ~r2_hidden(A_270, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_5705])).
% 8.91/2.94  tff(c_5716, plain, (![A_270]: (~r2_hidden(A_270, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_5714])).
% 8.91/2.94  tff(c_8154, plain, (![A_270]: (~r2_hidden(A_270, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_5716])).
% 8.91/2.94  tff(c_10074, plain, (![B_503]: (r2_hidden('#skF_3'('#skF_5', B_503), B_503) | k2_relat_1('#skF_5')=B_503)), inference(resolution, [status(thm)], [c_9978, c_8154])).
% 8.91/2.94  tff(c_10110, plain, (![B_504]: (r2_hidden('#skF_3'('#skF_5', B_504), B_504) | B_504='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8165, c_10074])).
% 8.91/2.94  tff(c_8753, plain, (![A_431, C_432]: (r2_hidden(k4_tarski('#skF_4'(A_431, k2_relat_1(A_431), C_432), C_432), A_431) | ~r2_hidden(C_432, k2_relat_1(A_431)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.91/2.94  tff(c_8105, plain, (![A_270]: (~r2_hidden(A_270, '#skF_7'))), inference(splitRight, [status(thm)], [c_5713])).
% 8.91/2.94  tff(c_8765, plain, (![C_432]: (~r2_hidden(C_432, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_8753, c_8105])).
% 8.91/2.94  tff(c_8782, plain, (![C_432]: (~r2_hidden(C_432, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8601, c_8765])).
% 8.91/2.94  tff(c_10198, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_10110, c_8782])).
% 8.91/2.94  tff(c_10235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9231, c_10198])).
% 8.91/2.94  tff(c_10237, plain, (k1_relat_1(k2_funct_1('#skF_7'))='#skF_5'), inference(splitRight, [status(thm)], [c_9210])).
% 8.91/2.94  tff(c_10249, plain, (k2_relat_1('#skF_7')='#skF_5' | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10237, c_58])).
% 8.91/2.94  tff(c_10263, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_102, c_8601, c_10249])).
% 8.91/2.94  tff(c_10236, plain, (![B_423]: (v1_funct_2(k2_funct_1('#skF_7'), '#skF_5', B_423))), inference(splitRight, [status(thm)], [c_9210])).
% 8.91/2.94  tff(c_10634, plain, (![B_423]: (v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', B_423))), inference(demodulation, [status(thm), theory('equality')], [c_10263, c_10236])).
% 8.91/2.94  tff(c_10311, plain, (~v1_funct_2(k2_funct_1('#skF_7'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10263, c_5699])).
% 8.91/2.94  tff(c_10637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10634, c_10311])).
% 8.91/2.94  tff(c_10638, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_8139])).
% 8.91/2.94  tff(c_60, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.91/2.94  tff(c_10658, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_60])).
% 8.91/2.94  tff(c_64, plain, (v1_funct_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.91/2.94  tff(c_10659, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_64])).
% 8.91/2.94  tff(c_10656, plain, (![A_2]: (r1_tarski('#skF_6', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_6])).
% 8.91/2.94  tff(c_10653, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_10638, c_38])).
% 8.91/2.94  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.91/2.94  tff(c_10655, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_10638, c_40])).
% 8.91/2.94  tff(c_11591, plain, (![B_594, A_595]: (v1_funct_2(B_594, k1_relat_1(B_594), A_595) | ~r1_tarski(k2_relat_1(B_594), A_595) | ~v1_funct_1(B_594) | ~v1_relat_1(B_594))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.91/2.94  tff(c_11600, plain, (![A_595]: (v1_funct_2('#skF_6', '#skF_6', A_595) | ~r1_tarski(k2_relat_1('#skF_6'), A_595) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10655, c_11591])).
% 8.91/2.94  tff(c_11603, plain, (![A_595]: (v1_funct_2('#skF_6', '#skF_6', A_595))), inference(demodulation, [status(thm), theory('equality')], [c_10658, c_10659, c_10656, c_10653, c_11600])).
% 8.91/2.94  tff(c_184, plain, (![A_65]: (k4_relat_1(A_65)=k1_xboole_0 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_170, c_4])).
% 8.91/2.94  tff(c_192, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_184])).
% 8.91/2.94  tff(c_10647, plain, (k4_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_10638, c_192])).
% 8.91/2.94  tff(c_10657, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_2])).
% 8.91/2.94  tff(c_10639, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_8139])).
% 8.91/2.94  tff(c_10665, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_10639])).
% 8.91/2.94  tff(c_10640, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_8127])).
% 8.91/2.94  tff(c_76, plain, (![C_50, A_48]: (k1_xboole_0=C_50 | ~v1_funct_2(C_50, A_48, k1_xboole_0) | k1_xboole_0=A_48 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.91/2.94  tff(c_113, plain, (![C_50, A_48]: (k1_xboole_0=C_50 | ~v1_funct_2(C_50, A_48, k1_xboole_0) | k1_xboole_0=A_48 | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_76])).
% 8.91/2.94  tff(c_11144, plain, (![C_560, A_561]: (C_560='#skF_6' | ~v1_funct_2(C_560, A_561, '#skF_6') | A_561='#skF_6' | ~m1_subset_1(C_560, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_10638, c_10638, c_10638, c_113])).
% 8.91/2.94  tff(c_11152, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_106, c_11144])).
% 8.91/2.94  tff(c_11166, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10640, c_11152])).
% 8.91/2.94  tff(c_11167, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_10665, c_11166])).
% 8.91/2.94  tff(c_10805, plain, (![A_533]: (k4_relat_1(A_533)=k2_funct_1(A_533) | ~v2_funct_1(A_533) | ~v1_funct_1(A_533) | ~v1_relat_1(A_533))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.91/2.94  tff(c_10811, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_102, c_10805])).
% 8.91/2.94  tff(c_10815, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_108, c_10811])).
% 8.91/2.94  tff(c_10822, plain, (v1_xboole_0(k2_funct_1('#skF_7')) | ~v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10815, c_36])).
% 8.91/2.94  tff(c_10831, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_10822])).
% 8.91/2.94  tff(c_11176, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11167, c_10831])).
% 8.91/2.94  tff(c_11197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10657, c_11176])).
% 8.91/2.94  tff(c_11199, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_10822])).
% 8.91/2.94  tff(c_10652, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_4])).
% 8.91/2.94  tff(c_11221, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_11199, c_10652])).
% 8.91/2.94  tff(c_11227, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11221, c_11221, c_10815])).
% 8.91/2.94  tff(c_11239, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10647, c_11227])).
% 8.91/2.94  tff(c_11231, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11221, c_5699])).
% 8.91/2.94  tff(c_11328, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11239, c_11231])).
% 8.91/2.94  tff(c_11613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11603, c_11328])).
% 8.91/2.94  tff(c_11614, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitRight, [status(thm)], [c_5714])).
% 8.91/2.94  tff(c_11617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11614, c_2])).
% 8.91/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/2.94  
% 8.91/2.94  Inference rules
% 8.91/2.94  ----------------------
% 8.91/2.94  #Ref     : 0
% 8.91/2.94  #Sup     : 2584
% 8.91/2.94  #Fact    : 0
% 8.91/2.94  #Define  : 0
% 8.91/2.94  #Split   : 26
% 8.91/2.94  #Chain   : 0
% 8.91/2.94  #Close   : 0
% 8.91/2.94  
% 8.91/2.94  Ordering : KBO
% 8.91/2.94  
% 8.91/2.94  Simplification rules
% 8.91/2.94  ----------------------
% 8.91/2.94  #Subsume      : 500
% 8.91/2.94  #Demod        : 4085
% 8.91/2.94  #Tautology    : 1300
% 8.91/2.94  #SimpNegUnit  : 36
% 8.91/2.94  #BackRed      : 444
% 8.91/2.94  
% 8.91/2.94  #Partial instantiations: 0
% 8.91/2.94  #Strategies tried      : 1
% 8.91/2.94  
% 8.91/2.95  Timing (in seconds)
% 8.91/2.95  ----------------------
% 8.91/2.95  Preprocessing        : 0.40
% 8.91/2.95  Parsing              : 0.21
% 8.91/2.95  CNF conversion       : 0.03
% 8.91/2.95  Main loop            : 1.72
% 8.91/2.95  Inferencing          : 0.53
% 8.91/2.95  Reduction            : 0.61
% 8.91/2.95  Demodulation         : 0.45
% 8.91/2.95  BG Simplification    : 0.07
% 8.91/2.95  Subsumption          : 0.39
% 8.91/2.95  Abstraction          : 0.08
% 8.91/2.95  MUC search           : 0.00
% 8.91/2.95  Cooper               : 0.00
% 8.91/2.95  Total                : 2.18
% 8.91/2.95  Index Insertion      : 0.00
% 8.91/2.95  Index Deletion       : 0.00
% 8.91/2.95  Index Matching       : 0.00
% 8.91/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
