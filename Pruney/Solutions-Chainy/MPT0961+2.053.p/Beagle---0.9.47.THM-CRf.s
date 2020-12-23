%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 318 expanded)
%              Number of leaves         :   24 ( 112 expanded)
%              Depth                    :    8
%              Number of atoms          :  151 ( 761 expanded)
%              Number of equality atoms :   55 ( 309 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,(
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

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_740,plain,(
    ! [C_142,A_143,B_144] :
      ( m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ r1_tarski(k2_relat_1(C_142),B_144)
      | ~ r1_tarski(k1_relat_1(C_142),A_143)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_212,plain,(
    ! [C_55,A_56,B_57] :
      ( m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ r1_tarski(k2_relat_1(C_55),B_57)
      | ~ r1_tarski(k1_relat_1(C_55),A_56)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(C_61,k2_zfmisc_1(A_62,B_63))
      | ~ r1_tarski(k2_relat_1(C_61),B_63)
      | ~ r1_tarski(k1_relat_1(C_61),A_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(resolution,[status(thm)],[c_212,c_10])).

tff(c_255,plain,(
    ! [C_64,A_65] :
      ( r1_tarski(C_64,k2_zfmisc_1(A_65,k2_relat_1(C_64)))
      | ~ r1_tarski(k1_relat_1(C_64),A_65)
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_246])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_27,B_28,A_4] :
      ( k1_relset_1(A_27,B_28,A_4) = k1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_27,B_28)) ) ),
    inference(resolution,[status(thm)],[c_12,c_98])).

tff(c_282,plain,(
    ! [A_66,C_67] :
      ( k1_relset_1(A_66,k2_relat_1(C_67),C_67) = k1_relat_1(C_67)
      | ~ r1_tarski(k1_relat_1(C_67),A_66)
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_255,c_103])).

tff(c_294,plain,(
    ! [C_67] :
      ( k1_relset_1(k1_relat_1(C_67),k2_relat_1(C_67),C_67) = k1_relat_1(C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_282])).

tff(c_63,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_68,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_24,plain,(
    ! [C_12,A_10,B_11] :
      ( m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ r1_tarski(k2_relat_1(C_12),B_11)
      | ~ r1_tarski(k1_relat_1(C_12),A_10)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,(
    ! [B_58,C_59,A_60] :
      ( k1_xboole_0 = B_58
      | v1_funct_2(C_59,A_60,B_58)
      | k1_relset_1(A_60,B_58,C_59) != A_60
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_522,plain,(
    ! [B_101,C_102,A_103] :
      ( k1_xboole_0 = B_101
      | v1_funct_2(C_102,A_103,B_101)
      | k1_relset_1(A_103,B_101,C_102) != A_103
      | ~ r1_tarski(k2_relat_1(C_102),B_101)
      | ~ r1_tarski(k1_relat_1(C_102),A_103)
      | ~ v1_relat_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_24,c_236])).

tff(c_535,plain,(
    ! [C_104,A_105] :
      ( k2_relat_1(C_104) = k1_xboole_0
      | v1_funct_2(C_104,A_105,k2_relat_1(C_104))
      | k1_relset_1(A_105,k2_relat_1(C_104),C_104) != A_105
      | ~ r1_tarski(k1_relat_1(C_104),A_105)
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_6,c_522])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_62,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_549,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_535,c_62])).

tff(c_560,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_549])).

tff(c_561,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_560])).

tff(c_566,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_561])).

tff(c_570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_566])).

tff(c_571,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_577,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_571,c_16])).

tff(c_56,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_61,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_574,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_61])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_574])).

tff(c_597,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_758,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_740,c_597])).

tff(c_769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_6,c_758])).

tff(c_770,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_775,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_8])).

tff(c_771,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_780,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_771])).

tff(c_853,plain,(
    ! [A_157,B_158,C_159] :
      ( k1_relset_1(A_157,B_158,C_159) = k1_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_859,plain,(
    ! [A_160,B_161,A_162] :
      ( k1_relset_1(A_160,B_161,A_162) = k1_relat_1(A_162)
      | ~ r1_tarski(A_162,k2_zfmisc_1(A_160,B_161)) ) ),
    inference(resolution,[status(thm)],[c_12,c_853])).

tff(c_863,plain,(
    ! [A_160,B_161] : k1_relset_1(A_160,B_161,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_775,c_859])).

tff(c_869,plain,(
    ! [A_160,B_161] : k1_relset_1(A_160,B_161,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_863])).

tff(c_30,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_908,plain,(
    ! [C_172,B_173] :
      ( v1_funct_2(C_172,'#skF_1',B_173)
      | k1_relset_1('#skF_1',B_173,C_172) != '#skF_1'
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_173))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_770,c_770,c_770,c_30])).

tff(c_914,plain,(
    ! [A_174,B_175] :
      ( v1_funct_2(A_174,'#skF_1',B_175)
      | k1_relset_1('#skF_1',B_175,A_174) != '#skF_1'
      | ~ r1_tarski(A_174,k2_zfmisc_1('#skF_1',B_175)) ) ),
    inference(resolution,[status(thm)],[c_12,c_908])).

tff(c_918,plain,(
    ! [B_175] :
      ( v1_funct_2('#skF_1','#skF_1',B_175)
      | k1_relset_1('#skF_1',B_175,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_775,c_914])).

tff(c_925,plain,(
    ! [B_175] : v1_funct_2('#skF_1','#skF_1',B_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_918])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_773,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_770,c_14])).

tff(c_814,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_780,c_773,c_780,c_44])).

tff(c_815,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_814])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_815])).

tff(c_931,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_958,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_931])).

tff(c_962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_958])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.10/1.49  
% 3.10/1.49  %Foreground sorts:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Background operators:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Foreground operators:
% 3.10/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.10/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.49  
% 3.10/1.50  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.10/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.10/1.50  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.10/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.10/1.50  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.10/1.50  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.10/1.50  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.10/1.50  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.10/1.50  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.10/1.50  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.10/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.50  tff(c_740, plain, (![C_142, A_143, B_144]: (m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~r1_tarski(k2_relat_1(C_142), B_144) | ~r1_tarski(k1_relat_1(C_142), A_143) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.10/1.50  tff(c_212, plain, (![C_55, A_56, B_57]: (m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~r1_tarski(k2_relat_1(C_55), B_57) | ~r1_tarski(k1_relat_1(C_55), A_56) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.10/1.50  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.50  tff(c_246, plain, (![C_61, A_62, B_63]: (r1_tarski(C_61, k2_zfmisc_1(A_62, B_63)) | ~r1_tarski(k2_relat_1(C_61), B_63) | ~r1_tarski(k1_relat_1(C_61), A_62) | ~v1_relat_1(C_61))), inference(resolution, [status(thm)], [c_212, c_10])).
% 3.10/1.50  tff(c_255, plain, (![C_64, A_65]: (r1_tarski(C_64, k2_zfmisc_1(A_65, k2_relat_1(C_64))) | ~r1_tarski(k1_relat_1(C_64), A_65) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_6, c_246])).
% 3.10/1.50  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.50  tff(c_98, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.10/1.50  tff(c_103, plain, (![A_27, B_28, A_4]: (k1_relset_1(A_27, B_28, A_4)=k1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_27, B_28)))), inference(resolution, [status(thm)], [c_12, c_98])).
% 3.10/1.50  tff(c_282, plain, (![A_66, C_67]: (k1_relset_1(A_66, k2_relat_1(C_67), C_67)=k1_relat_1(C_67) | ~r1_tarski(k1_relat_1(C_67), A_66) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_255, c_103])).
% 3.10/1.50  tff(c_294, plain, (![C_67]: (k1_relset_1(k1_relat_1(C_67), k2_relat_1(C_67), C_67)=k1_relat_1(C_67) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_6, c_282])).
% 3.10/1.50  tff(c_63, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.10/1.50  tff(c_67, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_63])).
% 3.10/1.50  tff(c_68, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_67])).
% 3.10/1.50  tff(c_24, plain, (![C_12, A_10, B_11]: (m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~r1_tarski(k2_relat_1(C_12), B_11) | ~r1_tarski(k1_relat_1(C_12), A_10) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.10/1.50  tff(c_236, plain, (![B_58, C_59, A_60]: (k1_xboole_0=B_58 | v1_funct_2(C_59, A_60, B_58) | k1_relset_1(A_60, B_58, C_59)!=A_60 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_58))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.10/1.50  tff(c_522, plain, (![B_101, C_102, A_103]: (k1_xboole_0=B_101 | v1_funct_2(C_102, A_103, B_101) | k1_relset_1(A_103, B_101, C_102)!=A_103 | ~r1_tarski(k2_relat_1(C_102), B_101) | ~r1_tarski(k1_relat_1(C_102), A_103) | ~v1_relat_1(C_102))), inference(resolution, [status(thm)], [c_24, c_236])).
% 3.10/1.50  tff(c_535, plain, (![C_104, A_105]: (k2_relat_1(C_104)=k1_xboole_0 | v1_funct_2(C_104, A_105, k2_relat_1(C_104)) | k1_relset_1(A_105, k2_relat_1(C_104), C_104)!=A_105 | ~r1_tarski(k1_relat_1(C_104), A_105) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_6, c_522])).
% 3.10/1.50  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.10/1.50  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.10/1.50  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 3.10/1.50  tff(c_62, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.10/1.50  tff(c_549, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_535, c_62])).
% 3.10/1.50  tff(c_560, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_549])).
% 3.10/1.50  tff(c_561, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_560])).
% 3.10/1.50  tff(c_566, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_294, c_561])).
% 3.10/1.50  tff(c_570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_566])).
% 3.10/1.50  tff(c_571, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_67])).
% 3.10/1.50  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.10/1.50  tff(c_577, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_571, c_571, c_16])).
% 3.10/1.50  tff(c_56, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.10/1.50  tff(c_60, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_56])).
% 3.10/1.50  tff(c_61, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.10/1.50  tff(c_574, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_571, c_61])).
% 3.10/1.50  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_574])).
% 3.10/1.50  tff(c_597, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 3.10/1.50  tff(c_758, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_740, c_597])).
% 3.10/1.50  tff(c_769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_6, c_758])).
% 3.10/1.50  tff(c_770, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_60])).
% 3.10/1.50  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.50  tff(c_775, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_8])).
% 3.10/1.50  tff(c_771, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.10/1.50  tff(c_780, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_771])).
% 3.10/1.50  tff(c_853, plain, (![A_157, B_158, C_159]: (k1_relset_1(A_157, B_158, C_159)=k1_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.10/1.50  tff(c_859, plain, (![A_160, B_161, A_162]: (k1_relset_1(A_160, B_161, A_162)=k1_relat_1(A_162) | ~r1_tarski(A_162, k2_zfmisc_1(A_160, B_161)))), inference(resolution, [status(thm)], [c_12, c_853])).
% 3.10/1.50  tff(c_863, plain, (![A_160, B_161]: (k1_relset_1(A_160, B_161, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_775, c_859])).
% 3.10/1.50  tff(c_869, plain, (![A_160, B_161]: (k1_relset_1(A_160, B_161, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_863])).
% 3.10/1.50  tff(c_30, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.10/1.50  tff(c_908, plain, (![C_172, B_173]: (v1_funct_2(C_172, '#skF_1', B_173) | k1_relset_1('#skF_1', B_173, C_172)!='#skF_1' | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_173))))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_770, c_770, c_770, c_30])).
% 3.10/1.50  tff(c_914, plain, (![A_174, B_175]: (v1_funct_2(A_174, '#skF_1', B_175) | k1_relset_1('#skF_1', B_175, A_174)!='#skF_1' | ~r1_tarski(A_174, k2_zfmisc_1('#skF_1', B_175)))), inference(resolution, [status(thm)], [c_12, c_908])).
% 3.10/1.50  tff(c_918, plain, (![B_175]: (v1_funct_2('#skF_1', '#skF_1', B_175) | k1_relset_1('#skF_1', B_175, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_775, c_914])).
% 3.10/1.50  tff(c_925, plain, (![B_175]: (v1_funct_2('#skF_1', '#skF_1', B_175))), inference(demodulation, [status(thm), theory('equality')], [c_869, c_918])).
% 3.10/1.50  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.10/1.50  tff(c_773, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_770, c_14])).
% 3.10/1.50  tff(c_814, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_773, c_780, c_773, c_780, c_44])).
% 3.10/1.50  tff(c_815, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_814])).
% 3.10/1.50  tff(c_930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_925, c_815])).
% 3.10/1.50  tff(c_931, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_814])).
% 3.10/1.50  tff(c_958, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_931])).
% 3.10/1.50  tff(c_962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_775, c_958])).
% 3.10/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  Inference rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Ref     : 0
% 3.10/1.50  #Sup     : 168
% 3.10/1.50  #Fact    : 0
% 3.10/1.50  #Define  : 0
% 3.10/1.50  #Split   : 5
% 3.10/1.50  #Chain   : 0
% 3.10/1.50  #Close   : 0
% 3.10/1.50  
% 3.10/1.50  Ordering : KBO
% 3.10/1.50  
% 3.10/1.50  Simplification rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Subsume      : 9
% 3.10/1.50  #Demod        : 172
% 3.10/1.50  #Tautology    : 89
% 3.10/1.50  #SimpNegUnit  : 1
% 3.10/1.50  #BackRed      : 12
% 3.10/1.50  
% 3.10/1.50  #Partial instantiations: 0
% 3.10/1.50  #Strategies tried      : 1
% 3.10/1.50  
% 3.10/1.50  Timing (in seconds)
% 3.10/1.50  ----------------------
% 3.10/1.51  Preprocessing        : 0.29
% 3.10/1.51  Parsing              : 0.15
% 3.10/1.51  CNF conversion       : 0.02
% 3.10/1.51  Main loop            : 0.38
% 3.10/1.51  Inferencing          : 0.14
% 3.10/1.51  Reduction            : 0.11
% 3.10/1.51  Demodulation         : 0.07
% 3.10/1.51  BG Simplification    : 0.02
% 3.10/1.51  Subsumption          : 0.09
% 3.10/1.51  Abstraction          : 0.02
% 3.10/1.51  MUC search           : 0.00
% 3.10/1.51  Cooper               : 0.00
% 3.10/1.51  Total                : 0.71
% 3.10/1.51  Index Insertion      : 0.00
% 3.10/1.51  Index Deletion       : 0.00
% 3.10/1.51  Index Matching       : 0.00
% 3.10/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
