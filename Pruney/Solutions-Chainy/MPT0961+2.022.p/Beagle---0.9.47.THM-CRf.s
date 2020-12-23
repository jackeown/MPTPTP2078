%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:44 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 390 expanded)
%              Number of leaves         :   31 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  128 ( 855 expanded)
%              Number of equality atoms :   46 ( 282 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1080,plain,(
    ! [A_164] :
      ( r1_tarski(A_164,k2_zfmisc_1(k1_relat_1(A_164),k2_relat_1(A_164)))
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1013,plain,(
    ! [A_148,B_149] :
      ( m1_subset_1(A_148,k1_zfmisc_1(B_149))
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_324,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_463,plain,(
    ! [A_104,B_105,A_106] :
      ( k1_relset_1(A_104,B_105,A_106) = k1_relat_1(A_106)
      | ~ r1_tarski(A_106,k2_zfmisc_1(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_12,c_324])).

tff(c_477,plain,(
    ! [A_13] :
      ( k1_relset_1(k1_relat_1(A_13),k2_relat_1(A_13),A_13) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_463])).

tff(c_429,plain,(
    ! [B_97,C_98,A_99] :
      ( k1_xboole_0 = B_97
      | v1_funct_2(C_98,A_99,B_97)
      | k1_relset_1(A_99,B_97,C_98) != A_99
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_697,plain,(
    ! [B_131,A_132,A_133] :
      ( k1_xboole_0 = B_131
      | v1_funct_2(A_132,A_133,B_131)
      | k1_relset_1(A_133,B_131,A_132) != A_133
      | ~ r1_tarski(A_132,k2_zfmisc_1(A_133,B_131)) ) ),
    inference(resolution,[status(thm)],[c_12,c_429])).

tff(c_776,plain,(
    ! [A_140] :
      ( k2_relat_1(A_140) = k1_xboole_0
      | v1_funct_2(A_140,k1_relat_1(A_140),k2_relat_1(A_140))
      | k1_relset_1(k1_relat_1(A_140),k2_relat_1(A_140),A_140) != k1_relat_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_20,c_697])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_95,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_783,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_776,c_95])).

tff(c_801,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_783])).

tff(c_806,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_801])).

tff(c_809,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_806])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_809])).

tff(c_814,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_801])).

tff(c_829,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_20])).

tff(c_839,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4,c_829])).

tff(c_68,plain,(
    ! [A_28] : k2_zfmisc_1(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    ! [A_40] : v4_relat_1(k1_xboole_0,A_40) ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_148,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ v4_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_151,plain,(
    ! [A_40] :
      ( k7_relat_1(k1_xboole_0,A_40) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_146,c_148])).

tff(c_154,plain,(
    ! [A_40] : k7_relat_1(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_151])).

tff(c_271,plain,(
    ! [B_72,A_73] :
      ( k1_relat_1(k7_relat_1(B_72,A_73)) = A_73
      | ~ r1_tarski(A_73,k1_relat_1(B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_278,plain,(
    ! [A_73] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_73)) = A_73
      | ~ r1_tarski(A_73,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_271])).

tff(c_281,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24,c_154,c_278])).

tff(c_855,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_839,c_281])).

tff(c_338,plain,(
    ! [A_77,B_78] : k1_relset_1(A_77,B_78,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_324])).

tff(c_341,plain,(
    ! [A_77,B_78] : k1_relset_1(A_77,B_78,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_338])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_534,plain,(
    ! [C_109,B_110] :
      ( v1_funct_2(C_109,k1_xboole_0,B_110)
      | k1_relset_1(k1_xboole_0,B_110,C_109) != k1_xboole_0
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38])).

tff(c_540,plain,(
    ! [B_110] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_110)
      | k1_relset_1(k1_xboole_0,B_110,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_534])).

tff(c_544,plain,(
    ! [B_110] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_540])).

tff(c_874,plain,(
    ! [B_110] : v1_funct_2('#skF_1','#skF_1',B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_855,c_544])).

tff(c_904,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_855,c_24])).

tff(c_816,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_95])).

tff(c_857,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_816])).

tff(c_967,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_857])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_967])).

tff(c_1004,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1020,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1013,c_1004])).

tff(c_1083,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1080,c_1020])).

tff(c_1093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1083])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.57  
% 2.97/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.97/1.57  
% 2.97/1.57  %Foreground sorts:
% 2.97/1.57  
% 2.97/1.57  
% 2.97/1.57  %Background operators:
% 2.97/1.57  
% 2.97/1.57  
% 2.97/1.57  %Foreground operators:
% 2.97/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.97/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.97/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.97/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.97/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.97/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.57  
% 2.97/1.59  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.97/1.59  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.97/1.59  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.97/1.59  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.97/1.59  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.97/1.59  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.97/1.59  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.97/1.59  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.97/1.59  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.97/1.59  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.97/1.59  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.97/1.59  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.97/1.59  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.97/1.59  tff(c_1080, plain, (![A_164]: (r1_tarski(A_164, k2_zfmisc_1(k1_relat_1(A_164), k2_relat_1(A_164))) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.59  tff(c_1013, plain, (![A_148, B_149]: (m1_subset_1(A_148, k1_zfmisc_1(B_149)) | ~r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.59  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.59  tff(c_20, plain, (![A_13]: (r1_tarski(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.59  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.59  tff(c_324, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.97/1.59  tff(c_463, plain, (![A_104, B_105, A_106]: (k1_relset_1(A_104, B_105, A_106)=k1_relat_1(A_106) | ~r1_tarski(A_106, k2_zfmisc_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_12, c_324])).
% 2.97/1.59  tff(c_477, plain, (![A_13]: (k1_relset_1(k1_relat_1(A_13), k2_relat_1(A_13), A_13)=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_20, c_463])).
% 2.97/1.59  tff(c_429, plain, (![B_97, C_98, A_99]: (k1_xboole_0=B_97 | v1_funct_2(C_98, A_99, B_97) | k1_relset_1(A_99, B_97, C_98)!=A_99 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_97))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.97/1.59  tff(c_697, plain, (![B_131, A_132, A_133]: (k1_xboole_0=B_131 | v1_funct_2(A_132, A_133, B_131) | k1_relset_1(A_133, B_131, A_132)!=A_133 | ~r1_tarski(A_132, k2_zfmisc_1(A_133, B_131)))), inference(resolution, [status(thm)], [c_12, c_429])).
% 2.97/1.59  tff(c_776, plain, (![A_140]: (k2_relat_1(A_140)=k1_xboole_0 | v1_funct_2(A_140, k1_relat_1(A_140), k2_relat_1(A_140)) | k1_relset_1(k1_relat_1(A_140), k2_relat_1(A_140), A_140)!=k1_relat_1(A_140) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_20, c_697])).
% 2.97/1.59  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.97/1.59  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.97/1.59  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 2.97/1.59  tff(c_95, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.97/1.59  tff(c_783, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_776, c_95])).
% 2.97/1.59  tff(c_801, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_783])).
% 2.97/1.59  tff(c_806, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_801])).
% 2.97/1.59  tff(c_809, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_477, c_806])).
% 2.97/1.59  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_809])).
% 2.97/1.59  tff(c_814, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_801])).
% 2.97/1.59  tff(c_829, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_814, c_20])).
% 2.97/1.59  tff(c_839, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4, c_829])).
% 2.97/1.59  tff(c_68, plain, (![A_28]: (k2_zfmisc_1(A_28, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.59  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.97/1.59  tff(c_72, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_16])).
% 2.97/1.59  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.97/1.59  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.59  tff(c_130, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.97/1.59  tff(c_146, plain, (![A_40]: (v4_relat_1(k1_xboole_0, A_40))), inference(resolution, [status(thm)], [c_8, c_130])).
% 2.97/1.59  tff(c_148, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~v4_relat_1(B_43, A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.97/1.59  tff(c_151, plain, (![A_40]: (k7_relat_1(k1_xboole_0, A_40)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_146, c_148])).
% 2.97/1.59  tff(c_154, plain, (![A_40]: (k7_relat_1(k1_xboole_0, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_151])).
% 2.97/1.59  tff(c_271, plain, (![B_72, A_73]: (k1_relat_1(k7_relat_1(B_72, A_73))=A_73 | ~r1_tarski(A_73, k1_relat_1(B_72)) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.97/1.59  tff(c_278, plain, (![A_73]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_73))=A_73 | ~r1_tarski(A_73, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_271])).
% 2.97/1.59  tff(c_281, plain, (![A_73]: (k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_24, c_154, c_278])).
% 2.97/1.59  tff(c_855, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_839, c_281])).
% 2.97/1.59  tff(c_338, plain, (![A_77, B_78]: (k1_relset_1(A_77, B_78, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_324])).
% 2.97/1.59  tff(c_341, plain, (![A_77, B_78]: (k1_relset_1(A_77, B_78, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_338])).
% 2.97/1.59  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.59  tff(c_38, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.97/1.59  tff(c_534, plain, (![C_109, B_110]: (v1_funct_2(C_109, k1_xboole_0, B_110) | k1_relset_1(k1_xboole_0, B_110, C_109)!=k1_xboole_0 | ~m1_subset_1(C_109, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_38])).
% 2.97/1.59  tff(c_540, plain, (![B_110]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_110) | k1_relset_1(k1_xboole_0, B_110, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_534])).
% 2.97/1.59  tff(c_544, plain, (![B_110]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_540])).
% 2.97/1.59  tff(c_874, plain, (![B_110]: (v1_funct_2('#skF_1', '#skF_1', B_110))), inference(demodulation, [status(thm), theory('equality')], [c_855, c_855, c_544])).
% 2.97/1.59  tff(c_904, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_855, c_855, c_24])).
% 2.97/1.59  tff(c_816, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_814, c_95])).
% 2.97/1.59  tff(c_857, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_855, c_816])).
% 2.97/1.59  tff(c_967, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_904, c_857])).
% 2.97/1.59  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_874, c_967])).
% 2.97/1.59  tff(c_1004, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 2.97/1.59  tff(c_1020, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_1013, c_1004])).
% 2.97/1.59  tff(c_1083, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1080, c_1020])).
% 2.97/1.59  tff(c_1093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1083])).
% 2.97/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.59  
% 2.97/1.59  Inference rules
% 2.97/1.59  ----------------------
% 2.97/1.59  #Ref     : 0
% 2.97/1.59  #Sup     : 203
% 2.97/1.59  #Fact    : 0
% 2.97/1.59  #Define  : 0
% 2.97/1.59  #Split   : 2
% 2.97/1.59  #Chain   : 0
% 2.97/1.59  #Close   : 0
% 2.97/1.59  
% 2.97/1.59  Ordering : KBO
% 2.97/1.59  
% 2.97/1.59  Simplification rules
% 2.97/1.59  ----------------------
% 2.97/1.59  #Subsume      : 20
% 2.97/1.59  #Demod        : 285
% 2.97/1.59  #Tautology    : 106
% 2.97/1.59  #SimpNegUnit  : 0
% 2.97/1.59  #BackRed      : 52
% 2.97/1.59  
% 2.97/1.59  #Partial instantiations: 0
% 2.97/1.59  #Strategies tried      : 1
% 2.97/1.59  
% 2.97/1.59  Timing (in seconds)
% 2.97/1.59  ----------------------
% 2.97/1.59  Preprocessing        : 0.33
% 2.97/1.59  Parsing              : 0.18
% 2.97/1.59  CNF conversion       : 0.02
% 2.97/1.59  Main loop            : 0.38
% 2.97/1.59  Inferencing          : 0.14
% 2.97/1.59  Reduction            : 0.12
% 2.97/1.59  Demodulation         : 0.09
% 2.97/1.59  BG Simplification    : 0.02
% 2.97/1.59  Subsumption          : 0.07
% 2.97/1.59  Abstraction          : 0.02
% 2.97/1.59  MUC search           : 0.00
% 2.97/1.59  Cooper               : 0.00
% 2.97/1.59  Total                : 0.74
% 2.97/1.59  Index Insertion      : 0.00
% 2.97/1.59  Index Deletion       : 0.00
% 2.97/1.59  Index Matching       : 0.00
% 2.97/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
