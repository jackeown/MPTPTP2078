%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:35 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 226 expanded)
%              Number of leaves         :   41 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 455 expanded)
%              Number of equality atoms :   79 ( 218 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_126,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_134,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_126])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_143,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_134,c_28])).

tff(c_158,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_215,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_223,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_215])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_233,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_56])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_172,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_180,plain,(
    v4_relat_1('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_172])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_191,plain,
    ( k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_22])).

tff(c_194,plain,(
    k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_191])).

tff(c_267,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_83,k1_tarski(A_84))),k1_tarski(k1_funct_1(B_83,A_84)))
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_270,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),k1_tarski(k1_funct_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_267])).

tff(c_276,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_tarski(k1_funct_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_64,c_270])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_343,plain,(
    ! [B_93,C_94,A_95] :
      ( k2_tarski(B_93,C_94) = A_95
      | k1_tarski(C_94) = A_95
      | k1_tarski(B_93) = A_95
      | k1_xboole_0 = A_95
      | ~ r1_tarski(A_95,k2_tarski(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_358,plain,(
    ! [A_2,A_95] :
      ( k2_tarski(A_2,A_2) = A_95
      | k1_tarski(A_2) = A_95
      | k1_tarski(A_2) = A_95
      | k1_xboole_0 = A_95
      | ~ r1_tarski(A_95,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_343])).

tff(c_502,plain,(
    ! [A_108,A_109] :
      ( k1_tarski(A_108) = A_109
      | k1_tarski(A_108) = A_109
      | k1_tarski(A_108) = A_109
      | k1_xboole_0 = A_109
      | ~ r1_tarski(A_109,k1_tarski(A_108)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_358])).

tff(c_511,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_276,c_502])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_233,c_233,c_233,c_511])).

tff(c_527,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [A_38,B_39] : k2_xboole_0(k1_tarski(A_38),B_39) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [A_38] : k1_tarski(A_38) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_572,plain,(
    ! [A_38] : k1_tarski(A_38) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_102])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_580,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_58])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_541,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_527,c_26])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_142,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_134,c_30])).

tff(c_529,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_527,c_529])).

tff(c_567,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_587,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_567])).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_576,plain,(
    ! [A_8] : m1_subset_1('#skF_3',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_18])).

tff(c_687,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_691,plain,(
    ! [A_141,B_142] : k1_relset_1(A_141,B_142,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_576,c_687])).

tff(c_693,plain,(
    ! [A_141,B_142] : k1_relset_1(A_141,B_142,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_691])).

tff(c_54,plain,(
    ! [B_30,A_29,C_31] :
      ( k1_xboole_0 = B_30
      | k1_relset_1(A_29,B_30,C_31) = A_29
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_751,plain,(
    ! [B_160,A_161,C_162] :
      ( B_160 = '#skF_3'
      | k1_relset_1(A_161,B_160,C_162) = A_161
      | ~ v1_funct_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_54])).

tff(c_755,plain,(
    ! [B_160,A_161] :
      ( B_160 = '#skF_3'
      | k1_relset_1(A_161,B_160,'#skF_3') = A_161
      | ~ v1_funct_2('#skF_3',A_161,B_160) ) ),
    inference(resolution,[status(thm)],[c_576,c_751])).

tff(c_758,plain,(
    ! [B_163,A_164] :
      ( B_163 = '#skF_3'
      | A_164 = '#skF_3'
      | ~ v1_funct_2('#skF_3',A_164,B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_755])).

tff(c_767,plain,
    ( '#skF_2' = '#skF_3'
    | k1_tarski('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_758])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_572,c_580,c_767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n004.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:53:23 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  
% 3.36/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.55  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.36/1.55  
% 3.36/1.55  %Foreground sorts:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Background operators:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Foreground operators:
% 3.36/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.36/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.36/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.36/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.36/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.36/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.36/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.55  
% 3.36/1.57  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.36/1.57  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.36/1.57  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.36/1.57  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.36/1.57  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.36/1.57  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.36/1.57  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 3.36/1.57  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.36/1.57  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.36/1.57  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.36/1.57  tff(f_47, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.36/1.57  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.36/1.57  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.36/1.57  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.36/1.57  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.36/1.57  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.36/1.57  tff(c_126, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.36/1.57  tff(c_134, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_126])).
% 3.36/1.57  tff(c_28, plain, (![A_14]: (k2_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.57  tff(c_143, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_134, c_28])).
% 3.36/1.57  tff(c_158, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_143])).
% 3.36/1.57  tff(c_215, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.57  tff(c_223, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_215])).
% 3.36/1.57  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.36/1.57  tff(c_233, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_56])).
% 3.36/1.57  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.36/1.57  tff(c_172, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.36/1.57  tff(c_180, plain, (v4_relat_1('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_172])).
% 3.36/1.57  tff(c_22, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.57  tff(c_191, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_22])).
% 3.36/1.57  tff(c_194, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_191])).
% 3.36/1.57  tff(c_267, plain, (![B_83, A_84]: (r1_tarski(k2_relat_1(k7_relat_1(B_83, k1_tarski(A_84))), k1_tarski(k1_funct_1(B_83, A_84))) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.57  tff(c_270, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_tarski(k1_funct_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_194, c_267])).
% 3.36/1.57  tff(c_276, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_tarski(k1_funct_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_64, c_270])).
% 3.36/1.57  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.57  tff(c_343, plain, (![B_93, C_94, A_95]: (k2_tarski(B_93, C_94)=A_95 | k1_tarski(C_94)=A_95 | k1_tarski(B_93)=A_95 | k1_xboole_0=A_95 | ~r1_tarski(A_95, k2_tarski(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.36/1.57  tff(c_358, plain, (![A_2, A_95]: (k2_tarski(A_2, A_2)=A_95 | k1_tarski(A_2)=A_95 | k1_tarski(A_2)=A_95 | k1_xboole_0=A_95 | ~r1_tarski(A_95, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_343])).
% 3.36/1.57  tff(c_502, plain, (![A_108, A_109]: (k1_tarski(A_108)=A_109 | k1_tarski(A_108)=A_109 | k1_tarski(A_108)=A_109 | k1_xboole_0=A_109 | ~r1_tarski(A_109, k1_tarski(A_108)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_358])).
% 3.36/1.57  tff(c_511, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_276, c_502])).
% 3.36/1.57  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_233, c_233, c_233, c_511])).
% 3.36/1.57  tff(c_527, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_143])).
% 3.36/1.57  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.57  tff(c_98, plain, (![A_38, B_39]: (k2_xboole_0(k1_tarski(A_38), B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.57  tff(c_102, plain, (![A_38]: (k1_tarski(A_38)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 3.36/1.57  tff(c_572, plain, (![A_38]: (k1_tarski(A_38)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_102])).
% 3.36/1.57  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.36/1.57  tff(c_580, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_58])).
% 3.36/1.57  tff(c_62, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.36/1.57  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.57  tff(c_541, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_527, c_26])).
% 3.36/1.57  tff(c_30, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.57  tff(c_142, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_134, c_30])).
% 3.36/1.57  tff(c_529, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_142])).
% 3.36/1.57  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_541, c_527, c_529])).
% 3.36/1.57  tff(c_567, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_142])).
% 3.36/1.57  tff(c_587, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_567])).
% 3.36/1.57  tff(c_18, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.57  tff(c_576, plain, (![A_8]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_18])).
% 3.36/1.57  tff(c_687, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.36/1.57  tff(c_691, plain, (![A_141, B_142]: (k1_relset_1(A_141, B_142, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_576, c_687])).
% 3.36/1.57  tff(c_693, plain, (![A_141, B_142]: (k1_relset_1(A_141, B_142, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_587, c_691])).
% 3.36/1.57  tff(c_54, plain, (![B_30, A_29, C_31]: (k1_xboole_0=B_30 | k1_relset_1(A_29, B_30, C_31)=A_29 | ~v1_funct_2(C_31, A_29, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.36/1.57  tff(c_751, plain, (![B_160, A_161, C_162]: (B_160='#skF_3' | k1_relset_1(A_161, B_160, C_162)=A_161 | ~v1_funct_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_54])).
% 3.36/1.57  tff(c_755, plain, (![B_160, A_161]: (B_160='#skF_3' | k1_relset_1(A_161, B_160, '#skF_3')=A_161 | ~v1_funct_2('#skF_3', A_161, B_160))), inference(resolution, [status(thm)], [c_576, c_751])).
% 3.36/1.57  tff(c_758, plain, (![B_163, A_164]: (B_163='#skF_3' | A_164='#skF_3' | ~v1_funct_2('#skF_3', A_164, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_755])).
% 3.36/1.57  tff(c_767, plain, ('#skF_2'='#skF_3' | k1_tarski('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_62, c_758])).
% 3.36/1.57  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_572, c_580, c_767])).
% 3.36/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  Inference rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Ref     : 0
% 3.36/1.57  #Sup     : 140
% 3.36/1.57  #Fact    : 0
% 3.36/1.57  #Define  : 0
% 3.36/1.57  #Split   : 3
% 3.36/1.57  #Chain   : 0
% 3.36/1.57  #Close   : 0
% 3.36/1.57  
% 3.36/1.57  Ordering : KBO
% 3.36/1.57  
% 3.36/1.57  Simplification rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Subsume      : 5
% 3.36/1.57  #Demod        : 141
% 3.36/1.57  #Tautology    : 96
% 3.36/1.57  #SimpNegUnit  : 10
% 3.36/1.57  #BackRed      : 35
% 3.36/1.57  
% 3.36/1.57  #Partial instantiations: 0
% 3.36/1.57  #Strategies tried      : 1
% 3.36/1.57  
% 3.36/1.57  Timing (in seconds)
% 3.36/1.57  ----------------------
% 3.36/1.57  Preprocessing        : 0.40
% 3.36/1.57  Parsing              : 0.20
% 3.36/1.57  CNF conversion       : 0.03
% 3.36/1.57  Main loop            : 0.36
% 3.36/1.57  Inferencing          : 0.13
% 3.36/1.57  Reduction            : 0.12
% 3.36/1.57  Demodulation         : 0.09
% 3.36/1.57  BG Simplification    : 0.02
% 3.36/1.57  Subsumption          : 0.06
% 3.36/1.57  Abstraction          : 0.02
% 3.36/1.57  MUC search           : 0.00
% 3.36/1.57  Cooper               : 0.00
% 3.36/1.57  Total                : 0.80
% 3.36/1.57  Index Insertion      : 0.00
% 3.36/1.57  Index Deletion       : 0.00
% 3.36/1.57  Index Matching       : 0.00
% 3.36/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
