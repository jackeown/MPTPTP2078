%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:44 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 836 expanded)
%              Number of leaves         :   27 ( 291 expanded)
%              Depth                    :   13
%              Number of atoms          :  178 (2002 expanded)
%              Number of equality atoms :   61 ( 610 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_216,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_417,plain,(
    ! [A_94,B_95,A_96] :
      ( k1_relset_1(A_94,B_95,A_96) = k1_relat_1(A_96)
      | ~ r1_tarski(A_96,k2_zfmisc_1(A_94,B_95)) ) ),
    inference(resolution,[status(thm)],[c_18,c_216])).

tff(c_435,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_24,c_417])).

tff(c_357,plain,(
    ! [B_84,C_85,A_86] :
      ( k1_xboole_0 = B_84
      | v1_funct_2(C_85,A_86,B_84)
      | k1_relset_1(A_86,B_84,C_85) != A_86
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1243,plain,(
    ! [B_196,A_197,A_198] :
      ( k1_xboole_0 = B_196
      | v1_funct_2(A_197,A_198,B_196)
      | k1_relset_1(A_198,B_196,A_197) != A_198
      | ~ r1_tarski(A_197,k2_zfmisc_1(A_198,B_196)) ) ),
    inference(resolution,[status(thm)],[c_18,c_357])).

tff(c_1660,plain,(
    ! [A_228] :
      ( k2_relat_1(A_228) = k1_xboole_0
      | v1_funct_2(A_228,k1_relat_1(A_228),k2_relat_1(A_228))
      | k1_relset_1(k1_relat_1(A_228),k2_relat_1(A_228),A_228) != k1_relat_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(resolution,[status(thm)],[c_24,c_1243])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_101,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1665,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1660,c_101])).

tff(c_1671,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1665])).

tff(c_1672,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1671])).

tff(c_1678,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_1672])).

tff(c_1685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1678])).

tff(c_1686,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1671])).

tff(c_1729,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_24])).

tff(c_1761,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12,c_1729])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1786,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1761,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_234,plain,(
    ! [A_68,A_69,B_70] :
      ( v4_relat_1(A_68,A_69)
      | ~ r1_tarski(A_68,k2_zfmisc_1(A_69,B_70)) ) ),
    inference(resolution,[status(thm)],[c_18,c_199])).

tff(c_255,plain,(
    ! [A_71,B_72] : v4_relat_1(k2_zfmisc_1(A_71,B_72),A_71) ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_132,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(k1_relat_1(B_40),A_41)
      | ~ v4_relat_1(B_40,A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_140,plain,(
    ! [B_40] :
      ( k1_relat_1(B_40) = k1_xboole_0
      | ~ v4_relat_1(B_40,k1_xboole_0)
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_259,plain,(
    ! [B_72] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_72)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_72)) ) ),
    inference(resolution,[status(thm)],[c_255,c_140])).

tff(c_267,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_259])).

tff(c_322,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_1848,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_322])).

tff(c_1864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1848])).

tff(c_1866,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_262,plain,(
    ! [A_4] : v4_relat_1(k1_xboole_0,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_255])).

tff(c_1865,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_22,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1879,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | ~ v4_relat_1(k1_xboole_0,A_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1865,c_22])).

tff(c_1889,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_262,c_1879])).

tff(c_2030,plain,(
    ! [A_247,B_248,A_249] :
      ( k1_relset_1(A_247,B_248,A_249) = k1_relat_1(A_249)
      | ~ r1_tarski(A_249,k2_zfmisc_1(A_247,B_248)) ) ),
    inference(resolution,[status(thm)],[c_18,c_216])).

tff(c_2054,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_24,c_2030])).

tff(c_1936,plain,(
    ! [B_232,C_233,A_234] :
      ( k1_xboole_0 = B_232
      | v1_funct_2(C_233,A_234,B_232)
      | k1_relset_1(A_234,B_232,C_233) != A_234
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3043,plain,(
    ! [B_350,A_351,A_352] :
      ( k1_xboole_0 = B_350
      | v1_funct_2(A_351,A_352,B_350)
      | k1_relset_1(A_352,B_350,A_351) != A_352
      | ~ r1_tarski(A_351,k2_zfmisc_1(A_352,B_350)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1936])).

tff(c_3702,plain,(
    ! [A_392] :
      ( k2_relat_1(A_392) = k1_xboole_0
      | v1_funct_2(A_392,k1_relat_1(A_392),k2_relat_1(A_392))
      | k1_relset_1(k1_relat_1(A_392),k2_relat_1(A_392),A_392) != k1_relat_1(A_392)
      | ~ v1_relat_1(A_392) ) ),
    inference(resolution,[status(thm)],[c_24,c_3043])).

tff(c_3711,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3702,c_101])).

tff(c_3723,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3711])).

tff(c_3726,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3723])).

tff(c_3732,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2054,c_3726])).

tff(c_3739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3732])).

tff(c_3740,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3723])).

tff(c_185,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,k2_zfmisc_1(k1_relat_1(A_56),k2_relat_1(A_56)))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_197,plain,(
    ! [A_56] :
      ( k2_zfmisc_1(k1_relat_1(A_56),k2_relat_1(A_56)) = A_56
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_56),k2_relat_1(A_56)),A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_3765,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3740,c_197])).

tff(c_3804,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1889,c_12,c_12,c_3740,c_3765])).

tff(c_2034,plain,(
    ! [A_247,B_248] : k1_relset_1(A_247,B_248,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1889,c_2030])).

tff(c_2053,plain,(
    ! [A_247,B_248] : k1_relset_1(A_247,B_248,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_2034])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_274,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_278,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_274])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_278])).

tff(c_284,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_38,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2175,plain,(
    ! [C_265,B_266] :
      ( v1_funct_2(C_265,k1_xboole_0,B_266)
      | k1_relset_1(k1_xboole_0,B_266,C_265) != k1_xboole_0
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_2177,plain,(
    ! [B_266] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_266)
      | k1_relset_1(k1_xboole_0,B_266,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_284,c_2175])).

tff(c_2183,plain,(
    ! [B_266] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_2177])).

tff(c_3871,plain,(
    ! [B_266] : v1_funct_2('#skF_1','#skF_1',B_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3804,c_3804,c_2183])).

tff(c_3886,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3804,c_3804,c_1865])).

tff(c_3742,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3740,c_101])).

tff(c_3822,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3804,c_3742])).

tff(c_4029,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_3822])).

tff(c_4321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3871,c_4029])).

tff(c_4322,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4338,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_4322])).

tff(c_4345,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4338])).

tff(c_4349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:16:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.12  
% 5.80/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.12  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.80/2.12  
% 5.80/2.12  %Foreground sorts:
% 5.80/2.12  
% 5.80/2.12  
% 5.80/2.12  %Background operators:
% 5.80/2.12  
% 5.80/2.12  
% 5.80/2.12  %Foreground operators:
% 5.80/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.80/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.80/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.80/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.80/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.80/2.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.80/2.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.80/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.80/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.80/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.80/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.80/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.12  
% 5.80/2.14  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.80/2.14  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 5.80/2.14  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.80/2.14  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.80/2.14  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.80/2.14  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.80/2.14  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.80/2.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.80/2.14  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.80/2.14  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.80/2.14  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.80/2.14  tff(c_24, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.80/2.14  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.80/2.14  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.80/2.14  tff(c_216, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.80/2.14  tff(c_417, plain, (![A_94, B_95, A_96]: (k1_relset_1(A_94, B_95, A_96)=k1_relat_1(A_96) | ~r1_tarski(A_96, k2_zfmisc_1(A_94, B_95)))), inference(resolution, [status(thm)], [c_18, c_216])).
% 5.80/2.14  tff(c_435, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_24, c_417])).
% 5.80/2.14  tff(c_357, plain, (![B_84, C_85, A_86]: (k1_xboole_0=B_84 | v1_funct_2(C_85, A_86, B_84) | k1_relset_1(A_86, B_84, C_85)!=A_86 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_84))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.80/2.14  tff(c_1243, plain, (![B_196, A_197, A_198]: (k1_xboole_0=B_196 | v1_funct_2(A_197, A_198, B_196) | k1_relset_1(A_198, B_196, A_197)!=A_198 | ~r1_tarski(A_197, k2_zfmisc_1(A_198, B_196)))), inference(resolution, [status(thm)], [c_18, c_357])).
% 5.80/2.14  tff(c_1660, plain, (![A_228]: (k2_relat_1(A_228)=k1_xboole_0 | v1_funct_2(A_228, k1_relat_1(A_228), k2_relat_1(A_228)) | k1_relset_1(k1_relat_1(A_228), k2_relat_1(A_228), A_228)!=k1_relat_1(A_228) | ~v1_relat_1(A_228))), inference(resolution, [status(thm)], [c_24, c_1243])).
% 5.80/2.14  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.80/2.14  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.80/2.14  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 5.80/2.14  tff(c_101, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 5.80/2.14  tff(c_1665, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1660, c_101])).
% 5.80/2.14  tff(c_1671, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1665])).
% 5.80/2.14  tff(c_1672, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1671])).
% 5.80/2.14  tff(c_1678, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_435, c_1672])).
% 5.80/2.14  tff(c_1685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1678])).
% 5.80/2.14  tff(c_1686, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1671])).
% 5.80/2.14  tff(c_1729, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1686, c_24])).
% 5.80/2.14  tff(c_1761, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12, c_1729])).
% 5.80/2.14  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.14  tff(c_1786, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1761, c_8])).
% 5.80/2.14  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.80/2.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.14  tff(c_199, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.80/2.14  tff(c_234, plain, (![A_68, A_69, B_70]: (v4_relat_1(A_68, A_69) | ~r1_tarski(A_68, k2_zfmisc_1(A_69, B_70)))), inference(resolution, [status(thm)], [c_18, c_199])).
% 5.80/2.14  tff(c_255, plain, (![A_71, B_72]: (v4_relat_1(k2_zfmisc_1(A_71, B_72), A_71))), inference(resolution, [status(thm)], [c_6, c_234])).
% 5.80/2.14  tff(c_132, plain, (![B_40, A_41]: (r1_tarski(k1_relat_1(B_40), A_41) | ~v4_relat_1(B_40, A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.14  tff(c_140, plain, (![B_40]: (k1_relat_1(B_40)=k1_xboole_0 | ~v4_relat_1(B_40, k1_xboole_0) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_132, c_8])).
% 5.80/2.14  tff(c_259, plain, (![B_72]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_72))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_72)))), inference(resolution, [status(thm)], [c_255, c_140])).
% 5.80/2.14  tff(c_267, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_259])).
% 5.80/2.14  tff(c_322, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_267])).
% 5.80/2.14  tff(c_1848, plain, (~v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_322])).
% 5.80/2.14  tff(c_1864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1848])).
% 5.80/2.14  tff(c_1866, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_267])).
% 5.80/2.14  tff(c_262, plain, (![A_4]: (v4_relat_1(k1_xboole_0, A_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_255])).
% 5.80/2.14  tff(c_1865, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_267])).
% 5.80/2.14  tff(c_22, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.14  tff(c_1879, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | ~v4_relat_1(k1_xboole_0, A_8) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1865, c_22])).
% 5.80/2.14  tff(c_1889, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_262, c_1879])).
% 5.80/2.14  tff(c_2030, plain, (![A_247, B_248, A_249]: (k1_relset_1(A_247, B_248, A_249)=k1_relat_1(A_249) | ~r1_tarski(A_249, k2_zfmisc_1(A_247, B_248)))), inference(resolution, [status(thm)], [c_18, c_216])).
% 5.80/2.14  tff(c_2054, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_24, c_2030])).
% 5.80/2.14  tff(c_1936, plain, (![B_232, C_233, A_234]: (k1_xboole_0=B_232 | v1_funct_2(C_233, A_234, B_232) | k1_relset_1(A_234, B_232, C_233)!=A_234 | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_232))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.80/2.14  tff(c_3043, plain, (![B_350, A_351, A_352]: (k1_xboole_0=B_350 | v1_funct_2(A_351, A_352, B_350) | k1_relset_1(A_352, B_350, A_351)!=A_352 | ~r1_tarski(A_351, k2_zfmisc_1(A_352, B_350)))), inference(resolution, [status(thm)], [c_18, c_1936])).
% 5.80/2.14  tff(c_3702, plain, (![A_392]: (k2_relat_1(A_392)=k1_xboole_0 | v1_funct_2(A_392, k1_relat_1(A_392), k2_relat_1(A_392)) | k1_relset_1(k1_relat_1(A_392), k2_relat_1(A_392), A_392)!=k1_relat_1(A_392) | ~v1_relat_1(A_392))), inference(resolution, [status(thm)], [c_24, c_3043])).
% 5.80/2.14  tff(c_3711, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3702, c_101])).
% 5.80/2.14  tff(c_3723, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3711])).
% 5.80/2.14  tff(c_3726, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3723])).
% 5.80/2.14  tff(c_3732, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2054, c_3726])).
% 5.80/2.14  tff(c_3739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3732])).
% 5.80/2.14  tff(c_3740, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3723])).
% 5.80/2.14  tff(c_185, plain, (![A_56]: (r1_tarski(A_56, k2_zfmisc_1(k1_relat_1(A_56), k2_relat_1(A_56))) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.80/2.14  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.14  tff(c_197, plain, (![A_56]: (k2_zfmisc_1(k1_relat_1(A_56), k2_relat_1(A_56))=A_56 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_56), k2_relat_1(A_56)), A_56) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_185, c_2])).
% 5.80/2.14  tff(c_3765, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3740, c_197])).
% 5.80/2.14  tff(c_3804, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1889, c_12, c_12, c_3740, c_3765])).
% 5.80/2.14  tff(c_2034, plain, (![A_247, B_248]: (k1_relset_1(A_247, B_248, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1889, c_2030])).
% 5.80/2.14  tff(c_2053, plain, (![A_247, B_248]: (k1_relset_1(A_247, B_248, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_2034])).
% 5.80/2.14  tff(c_34, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.80/2.14  tff(c_55, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 5.80/2.14  tff(c_274, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_55])).
% 5.80/2.14  tff(c_278, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_274])).
% 5.80/2.14  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_278])).
% 5.80/2.14  tff(c_284, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_55])).
% 5.80/2.14  tff(c_38, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.80/2.14  tff(c_2175, plain, (![C_265, B_266]: (v1_funct_2(C_265, k1_xboole_0, B_266) | k1_relset_1(k1_xboole_0, B_266, C_265)!=k1_xboole_0 | ~m1_subset_1(C_265, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 5.80/2.14  tff(c_2177, plain, (![B_266]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_266) | k1_relset_1(k1_xboole_0, B_266, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_284, c_2175])).
% 5.80/2.14  tff(c_2183, plain, (![B_266]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_266))), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_2177])).
% 5.80/2.14  tff(c_3871, plain, (![B_266]: (v1_funct_2('#skF_1', '#skF_1', B_266))), inference(demodulation, [status(thm), theory('equality')], [c_3804, c_3804, c_2183])).
% 5.80/2.14  tff(c_3886, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3804, c_3804, c_1865])).
% 5.80/2.14  tff(c_3742, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3740, c_101])).
% 5.80/2.14  tff(c_3822, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3804, c_3742])).
% 5.80/2.14  tff(c_4029, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3886, c_3822])).
% 5.80/2.14  tff(c_4321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3871, c_4029])).
% 5.80/2.14  tff(c_4322, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 5.80/2.14  tff(c_4338, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_4322])).
% 5.80/2.14  tff(c_4345, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4338])).
% 5.80/2.14  tff(c_4349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_4345])).
% 5.80/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.14  
% 5.80/2.14  Inference rules
% 5.80/2.14  ----------------------
% 5.80/2.14  #Ref     : 0
% 5.80/2.14  #Sup     : 888
% 5.80/2.14  #Fact    : 0
% 5.80/2.14  #Define  : 0
% 5.80/2.14  #Split   : 6
% 5.80/2.14  #Chain   : 0
% 5.80/2.14  #Close   : 0
% 5.80/2.14  
% 5.80/2.14  Ordering : KBO
% 5.80/2.14  
% 5.80/2.14  Simplification rules
% 5.80/2.14  ----------------------
% 5.80/2.14  #Subsume      : 235
% 5.80/2.14  #Demod        : 1206
% 5.80/2.14  #Tautology    : 309
% 5.80/2.14  #SimpNegUnit  : 7
% 5.80/2.14  #BackRed      : 156
% 5.80/2.14  
% 5.80/2.14  #Partial instantiations: 0
% 5.80/2.14  #Strategies tried      : 1
% 5.80/2.14  
% 5.80/2.14  Timing (in seconds)
% 5.80/2.14  ----------------------
% 5.80/2.14  Preprocessing        : 0.33
% 5.80/2.14  Parsing              : 0.17
% 5.80/2.14  CNF conversion       : 0.02
% 5.80/2.14  Main loop            : 1.02
% 5.80/2.14  Inferencing          : 0.36
% 5.80/2.14  Reduction            : 0.30
% 5.80/2.14  Demodulation         : 0.21
% 5.80/2.15  BG Simplification    : 0.04
% 5.80/2.15  Subsumption          : 0.24
% 5.80/2.15  Abstraction          : 0.05
% 5.80/2.15  MUC search           : 0.00
% 5.80/2.15  Cooper               : 0.00
% 5.80/2.15  Total                : 1.39
% 5.80/2.15  Index Insertion      : 0.00
% 5.80/2.15  Index Deletion       : 0.00
% 5.80/2.15  Index Matching       : 0.00
% 5.80/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
