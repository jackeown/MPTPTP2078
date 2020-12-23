%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:43 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 877 expanded)
%              Number of leaves         :   35 ( 296 expanded)
%              Depth                    :   11
%              Number of atoms          :  308 (2409 expanded)
%              Number of equality atoms :   82 ( 453 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1477,plain,(
    ! [C_165,B_166,A_167] :
      ( v1_xboole_0(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(B_166,A_167)))
      | ~ v1_xboole_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1491,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1477])).

tff(c_1496,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1491])).

tff(c_129,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_129])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_20,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_146,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_143])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_146])).

tff(c_151,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1555,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1528,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1531,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1528])).

tff(c_1543,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1531])).

tff(c_26,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_152,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1648,plain,(
    ! [A_183,B_184,C_185] :
      ( k1_relset_1(A_183,B_184,C_185) = k1_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1670,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1648])).

tff(c_1797,plain,(
    ! [B_196,A_197,C_198] :
      ( k1_xboole_0 = B_196
      | k1_relset_1(A_197,B_196,C_198) = A_197
      | ~ v1_funct_2(C_198,A_197,B_196)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1806,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1797])).

tff(c_1823,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1670,c_1806])).

tff(c_1827,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1823])).

tff(c_24,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1575,plain,(
    ! [A_180] :
      ( m1_subset_1(A_180,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_180),k2_relat_1(A_180))))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    ! [C_17,B_15,A_14] :
      ( v1_xboole_0(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(B_15,A_14)))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1633,plain,(
    ! [A_181] :
      ( v1_xboole_0(A_181)
      | ~ v1_xboole_0(k2_relat_1(A_181))
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_1575,c_30])).

tff(c_1994,plain,(
    ! [A_213] :
      ( v1_xboole_0(k2_funct_1(A_213))
      | ~ v1_xboole_0(k1_relat_1(A_213))
      | ~ v1_funct_1(k2_funct_1(A_213))
      | ~ v1_relat_1(k2_funct_1(A_213))
      | ~ v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1633])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_105,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_2,c_105])).

tff(c_2002,plain,(
    ! [A_214] :
      ( k2_funct_1(A_214) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_214))
      | ~ v1_funct_1(k2_funct_1(A_214))
      | ~ v1_relat_1(k2_funct_1(A_214))
      | ~ v2_funct_1(A_214)
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(resolution,[status(thm)],[c_1994,c_108])).

tff(c_2005,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1827,c_2002])).

tff(c_2013,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_58,c_152,c_2005])).

tff(c_2033,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2013])).

tff(c_2036,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2033])).

tff(c_2040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_2036])).

tff(c_2042,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2013])).

tff(c_2081,plain,(
    ! [A_219] :
      ( m1_subset_1(k2_funct_1(A_219),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_219)),k1_relat_1(A_219))))
      | ~ v1_funct_1(k2_funct_1(A_219))
      | ~ v1_relat_1(k2_funct_1(A_219))
      | ~ v2_funct_1(A_219)
      | ~ v1_funct_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1575])).

tff(c_2104,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1827,c_2081])).

tff(c_2122,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_58,c_2042,c_152,c_2104])).

tff(c_2147,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2122])).

tff(c_2160,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_58,c_1543,c_2147])).

tff(c_2162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1555,c_2160])).

tff(c_2163,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1823])).

tff(c_2187,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2163,c_2])).

tff(c_2189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1496,c_2187])).

tff(c_2191,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_2211,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2191,c_30])).

tff(c_2214,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2211])).

tff(c_2190,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_2286,plain,(
    ! [A_228,B_229,C_230] :
      ( k1_relset_1(A_228,B_229,C_230) = k1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2311,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2191,c_2286])).

tff(c_2611,plain,(
    ! [B_255,C_256,A_257] :
      ( k1_xboole_0 = B_255
      | v1_funct_2(C_256,A_257,B_255)
      | k1_relset_1(A_257,B_255,C_256) != A_257
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2617,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2191,c_2611])).

tff(c_2633,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2617])).

tff(c_2634,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2190,c_2633])).

tff(c_2641,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2634])).

tff(c_2644,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2641])).

tff(c_2647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_58,c_1543,c_2644])).

tff(c_2648,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2634])).

tff(c_2676,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2648,c_2])).

tff(c_2678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2214,c_2676])).

tff(c_2680,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2211])).

tff(c_2686,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2680,c_108])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2702,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2686,c_2686,c_18])).

tff(c_2679,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2211])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2736,plain,(
    ! [A_260] :
      ( A_260 = '#skF_1'
      | ~ v1_xboole_0(A_260) ) ),
    inference(resolution,[status(thm)],[c_2680,c_4])).

tff(c_2743,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2679,c_2736])).

tff(c_2762,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2743,c_26])).

tff(c_2774,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_58,c_2702,c_1543,c_2762])).

tff(c_2782,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_1496])).

tff(c_2789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2680,c_2782])).

tff(c_2790,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1491])).

tff(c_2809,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2790,c_108])).

tff(c_2830,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2809,c_18])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2826,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_12])).

tff(c_3570,plain,(
    ! [A_333,B_334,C_335] :
      ( k1_relset_1(A_333,B_334,C_335) = k1_relat_1(C_335)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3580,plain,(
    ! [A_333,B_334] : k1_relset_1(A_333,B_334,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2826,c_3570])).

tff(c_3582,plain,(
    ! [A_333,B_334] : k1_relset_1(A_333,B_334,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2830,c_3580])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_3718,plain,(
    ! [C_354,B_355] :
      ( v1_funct_2(C_354,'#skF_3',B_355)
      | k1_relset_1('#skF_3',B_355,C_354) != '#skF_3'
      | ~ m1_subset_1(C_354,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2809,c_2809,c_2809,c_68])).

tff(c_3721,plain,(
    ! [B_355] :
      ( v1_funct_2('#skF_3','#skF_3',B_355)
      | k1_relset_1('#skF_3',B_355,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2826,c_3718])).

tff(c_3724,plain,(
    ! [B_355] : v1_funct_2('#skF_3','#skF_3',B_355) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3582,c_3721])).

tff(c_2827,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2809,c_10])).

tff(c_2791,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1491])).

tff(c_2816,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2791,c_108])).

tff(c_3360,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2816])).

tff(c_2986,plain,(
    ! [A_278] :
      ( m1_subset_1(A_278,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_278),k2_relat_1(A_278))))
      | ~ v1_funct_1(A_278)
      | ~ v1_relat_1(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3029,plain,(
    ! [A_281] :
      ( v1_xboole_0(A_281)
      | ~ v1_xboole_0(k2_relat_1(A_281))
      | ~ v1_funct_1(A_281)
      | ~ v1_relat_1(A_281) ) ),
    inference(resolution,[status(thm)],[c_2986,c_30])).

tff(c_3314,plain,(
    ! [A_316] :
      ( v1_xboole_0(k2_funct_1(A_316))
      | ~ v1_xboole_0(k1_relat_1(A_316))
      | ~ v1_funct_1(k2_funct_1(A_316))
      | ~ v1_relat_1(k2_funct_1(A_316))
      | ~ v2_funct_1(A_316)
      | ~ v1_funct_1(A_316)
      | ~ v1_relat_1(A_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3029])).

tff(c_2825,plain,(
    ! [A_32] :
      ( A_32 = '#skF_3'
      | ~ v1_xboole_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_108])).

tff(c_3322,plain,(
    ! [A_317] :
      ( k2_funct_1(A_317) = '#skF_3'
      | ~ v1_xboole_0(k1_relat_1(A_317))
      | ~ v1_funct_1(k2_funct_1(A_317))
      | ~ v1_relat_1(k2_funct_1(A_317))
      | ~ v2_funct_1(A_317)
      | ~ v1_funct_1(A_317)
      | ~ v1_relat_1(A_317) ) ),
    inference(resolution,[status(thm)],[c_3314,c_2825])).

tff(c_3325,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2830,c_3322])).

tff(c_3330,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_58,c_152,c_2790,c_3325])).

tff(c_3331,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3330])).

tff(c_3334,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_3331])).

tff(c_3338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_64,c_3334])).

tff(c_3339,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3330])).

tff(c_2840,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_2816])).

tff(c_2839,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_2903,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2827,c_2840,c_2839])).

tff(c_3353,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3339,c_2903])).

tff(c_3357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2826,c_3353])).

tff(c_3359,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_3469,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2827,c_3360,c_3359])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1490,plain,(
    ! [C_165] :
      ( v1_xboole_0(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1477])).

tff(c_1495,plain,(
    ! [C_165] :
      ( v1_xboole_0(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1490])).

tff(c_3453,plain,(
    ! [C_165] :
      ( v1_xboole_0(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_1495])).

tff(c_3479,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3469,c_3453])).

tff(c_2817,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2791,c_4])).

tff(c_3389,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3360,c_2817])).

tff(c_3486,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3479,c_3389])).

tff(c_3358,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_3396,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3360,c_3358])).

tff(c_3491,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_3396])).

tff(c_3728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3724,c_3491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/2.05  
% 5.16/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/2.05  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.16/2.05  
% 5.16/2.05  %Foreground sorts:
% 5.16/2.05  
% 5.16/2.05  
% 5.16/2.05  %Background operators:
% 5.16/2.05  
% 5.16/2.05  
% 5.16/2.05  %Foreground operators:
% 5.16/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.16/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.16/2.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.16/2.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.16/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.16/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.16/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.16/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.16/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.16/2.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.16/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.16/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.16/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.16/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.16/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.16/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.16/2.05  
% 5.51/2.07  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.51/2.07  tff(f_80, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.51/2.07  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.51/2.07  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.51/2.07  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.51/2.07  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.51/2.07  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.51/2.07  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.51/2.07  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.51/2.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.51/2.07  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.51/2.07  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.51/2.07  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.51/2.07  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.51/2.07  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.51/2.07  tff(c_1477, plain, (![C_165, B_166, A_167]: (v1_xboole_0(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(B_166, A_167))) | ~v1_xboole_0(A_167))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.51/2.07  tff(c_1491, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1477])).
% 5.51/2.07  tff(c_1496, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1491])).
% 5.51/2.07  tff(c_129, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.51/2.07  tff(c_141, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_129])).
% 5.51/2.07  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.51/2.07  tff(c_20, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.51/2.07  tff(c_54, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.51/2.07  tff(c_143, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.51/2.07  tff(c_146, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_143])).
% 5.51/2.07  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_146])).
% 5.51/2.07  tff(c_151, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 5.51/2.07  tff(c_1555, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_151])).
% 5.51/2.07  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.51/2.07  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.51/2.07  tff(c_1528, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.51/2.07  tff(c_1531, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1528])).
% 5.51/2.07  tff(c_1543, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1531])).
% 5.51/2.07  tff(c_26, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.51/2.07  tff(c_22, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.51/2.07  tff(c_152, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 5.51/2.07  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.51/2.07  tff(c_1648, plain, (![A_183, B_184, C_185]: (k1_relset_1(A_183, B_184, C_185)=k1_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.51/2.07  tff(c_1670, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1648])).
% 5.51/2.07  tff(c_1797, plain, (![B_196, A_197, C_198]: (k1_xboole_0=B_196 | k1_relset_1(A_197, B_196, C_198)=A_197 | ~v1_funct_2(C_198, A_197, B_196) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.51/2.07  tff(c_1806, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1797])).
% 5.51/2.07  tff(c_1823, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1670, c_1806])).
% 5.51/2.07  tff(c_1827, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1823])).
% 5.51/2.07  tff(c_24, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.51/2.07  tff(c_1575, plain, (![A_180]: (m1_subset_1(A_180, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_180), k2_relat_1(A_180)))) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.07  tff(c_30, plain, (![C_17, B_15, A_14]: (v1_xboole_0(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(B_15, A_14))) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.51/2.07  tff(c_1633, plain, (![A_181]: (v1_xboole_0(A_181) | ~v1_xboole_0(k2_relat_1(A_181)) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(resolution, [status(thm)], [c_1575, c_30])).
% 5.51/2.07  tff(c_1994, plain, (![A_213]: (v1_xboole_0(k2_funct_1(A_213)) | ~v1_xboole_0(k1_relat_1(A_213)) | ~v1_funct_1(k2_funct_1(A_213)) | ~v1_relat_1(k2_funct_1(A_213)) | ~v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1633])).
% 5.51/2.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.51/2.07  tff(c_105, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.51/2.07  tff(c_108, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_2, c_105])).
% 5.51/2.07  tff(c_2002, plain, (![A_214]: (k2_funct_1(A_214)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_214)) | ~v1_funct_1(k2_funct_1(A_214)) | ~v1_relat_1(k2_funct_1(A_214)) | ~v2_funct_1(A_214) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(resolution, [status(thm)], [c_1994, c_108])).
% 5.51/2.07  tff(c_2005, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_xboole_0('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1827, c_2002])).
% 5.51/2.07  tff(c_2013, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_xboole_0('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_58, c_152, c_2005])).
% 5.51/2.07  tff(c_2033, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2013])).
% 5.51/2.07  tff(c_2036, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2033])).
% 5.51/2.07  tff(c_2040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_2036])).
% 5.51/2.07  tff(c_2042, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2013])).
% 5.51/2.07  tff(c_2081, plain, (![A_219]: (m1_subset_1(k2_funct_1(A_219), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_219)), k1_relat_1(A_219)))) | ~v1_funct_1(k2_funct_1(A_219)) | ~v1_relat_1(k2_funct_1(A_219)) | ~v2_funct_1(A_219) | ~v1_funct_1(A_219) | ~v1_relat_1(A_219))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1575])).
% 5.51/2.07  tff(c_2104, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1827, c_2081])).
% 5.51/2.07  tff(c_2122, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_58, c_2042, c_152, c_2104])).
% 5.51/2.07  tff(c_2147, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2122])).
% 5.51/2.07  tff(c_2160, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_58, c_1543, c_2147])).
% 5.51/2.07  tff(c_2162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1555, c_2160])).
% 5.51/2.07  tff(c_2163, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1823])).
% 5.51/2.07  tff(c_2187, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2163, c_2])).
% 5.51/2.07  tff(c_2189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1496, c_2187])).
% 5.51/2.07  tff(c_2191, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_151])).
% 5.51/2.07  tff(c_2211, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2191, c_30])).
% 5.51/2.07  tff(c_2214, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2211])).
% 5.51/2.07  tff(c_2190, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_151])).
% 5.51/2.07  tff(c_2286, plain, (![A_228, B_229, C_230]: (k1_relset_1(A_228, B_229, C_230)=k1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.51/2.07  tff(c_2311, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2191, c_2286])).
% 5.51/2.07  tff(c_2611, plain, (![B_255, C_256, A_257]: (k1_xboole_0=B_255 | v1_funct_2(C_256, A_257, B_255) | k1_relset_1(A_257, B_255, C_256)!=A_257 | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_255))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.51/2.07  tff(c_2617, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2191, c_2611])).
% 5.51/2.07  tff(c_2633, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2617])).
% 5.51/2.07  tff(c_2634, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2190, c_2633])).
% 5.51/2.07  tff(c_2641, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2634])).
% 5.51/2.07  tff(c_2644, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2641])).
% 5.51/2.07  tff(c_2647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_58, c_1543, c_2644])).
% 5.51/2.07  tff(c_2648, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2634])).
% 5.51/2.07  tff(c_2676, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2648, c_2])).
% 5.51/2.07  tff(c_2678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2214, c_2676])).
% 5.51/2.07  tff(c_2680, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_2211])).
% 5.51/2.07  tff(c_2686, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2680, c_108])).
% 5.51/2.07  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.51/2.07  tff(c_2702, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2686, c_2686, c_18])).
% 5.51/2.07  tff(c_2679, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2211])).
% 5.51/2.07  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.51/2.07  tff(c_2736, plain, (![A_260]: (A_260='#skF_1' | ~v1_xboole_0(A_260))), inference(resolution, [status(thm)], [c_2680, c_4])).
% 5.51/2.07  tff(c_2743, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_2679, c_2736])).
% 5.51/2.07  tff(c_2762, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2743, c_26])).
% 5.51/2.07  tff(c_2774, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_58, c_2702, c_1543, c_2762])).
% 5.51/2.07  tff(c_2782, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_1496])).
% 5.51/2.07  tff(c_2789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2680, c_2782])).
% 5.51/2.07  tff(c_2790, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1491])).
% 5.51/2.07  tff(c_2809, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2790, c_108])).
% 5.51/2.07  tff(c_2830, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2809, c_18])).
% 5.51/2.07  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.51/2.07  tff(c_2826, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_12])).
% 5.51/2.07  tff(c_3570, plain, (![A_333, B_334, C_335]: (k1_relset_1(A_333, B_334, C_335)=k1_relat_1(C_335) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.51/2.07  tff(c_3580, plain, (![A_333, B_334]: (k1_relset_1(A_333, B_334, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2826, c_3570])).
% 5.51/2.07  tff(c_3582, plain, (![A_333, B_334]: (k1_relset_1(A_333, B_334, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2830, c_3580])).
% 5.51/2.07  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.51/2.07  tff(c_40, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.51/2.07  tff(c_68, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 5.51/2.07  tff(c_3718, plain, (![C_354, B_355]: (v1_funct_2(C_354, '#skF_3', B_355) | k1_relset_1('#skF_3', B_355, C_354)!='#skF_3' | ~m1_subset_1(C_354, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2809, c_2809, c_2809, c_68])).
% 5.51/2.07  tff(c_3721, plain, (![B_355]: (v1_funct_2('#skF_3', '#skF_3', B_355) | k1_relset_1('#skF_3', B_355, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_2826, c_3718])).
% 5.51/2.07  tff(c_3724, plain, (![B_355]: (v1_funct_2('#skF_3', '#skF_3', B_355))), inference(demodulation, [status(thm), theory('equality')], [c_3582, c_3721])).
% 5.51/2.07  tff(c_2827, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2809, c_10])).
% 5.51/2.07  tff(c_2791, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1491])).
% 5.51/2.07  tff(c_2816, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2791, c_108])).
% 5.51/2.07  tff(c_3360, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2816])).
% 5.51/2.07  tff(c_2986, plain, (![A_278]: (m1_subset_1(A_278, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_278), k2_relat_1(A_278)))) | ~v1_funct_1(A_278) | ~v1_relat_1(A_278))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.07  tff(c_3029, plain, (![A_281]: (v1_xboole_0(A_281) | ~v1_xboole_0(k2_relat_1(A_281)) | ~v1_funct_1(A_281) | ~v1_relat_1(A_281))), inference(resolution, [status(thm)], [c_2986, c_30])).
% 5.51/2.07  tff(c_3314, plain, (![A_316]: (v1_xboole_0(k2_funct_1(A_316)) | ~v1_xboole_0(k1_relat_1(A_316)) | ~v1_funct_1(k2_funct_1(A_316)) | ~v1_relat_1(k2_funct_1(A_316)) | ~v2_funct_1(A_316) | ~v1_funct_1(A_316) | ~v1_relat_1(A_316))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3029])).
% 5.51/2.07  tff(c_2825, plain, (![A_32]: (A_32='#skF_3' | ~v1_xboole_0(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_108])).
% 5.51/2.07  tff(c_3322, plain, (![A_317]: (k2_funct_1(A_317)='#skF_3' | ~v1_xboole_0(k1_relat_1(A_317)) | ~v1_funct_1(k2_funct_1(A_317)) | ~v1_relat_1(k2_funct_1(A_317)) | ~v2_funct_1(A_317) | ~v1_funct_1(A_317) | ~v1_relat_1(A_317))), inference(resolution, [status(thm)], [c_3314, c_2825])).
% 5.51/2.07  tff(c_3325, plain, (k2_funct_1('#skF_3')='#skF_3' | ~v1_xboole_0('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2830, c_3322])).
% 5.51/2.07  tff(c_3330, plain, (k2_funct_1('#skF_3')='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_58, c_152, c_2790, c_3325])).
% 5.51/2.07  tff(c_3331, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3330])).
% 5.51/2.07  tff(c_3334, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_3331])).
% 5.51/2.07  tff(c_3338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_64, c_3334])).
% 5.51/2.07  tff(c_3339, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_3330])).
% 5.51/2.07  tff(c_2840, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_2816])).
% 5.51/2.07  tff(c_2839, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_151])).
% 5.51/2.07  tff(c_2903, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2827, c_2840, c_2839])).
% 5.51/2.07  tff(c_3353, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3339, c_2903])).
% 5.51/2.07  tff(c_3357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2826, c_3353])).
% 5.51/2.07  tff(c_3359, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_151])).
% 5.51/2.07  tff(c_3469, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2827, c_3360, c_3359])).
% 5.51/2.07  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.51/2.07  tff(c_1490, plain, (![C_165]: (v1_xboole_0(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1477])).
% 5.51/2.07  tff(c_1495, plain, (![C_165]: (v1_xboole_0(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1490])).
% 5.51/2.07  tff(c_3453, plain, (![C_165]: (v1_xboole_0(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_1495])).
% 5.51/2.07  tff(c_3479, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3469, c_3453])).
% 5.51/2.07  tff(c_2817, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2791, c_4])).
% 5.51/2.07  tff(c_3389, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3360, c_2817])).
% 5.51/2.07  tff(c_3486, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3479, c_3389])).
% 5.51/2.07  tff(c_3358, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_151])).
% 5.51/2.07  tff(c_3396, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3360, c_3358])).
% 5.51/2.07  tff(c_3491, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3486, c_3396])).
% 5.51/2.07  tff(c_3728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3724, c_3491])).
% 5.51/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.07  
% 5.51/2.07  Inference rules
% 5.51/2.07  ----------------------
% 5.51/2.07  #Ref     : 0
% 5.51/2.07  #Sup     : 761
% 5.51/2.07  #Fact    : 0
% 5.51/2.07  #Define  : 0
% 5.51/2.07  #Split   : 21
% 5.51/2.07  #Chain   : 0
% 5.51/2.07  #Close   : 0
% 5.51/2.07  
% 5.51/2.07  Ordering : KBO
% 5.51/2.07  
% 5.51/2.07  Simplification rules
% 5.51/2.07  ----------------------
% 5.51/2.07  #Subsume      : 113
% 5.51/2.07  #Demod        : 1165
% 5.51/2.07  #Tautology    : 418
% 5.51/2.07  #SimpNegUnit  : 9
% 5.51/2.07  #BackRed      : 206
% 5.51/2.07  
% 5.51/2.07  #Partial instantiations: 0
% 5.51/2.07  #Strategies tried      : 1
% 5.51/2.07  
% 5.51/2.07  Timing (in seconds)
% 5.51/2.07  ----------------------
% 5.51/2.07  Preprocessing        : 0.38
% 5.51/2.08  Parsing              : 0.21
% 5.51/2.08  CNF conversion       : 0.02
% 5.51/2.08  Main loop            : 0.84
% 5.51/2.08  Inferencing          : 0.29
% 5.51/2.08  Reduction            : 0.29
% 5.51/2.08  Demodulation         : 0.21
% 5.51/2.08  BG Simplification    : 0.04
% 5.51/2.08  Subsumption          : 0.14
% 5.51/2.08  Abstraction          : 0.04
% 5.51/2.08  MUC search           : 0.00
% 5.51/2.08  Cooper               : 0.00
% 5.51/2.08  Total                : 1.27
% 5.51/2.08  Index Insertion      : 0.00
% 5.51/2.08  Index Deletion       : 0.00
% 5.51/2.08  Index Matching       : 0.00
% 5.51/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
