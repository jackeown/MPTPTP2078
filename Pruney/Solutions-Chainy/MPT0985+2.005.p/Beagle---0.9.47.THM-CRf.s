%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:25 EST 2020

% Result     : Theorem 8.15s
% Output     : CNFRefutation 8.68s
% Verified   : 
% Statistics : Number of formulae       :  408 (2912 expanded)
%              Number of leaves         :   55 ( 936 expanded)
%              Depth                    :   20
%              Number of atoms          :  693 (7589 expanded)
%              Number of equality atoms :  217 (2063 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_214,negated_conjecture,(
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

tff(f_130,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_165,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_187,axiom,(
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

tff(f_169,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_161,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_141,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_151,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_197,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_98,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_110,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_62,plain,(
    ! [A_31] :
      ( v1_funct_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_100,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_228,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_231,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_228])).

tff(c_234,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_231])).

tff(c_106,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_272,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_279,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_272])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_279])).

tff(c_293,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_331,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_336,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_353,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_336])).

tff(c_64,plain,(
    ! [A_31] :
      ( v1_relat_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_294,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_104,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1053,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_relset_1(A_174,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1072,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_1053])).

tff(c_1580,plain,(
    ! [B_217,A_218,C_219] :
      ( k1_xboole_0 = B_217
      | k1_relset_1(A_218,B_217,C_219) = A_218
      | ~ v1_funct_2(C_219,A_218,B_217)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_218,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1593,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_1580])).

tff(c_1611,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1072,c_1593])).

tff(c_1614,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1611])).

tff(c_102,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1129,plain,(
    ! [A_186,B_187,C_188] :
      ( k2_relset_1(A_186,B_187,C_188) = k2_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1136,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_1129])).

tff(c_1149,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1136])).

tff(c_600,plain,(
    ! [C_138,A_139,B_140] :
      ( v4_relat_1(C_138,A_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_619,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_600])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = B_27
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_623,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_619,c_46])).

tff(c_626,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_623])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_630,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_44])).

tff(c_634,plain,(
    k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_630])).

tff(c_1151,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1149,c_634])).

tff(c_1678,plain,(
    ! [A_222,B_223] :
      ( k9_relat_1(k2_funct_1(A_222),k9_relat_1(A_222,B_223)) = B_223
      | ~ r1_tarski(B_223,k1_relat_1(A_222))
      | ~ v2_funct_1(A_222)
      | ~ v1_funct_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1696,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_1678])).

tff(c_1708,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_110,c_104,c_14,c_1614,c_1696])).

tff(c_66,plain,(
    ! [A_32,B_34] :
      ( k9_relat_1(k2_funct_1(A_32),k9_relat_1(A_32,B_34)) = B_34
      | ~ r1_tarski(B_34,k1_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1716,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1708,c_66])).

tff(c_1720,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_1716])).

tff(c_1744,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1720])).

tff(c_1747,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1744])).

tff(c_1751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_110,c_1747])).

tff(c_1753,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1720])).

tff(c_70,plain,(
    ! [A_35] :
      ( k1_relat_1(k2_funct_1(A_35)) = k2_relat_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1752,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1720])).

tff(c_1842,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1752])).

tff(c_1845,plain,
    ( ~ r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1842])).

tff(c_1851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_110,c_104,c_14,c_1149,c_1845])).

tff(c_1853,plain,(
    r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1752])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1869,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1853,c_10])).

tff(c_1925,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1869])).

tff(c_1928,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1925])).

tff(c_1934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_110,c_104,c_14,c_1149,c_1928])).

tff(c_1935,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1869])).

tff(c_42,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2002,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1935,c_42])).

tff(c_2019,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_1708,c_2002])).

tff(c_94,plain,(
    ! [A_51] :
      ( m1_subset_1(A_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_51),k2_relat_1(A_51))))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2036,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2019,c_94])).

tff(c_2066,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_294,c_1935,c_2036])).

tff(c_2068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_2066])).

tff(c_2069,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1611])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2105,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_8])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2099,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_2069,c_18])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_488,plain,(
    ! [C_121,B_122,A_123] :
      ( ~ v1_xboole_0(C_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(C_121))
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_498,plain,(
    ! [A_124,A_125] :
      ( ~ v1_xboole_0(A_124)
      | ~ r2_hidden(A_125,A_124) ) ),
    inference(resolution,[status(thm)],[c_111,c_488])).

tff(c_503,plain,(
    ! [A_126,B_127] :
      ( ~ v1_xboole_0(A_126)
      | r1_tarski(A_126,B_127) ) ),
    inference(resolution,[status(thm)],[c_6,c_498])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_335,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_331])).

tff(c_527,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_503,c_335])).

tff(c_796,plain,(
    ! [A_152] :
      ( k4_relat_1(A_152) = k2_funct_1(A_152)
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_802,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_796])).

tff(c_806,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_110,c_802])).

tff(c_40,plain,(
    ! [A_22] :
      ( v1_xboole_0(k4_relat_1(A_22))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_819,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_40])).

tff(c_823,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_527,c_819])).

tff(c_1180,plain,(
    ! [A_189] :
      ( m1_subset_1(A_189,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_189),k2_relat_1(A_189))))
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1206,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_1180])).

tff(c_1237,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_110,c_1206])).

tff(c_26,plain,(
    ! [B_14,A_12] :
      ( v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1263,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_1237,c_26])).

tff(c_1278,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_1263])).

tff(c_2310,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_1278])).

tff(c_2318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2105,c_2310])).

tff(c_2319,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_2320,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_2373,plain,(
    ! [C_263,A_264,B_265] :
      ( v1_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2392,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2320,c_2373])).

tff(c_2394,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_2373])).

tff(c_3470,plain,(
    ! [A_374,B_375,C_376] :
      ( k1_relset_1(A_374,B_375,C_376) = k1_relat_1(C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3501,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_3470])).

tff(c_3753,plain,(
    ! [B_399,A_400,C_401] :
      ( k1_xboole_0 = B_399
      | k1_relset_1(A_400,B_399,C_401) = A_400
      | ~ v1_funct_2(C_401,A_400,B_399)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_400,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3769,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_3753])).

tff(c_3789,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3501,c_3769])).

tff(c_3792,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3789])).

tff(c_2795,plain,(
    ! [C_308,A_309,B_310] :
      ( v4_relat_1(C_308,A_309)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2816,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2320,c_2795])).

tff(c_2828,plain,
    ( k7_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2816,c_46])).

tff(c_2831,plain,(
    k7_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_2828])).

tff(c_2934,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2831,c_44])).

tff(c_2938,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_2934])).

tff(c_3205,plain,(
    ! [A_356,B_357,C_358] :
      ( k2_relset_1(A_356,B_357,C_358) = k2_relat_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_3215,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_3205])).

tff(c_3229,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_3215])).

tff(c_2818,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_2795])).

tff(c_2822,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2818,c_46])).

tff(c_2825,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_2822])).

tff(c_2835,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2825,c_44])).

tff(c_2839,plain,(
    k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_2835])).

tff(c_3231,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3229,c_2839])).

tff(c_3855,plain,(
    ! [A_404,B_405] :
      ( k9_relat_1(k2_funct_1(A_404),k9_relat_1(A_404,B_405)) = B_405
      | ~ r1_tarski(B_405,k1_relat_1(A_404))
      | ~ v2_funct_1(A_404)
      | ~ v1_funct_1(A_404)
      | ~ v1_relat_1(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3873,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3231,c_3855])).

tff(c_3888,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_110,c_104,c_14,c_3792,c_2938,c_3873])).

tff(c_3499,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2320,c_3470])).

tff(c_3955,plain,(
    ! [B_406,C_407,A_408] :
      ( k1_xboole_0 = B_406
      | v1_funct_2(C_407,A_408,B_406)
      | k1_relset_1(A_408,B_406,C_407) != A_408
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_408,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3961,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2320,c_3955])).

tff(c_3981,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3961])).

tff(c_3982,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2319,c_3981])).

tff(c_3989,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3982])).

tff(c_3992,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3989])).

tff(c_3995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_110,c_104,c_3229,c_3992])).

tff(c_3997,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3982])).

tff(c_96,plain,(
    ! [A_51] :
      ( v1_funct_2(A_51,k1_relat_1(A_51),k2_relat_1(A_51))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_4060,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3997,c_96])).

tff(c_4078,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_294,c_3888,c_4060])).

tff(c_4080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2319,c_4078])).

tff(c_4081,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3789])).

tff(c_4122,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4081,c_8])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4118,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4081,c_4081,c_20])).

tff(c_2327,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2320,c_26])).

tff(c_2333,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2327])).

tff(c_4313,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4118,c_2333])).

tff(c_4318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4122,c_4313])).

tff(c_4320,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2327])).

tff(c_4557,plain,(
    ! [C_452,B_453,A_454] :
      ( ~ v1_xboole_0(C_452)
      | ~ m1_subset_1(B_453,k1_zfmisc_1(C_452))
      | ~ r2_hidden(A_454,B_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4657,plain,(
    ! [A_461,A_462] :
      ( ~ v1_xboole_0(A_461)
      | ~ r2_hidden(A_462,A_461) ) ),
    inference(resolution,[status(thm)],[c_111,c_4557])).

tff(c_4739,plain,(
    ! [A_469,B_470] :
      ( ~ v1_xboole_0(A_469)
      | r1_tarski(A_469,B_470) ) ),
    inference(resolution,[status(thm)],[c_6,c_4657])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2328,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2320,c_28])).

tff(c_4321,plain,(
    ! [B_414,A_415] :
      ( B_414 = A_415
      | ~ r1_tarski(B_414,A_415)
      | ~ r1_tarski(A_415,B_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4328,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2328,c_4321])).

tff(c_4556,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4328])).

tff(c_4742,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4739,c_4556])).

tff(c_4766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4320,c_4742])).

tff(c_4767,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4328])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4795,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k2_funct_1('#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4767,c_16])).

tff(c_4974,plain,(
    k2_funct_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4795])).

tff(c_4319,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2327])).

tff(c_4921,plain,(
    ! [C_481,B_482,A_483] :
      ( ~ v1_xboole_0(C_481)
      | ~ m1_subset_1(B_482,k1_zfmisc_1(C_481))
      | ~ r2_hidden(A_483,B_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4931,plain,(
    ! [A_484,A_485] :
      ( ~ v1_xboole_0(A_484)
      | ~ r2_hidden(A_485,A_484) ) ),
    inference(resolution,[status(thm)],[c_111,c_4921])).

tff(c_4935,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_4931])).

tff(c_4936,plain,(
    ! [A_486,B_487] :
      ( ~ v1_xboole_0(A_486)
      | r1_tarski(A_486,B_487) ) ),
    inference(resolution,[status(thm)],[c_6,c_4931])).

tff(c_5026,plain,(
    ! [B_496,A_497] :
      ( B_496 = A_497
      | ~ r1_tarski(B_496,A_497)
      | ~ v1_xboole_0(A_497) ) ),
    inference(resolution,[status(thm)],[c_4936,c_10])).

tff(c_5040,plain,(
    ! [B_498,A_499] :
      ( B_498 = A_499
      | ~ v1_xboole_0(B_498)
      | ~ v1_xboole_0(A_499) ) ),
    inference(resolution,[status(thm)],[c_4935,c_5026])).

tff(c_5053,plain,(
    ! [A_500] :
      ( k1_xboole_0 = A_500
      | ~ v1_xboole_0(A_500) ) ),
    inference(resolution,[status(thm)],[c_8,c_5040])).

tff(c_5056,plain,(
    k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4319,c_5053])).

tff(c_5069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4974,c_5056])).

tff(c_5070,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4795])).

tff(c_5100,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5070])).

tff(c_5132,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5100,c_8])).

tff(c_5128,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5100,c_5100,c_20])).

tff(c_297,plain,(
    ! [B_87,A_88] :
      ( v1_xboole_0(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_308,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_106,c_297])).

tff(c_321,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_5311,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5128,c_321])).

tff(c_5316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5132,c_5311])).

tff(c_5317,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5070])).

tff(c_5336,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5317,c_8])).

tff(c_5330,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5317,c_5317,c_18])).

tff(c_5519,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5330,c_321])).

tff(c_5524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5336,c_5519])).

tff(c_5526,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_8688,plain,(
    ! [C_870,B_871,A_872] :
      ( ~ v1_xboole_0(C_870)
      | ~ m1_subset_1(B_871,k1_zfmisc_1(C_870))
      | ~ r2_hidden(A_872,B_871) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8761,plain,(
    ! [A_877,A_878] :
      ( ~ v1_xboole_0(A_877)
      | ~ r2_hidden(A_878,A_877) ) ),
    inference(resolution,[status(thm)],[c_111,c_8688])).

tff(c_8766,plain,(
    ! [A_879,B_880] :
      ( ~ v1_xboole_0(A_879)
      | r1_tarski(A_879,B_880) ) ),
    inference(resolution,[status(thm)],[c_6,c_8761])).

tff(c_214,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_225,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_106,c_214])).

tff(c_8581,plain,(
    ! [B_856,A_857] :
      ( B_856 = A_857
      | ~ r1_tarski(B_856,A_857)
      | ~ r1_tarski(A_857,B_856) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8589,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_225,c_8581])).

tff(c_8640,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8589])).

tff(c_8773,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8766,c_8640])).

tff(c_8787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_8773])).

tff(c_8788,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8589])).

tff(c_8805,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8788,c_16])).

tff(c_8855,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8805])).

tff(c_5525,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_7483,plain,(
    ! [C_771,B_772,A_773] :
      ( ~ v1_xboole_0(C_771)
      | ~ m1_subset_1(B_772,k1_zfmisc_1(C_771))
      | ~ r2_hidden(A_773,B_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7526,plain,(
    ! [A_776,A_777] :
      ( ~ v1_xboole_0(A_776)
      | ~ r2_hidden(A_777,A_776) ) ),
    inference(resolution,[status(thm)],[c_111,c_7483])).

tff(c_7530,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_7526])).

tff(c_7489,plain,(
    ! [A_773] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_773,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_106,c_7483])).

tff(c_7498,plain,(
    ! [A_774] : ~ r2_hidden(A_774,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_7489])).

tff(c_7505,plain,(
    ! [B_775] : r1_tarski('#skF_4',B_775) ),
    inference(resolution,[status(thm)],[c_6,c_7498])).

tff(c_7549,plain,(
    ! [B_780] :
      ( B_780 = '#skF_4'
      | ~ r1_tarski(B_780,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7505,c_10])).

tff(c_7567,plain,(
    ! [A_781] :
      ( A_781 = '#skF_4'
      | ~ v1_xboole_0(A_781) ) ),
    inference(resolution,[status(thm)],[c_7530,c_7549])).

tff(c_7588,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_7567])).

tff(c_7621,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7588,c_7588,c_20])).

tff(c_7619,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7588,c_7588,c_18])).

tff(c_7583,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5526,c_7567])).

tff(c_8459,plain,(
    ! [B_853,A_854] :
      ( B_853 = '#skF_4'
      | A_854 = '#skF_4'
      | k2_zfmisc_1(A_854,B_853) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7588,c_7588,c_7588,c_16])).

tff(c_8473,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7583,c_8459])).

tff(c_8529,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8473])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5533,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5525,c_34])).

tff(c_6828,plain,(
    ! [C_685,B_686,A_687] :
      ( ~ v1_xboole_0(C_685)
      | ~ m1_subset_1(B_686,k1_zfmisc_1(C_685))
      | ~ r2_hidden(A_687,B_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6835,plain,(
    ! [A_688,A_689] :
      ( ~ v1_xboole_0(A_688)
      | ~ r2_hidden(A_689,A_688) ) ),
    inference(resolution,[status(thm)],[c_111,c_6828])).

tff(c_6839,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_6835])).

tff(c_6840,plain,(
    ! [A_690,B_691] :
      ( ~ v1_xboole_0(A_690)
      | r1_tarski(A_690,B_691) ) ),
    inference(resolution,[status(thm)],[c_6,c_6835])).

tff(c_6863,plain,(
    ! [B_694,A_695] :
      ( B_694 = A_695
      | ~ r1_tarski(B_694,A_695)
      | ~ v1_xboole_0(A_695) ) ),
    inference(resolution,[status(thm)],[c_6840,c_10])).

tff(c_6873,plain,(
    ! [B_696,A_697] :
      ( B_696 = A_697
      | ~ v1_xboole_0(B_696)
      | ~ v1_xboole_0(A_697) ) ),
    inference(resolution,[status(thm)],[c_6839,c_6863])).

tff(c_6883,plain,(
    ! [A_698] :
      ( A_698 = '#skF_4'
      | ~ v1_xboole_0(A_698) ) ),
    inference(resolution,[status(thm)],[c_5525,c_6873])).

tff(c_6911,plain,(
    ! [A_700] :
      ( k4_relat_1(A_700) = '#skF_4'
      | ~ v1_xboole_0(A_700) ) ),
    inference(resolution,[status(thm)],[c_40,c_6883])).

tff(c_6921,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5525,c_6911])).

tff(c_7313,plain,(
    ! [A_749] :
      ( k4_relat_1(A_749) = k2_funct_1(A_749)
      | ~ v2_funct_1(A_749)
      | ~ v1_funct_1(A_749)
      | ~ v1_relat_1(A_749) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_7319,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_7313])).

tff(c_7323,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5533,c_110,c_6921,c_7319])).

tff(c_5725,plain,(
    ! [C_545,B_546,A_547] :
      ( ~ v1_xboole_0(C_545)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(C_545))
      | ~ r2_hidden(A_547,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5765,plain,(
    ! [A_550,A_551] :
      ( ~ v1_xboole_0(A_550)
      | ~ r2_hidden(A_551,A_550) ) ),
    inference(resolution,[status(thm)],[c_111,c_5725])).

tff(c_5783,plain,(
    ! [A_553,B_554] :
      ( ~ v1_xboole_0(A_553)
      | r1_tarski(A_553,B_554) ) ),
    inference(resolution,[status(thm)],[c_6,c_5765])).

tff(c_5567,plain,(
    ! [B_517,A_518] :
      ( B_517 = A_518
      | ~ r1_tarski(B_517,A_518)
      | ~ r1_tarski(A_518,B_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5572,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_225,c_5567])).

tff(c_5623,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5572])).

tff(c_5798,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5783,c_5623])).

tff(c_5813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_5798])).

tff(c_5814,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5572])).

tff(c_5831,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5814,c_16])).

tff(c_5857,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5831])).

tff(c_5891,plain,(
    ! [C_565,B_566,A_567] :
      ( ~ v1_xboole_0(C_565)
      | ~ m1_subset_1(B_566,k1_zfmisc_1(C_565))
      | ~ r2_hidden(A_567,B_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5898,plain,(
    ! [A_568,A_569] :
      ( ~ v1_xboole_0(A_568)
      | ~ r2_hidden(A_569,A_568) ) ),
    inference(resolution,[status(thm)],[c_111,c_5891])).

tff(c_5902,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_5898])).

tff(c_5935,plain,(
    ! [A_576,B_577] :
      ( ~ v1_xboole_0(A_576)
      | r1_tarski(A_576,B_577) ) ),
    inference(resolution,[status(thm)],[c_6,c_5898])).

tff(c_5977,plain,(
    ! [B_585,A_586] :
      ( B_585 = A_586
      | ~ r1_tarski(B_585,A_586)
      | ~ v1_xboole_0(A_586) ) ),
    inference(resolution,[status(thm)],[c_5935,c_10])).

tff(c_5987,plain,(
    ! [B_587,A_588] :
      ( B_587 = A_588
      | ~ v1_xboole_0(B_587)
      | ~ v1_xboole_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_5902,c_5977])).

tff(c_6000,plain,(
    ! [A_589] :
      ( A_589 = '#skF_4'
      | ~ v1_xboole_0(A_589) ) ),
    inference(resolution,[status(thm)],[c_5525,c_5987])).

tff(c_6012,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_6000])).

tff(c_6020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5857,c_6012])).

tff(c_6022,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5831])).

tff(c_6040,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6022,c_6022,c_18])).

tff(c_6144,plain,(
    ! [C_597,B_598,A_599] :
      ( ~ v1_xboole_0(C_597)
      | ~ m1_subset_1(B_598,k1_zfmisc_1(C_597))
      | ~ r2_hidden(A_599,B_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6151,plain,(
    ! [A_600,A_601] :
      ( ~ v1_xboole_0(A_600)
      | ~ r2_hidden(A_601,A_600) ) ),
    inference(resolution,[status(thm)],[c_111,c_6144])).

tff(c_6155,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_6151])).

tff(c_6156,plain,(
    ! [A_602,B_603] :
      ( ~ v1_xboole_0(A_602)
      | r1_tarski(A_602,B_603) ) ),
    inference(resolution,[status(thm)],[c_6,c_6151])).

tff(c_6195,plain,(
    ! [B_607,A_608] :
      ( B_607 = A_608
      | ~ r1_tarski(B_607,A_608)
      | ~ v1_xboole_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_6156,c_10])).

tff(c_6205,plain,(
    ! [B_609,A_610] :
      ( B_609 = A_610
      | ~ v1_xboole_0(B_609)
      | ~ v1_xboole_0(A_610) ) ),
    inference(resolution,[status(thm)],[c_6155,c_6195])).

tff(c_6215,plain,(
    ! [A_611] :
      ( A_611 = '#skF_4'
      | ~ v1_xboole_0(A_611) ) ),
    inference(resolution,[status(thm)],[c_5525,c_6205])).

tff(c_6255,plain,(
    ! [A_618] :
      ( k4_relat_1(A_618) = '#skF_4'
      | ~ v1_xboole_0(A_618) ) ),
    inference(resolution,[status(thm)],[c_40,c_6215])).

tff(c_6265,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5525,c_6255])).

tff(c_6718,plain,(
    ! [A_672] :
      ( k4_relat_1(A_672) = k2_funct_1(A_672)
      | ~ v2_funct_1(A_672)
      | ~ v1_funct_1(A_672)
      | ~ v1_relat_1(A_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6724,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_6718])).

tff(c_6728,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5533,c_110,c_6265,c_6724])).

tff(c_6042,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6022,c_6022,c_20])).

tff(c_6021,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5831])).

tff(c_6094,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6022,c_6022,c_6021])).

tff(c_6095,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6094])).

tff(c_5551,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_5555,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_5551])).

tff(c_6098,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6095,c_5555])).

tff(c_6169,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6042,c_6098])).

tff(c_6173,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6155,c_6169])).

tff(c_6729,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6728,c_6173])).

tff(c_6735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_6729])).

tff(c_6736,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6094])).

tff(c_6739,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6736,c_5555])).

tff(c_6743,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6040,c_6739])).

tff(c_6859,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6840,c_6743])).

tff(c_7324,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7323,c_6859])).

tff(c_7330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_7324])).

tff(c_7332,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_7339,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7332,c_26])).

tff(c_7356,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7339])).

tff(c_8536,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8529,c_7356])).

tff(c_8543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_7619,c_8536])).

tff(c_8544,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8473])).

tff(c_8552,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_7356])).

tff(c_8559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_7621,c_8552])).

tff(c_8561,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7339])).

tff(c_8893,plain,(
    ! [C_891,B_892,A_893] :
      ( ~ v1_xboole_0(C_891)
      | ~ m1_subset_1(B_892,k1_zfmisc_1(C_891))
      | ~ r2_hidden(A_893,B_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8895,plain,(
    ! [A_893] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_893,k2_funct_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_7332,c_8893])).

tff(c_8905,plain,(
    ! [A_894] : ~ r2_hidden(A_894,k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8561,c_8895])).

tff(c_8910,plain,(
    ! [B_2] : r1_tarski(k2_funct_1('#skF_4'),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_8905])).

tff(c_9006,plain,(
    ! [A_903,A_904] :
      ( ~ v1_xboole_0(A_903)
      | ~ r2_hidden(A_904,A_903) ) ),
    inference(resolution,[status(thm)],[c_111,c_8893])).

tff(c_9031,plain,(
    ! [A_905,B_906] :
      ( ~ v1_xboole_0(A_905)
      | r1_tarski(A_905,B_906) ) ),
    inference(resolution,[status(thm)],[c_6,c_9006])).

tff(c_9085,plain,(
    ! [B_909,A_910] :
      ( B_909 = A_910
      | ~ r1_tarski(B_909,A_910)
      | ~ v1_xboole_0(A_910) ) ),
    inference(resolution,[status(thm)],[c_9031,c_10])).

tff(c_9099,plain,(
    ! [B_911] :
      ( k2_funct_1('#skF_4') = B_911
      | ~ v1_xboole_0(B_911) ) ),
    inference(resolution,[status(thm)],[c_8910,c_9085])).

tff(c_9117,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5525,c_9099])).

tff(c_9120,plain,(
    k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_9099])).

tff(c_9168,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9117,c_9120])).

tff(c_9169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8855,c_9168])).

tff(c_9171,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8805])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_9182,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_9171,c_50])).

tff(c_9179,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_9171,c_20])).

tff(c_11778,plain,(
    ! [A_1152,B_1153,C_1154] :
      ( k1_relset_1(A_1152,B_1153,C_1154) = k1_relat_1(C_1154)
      | ~ m1_subset_1(C_1154,k1_zfmisc_1(k2_zfmisc_1(A_1152,B_1153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_11795,plain,(
    ! [A_1155,B_1156] : k1_relset_1(A_1155,B_1156,k2_zfmisc_1(A_1155,B_1156)) = k1_relat_1(k2_zfmisc_1(A_1155,B_1156)) ),
    inference(resolution,[status(thm)],[c_111,c_11778])).

tff(c_11804,plain,(
    ! [B_9] : k1_relat_1(k2_zfmisc_1('#skF_4',B_9)) = k1_relset_1('#skF_4',B_9,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9179,c_11795])).

tff(c_11810,plain,(
    ! [B_9] : k1_relset_1('#skF_4',B_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9182,c_9179,c_11804])).

tff(c_86,plain,(
    ! [C_50,B_49] :
      ( v1_funct_2(C_50,k1_xboole_0,B_49)
      | k1_relset_1(k1_xboole_0,B_49,C_50) != k1_xboole_0
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_112,plain,(
    ! [C_50,B_49] :
      ( v1_funct_2(C_50,k1_xboole_0,B_49)
      | k1_relset_1(k1_xboole_0,B_49,C_50) != k1_xboole_0
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_86])).

tff(c_12945,plain,(
    ! [C_1216,B_1217] :
      ( v1_funct_2(C_1216,'#skF_4',B_1217)
      | k1_relset_1('#skF_4',B_1217,C_1216) != '#skF_4'
      | ~ m1_subset_1(C_1216,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_9171,c_9171,c_9171,c_112])).

tff(c_12951,plain,(
    ! [B_1217] :
      ( v1_funct_2('#skF_4','#skF_4',B_1217)
      | k1_relset_1('#skF_4',B_1217,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_111,c_12945])).

tff(c_12955,plain,(
    ! [B_1217] : v1_funct_2('#skF_4','#skF_4',B_1217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_12951])).

tff(c_9170,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8805])).

tff(c_9982,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_9171,c_9170])).

tff(c_9983,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9982])).

tff(c_9903,plain,(
    ! [C_1005,B_1006,A_1007] :
      ( ~ v1_xboole_0(C_1005)
      | ~ m1_subset_1(B_1006,k1_zfmisc_1(C_1005))
      | ~ r2_hidden(A_1007,B_1006) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9943,plain,(
    ! [A_1010,A_1011] :
      ( ~ v1_xboole_0(A_1010)
      | ~ r2_hidden(A_1011,A_1010) ) ),
    inference(resolution,[status(thm)],[c_111,c_9903])).

tff(c_9948,plain,(
    ! [A_1012,B_1013] :
      ( ~ v1_xboole_0(A_1012)
      | r1_tarski(A_1012,B_1013) ) ),
    inference(resolution,[status(thm)],[c_6,c_9943])).

tff(c_9177,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_9171,c_18])).

tff(c_9592,plain,(
    ! [C_967,B_968,A_969] :
      ( ~ v1_xboole_0(C_967)
      | ~ m1_subset_1(B_968,k1_zfmisc_1(C_967))
      | ~ r2_hidden(A_969,B_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9644,plain,(
    ! [A_972,A_973] :
      ( ~ v1_xboole_0(A_972)
      | ~ r2_hidden(A_973,A_972) ) ),
    inference(resolution,[status(thm)],[c_111,c_9592])).

tff(c_9649,plain,(
    ! [A_974,B_975] :
      ( ~ v1_xboole_0(A_974)
      | r1_tarski(A_974,B_975) ) ),
    inference(resolution,[status(thm)],[c_6,c_9644])).

tff(c_9220,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_9171,c_9170])).

tff(c_9221,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9220])).

tff(c_7340,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7332,c_28])).

tff(c_8588,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7340,c_8581])).

tff(c_9210,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8588])).

tff(c_9279,plain,(
    ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9179,c_9221,c_9210])).

tff(c_9664,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_9649,c_9279])).

tff(c_9680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_9664])).

tff(c_9681,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9220])).

tff(c_9766,plain,(
    ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9177,c_9681,c_9210])).

tff(c_9955,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_9948,c_9766])).

tff(c_9969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_9955])).

tff(c_9970,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8588])).

tff(c_10066,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9179,c_9983,c_9970])).

tff(c_7331,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_9989,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9983,c_7331])).

tff(c_10087,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10066,c_9989])).

tff(c_12959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12955,c_10087])).

tff(c_12961,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9982])).

tff(c_82,plain,(
    ! [A_48] :
      ( v1_funct_2(k1_xboole_0,A_48,k1_xboole_0)
      | k1_xboole_0 = A_48
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_48,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_115,plain,(
    ! [A_48] :
      ( v1_funct_2(k1_xboole_0,A_48,k1_xboole_0)
      | k1_xboole_0 = A_48
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_117,plain,(
    ! [A_48] :
      ( v1_funct_2(k1_xboole_0,A_48,k1_xboole_0)
      | k1_xboole_0 = A_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_115])).

tff(c_13073,plain,(
    ! [A_1229] :
      ( v1_funct_2('#skF_4',A_1229,'#skF_4')
      | A_1229 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_9171,c_9171,c_117])).

tff(c_12960,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9982])).

tff(c_13045,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9177,c_12960,c_9970])).

tff(c_12967,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12960,c_7331])).

tff(c_13066,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13045,c_12967])).

tff(c_13076,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13073,c_13066])).

tff(c_13080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12961,c_13076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:26:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.15/2.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/2.99  
% 8.43/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/3.00  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.43/3.00  
% 8.43/3.00  %Foreground sorts:
% 8.43/3.00  
% 8.43/3.00  
% 8.43/3.00  %Background operators:
% 8.43/3.00  
% 8.43/3.00  
% 8.43/3.00  %Foreground operators:
% 8.43/3.00  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.43/3.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.43/3.00  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.43/3.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.43/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.43/3.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.43/3.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.43/3.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.43/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.43/3.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.43/3.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.43/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.43/3.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.43/3.00  tff('#skF_3', type, '#skF_3': $i).
% 8.43/3.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.43/3.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.43/3.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.43/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.43/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.43/3.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.43/3.00  tff('#skF_4', type, '#skF_4': $i).
% 8.43/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.43/3.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.43/3.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.43/3.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.43/3.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.43/3.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.43/3.00  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.43/3.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.43/3.00  
% 8.68/3.04  tff(f_214, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.68/3.04  tff(f_130, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.68/3.04  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.68/3.04  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.68/3.04  tff(f_165, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.68/3.04  tff(f_187, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.68/3.04  tff(f_169, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.68/3.04  tff(f_161, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.68/3.04  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.68/3.04  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 8.68/3.04  tff(f_141, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 8.68/3.04  tff(f_151, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.68/3.04  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.68/3.04  tff(f_197, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 8.68/3.04  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.68/3.04  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.68/3.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.68/3.04  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.68/3.04  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.68/3.04  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.68/3.04  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.68/3.04  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.68/3.04  tff(f_81, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 8.68/3.04  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.68/3.04  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 8.68/3.04  tff(f_98, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 8.68/3.04  tff(c_110, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.68/3.04  tff(c_62, plain, (![A_31]: (v1_funct_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.68/3.04  tff(c_100, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.68/3.04  tff(c_228, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_100])).
% 8.68/3.04  tff(c_231, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_228])).
% 8.68/3.04  tff(c_234, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_231])).
% 8.68/3.04  tff(c_106, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.68/3.04  tff(c_272, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.68/3.04  tff(c_279, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_272])).
% 8.68/3.04  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_279])).
% 8.68/3.04  tff(c_293, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_100])).
% 8.68/3.04  tff(c_331, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_293])).
% 8.68/3.04  tff(c_336, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.68/3.04  tff(c_353, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_336])).
% 8.68/3.04  tff(c_64, plain, (![A_31]: (v1_relat_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.68/3.04  tff(c_294, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_100])).
% 8.68/3.04  tff(c_104, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.68/3.04  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.68/3.04  tff(c_108, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.68/3.04  tff(c_1053, plain, (![A_174, B_175, C_176]: (k1_relset_1(A_174, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.68/3.04  tff(c_1072, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_1053])).
% 8.68/3.04  tff(c_1580, plain, (![B_217, A_218, C_219]: (k1_xboole_0=B_217 | k1_relset_1(A_218, B_217, C_219)=A_218 | ~v1_funct_2(C_219, A_218, B_217) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_218, B_217))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.68/3.04  tff(c_1593, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_106, c_1580])).
% 8.68/3.04  tff(c_1611, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1072, c_1593])).
% 8.68/3.04  tff(c_1614, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1611])).
% 8.68/3.04  tff(c_102, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_214])).
% 8.68/3.04  tff(c_1129, plain, (![A_186, B_187, C_188]: (k2_relset_1(A_186, B_187, C_188)=k2_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.68/3.04  tff(c_1136, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_1129])).
% 8.68/3.04  tff(c_1149, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1136])).
% 8.68/3.04  tff(c_600, plain, (![C_138, A_139, B_140]: (v4_relat_1(C_138, A_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.68/3.04  tff(c_619, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_106, c_600])).
% 8.68/3.04  tff(c_46, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=B_27 | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.68/3.04  tff(c_623, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_619, c_46])).
% 8.68/3.04  tff(c_626, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_623])).
% 8.68/3.04  tff(c_44, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.68/3.04  tff(c_630, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_626, c_44])).
% 8.68/3.04  tff(c_634, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_630])).
% 8.68/3.04  tff(c_1151, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1149, c_634])).
% 8.68/3.04  tff(c_1678, plain, (![A_222, B_223]: (k9_relat_1(k2_funct_1(A_222), k9_relat_1(A_222, B_223))=B_223 | ~r1_tarski(B_223, k1_relat_1(A_222)) | ~v2_funct_1(A_222) | ~v1_funct_1(A_222) | ~v1_relat_1(A_222))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.68/3.04  tff(c_1696, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1151, c_1678])).
% 8.68/3.04  tff(c_1708, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_110, c_104, c_14, c_1614, c_1696])).
% 8.68/3.04  tff(c_66, plain, (![A_32, B_34]: (k9_relat_1(k2_funct_1(A_32), k9_relat_1(A_32, B_34))=B_34 | ~r1_tarski(B_34, k1_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.68/3.04  tff(c_1716, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1708, c_66])).
% 8.68/3.04  tff(c_1720, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_1716])).
% 8.68/3.04  tff(c_1744, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1720])).
% 8.68/3.04  tff(c_1747, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1744])).
% 8.68/3.04  tff(c_1751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_110, c_1747])).
% 8.68/3.04  tff(c_1753, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1720])).
% 8.68/3.04  tff(c_70, plain, (![A_35]: (k1_relat_1(k2_funct_1(A_35))=k2_relat_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.68/3.04  tff(c_1752, plain, (~v2_funct_1(k2_funct_1('#skF_4')) | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1720])).
% 8.68/3.04  tff(c_1842, plain, (~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_1752])).
% 8.68/3.04  tff(c_1845, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70, c_1842])).
% 8.68/3.04  tff(c_1851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_110, c_104, c_14, c_1149, c_1845])).
% 8.68/3.04  tff(c_1853, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1752])).
% 8.68/3.04  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.68/3.04  tff(c_1869, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_1853, c_10])).
% 8.68/3.04  tff(c_1925, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_1869])).
% 8.68/3.04  tff(c_1928, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70, c_1925])).
% 8.68/3.04  tff(c_1934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_110, c_104, c_14, c_1149, c_1928])).
% 8.68/3.04  tff(c_1935, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_1869])).
% 8.68/3.04  tff(c_42, plain, (![A_23]: (k9_relat_1(A_23, k1_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.68/3.04  tff(c_2002, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1935, c_42])).
% 8.68/3.04  tff(c_2019, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_1708, c_2002])).
% 8.68/3.04  tff(c_94, plain, (![A_51]: (m1_subset_1(A_51, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_51), k2_relat_1(A_51)))) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.68/3.04  tff(c_2036, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2019, c_94])).
% 8.68/3.04  tff(c_2066, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_294, c_1935, c_2036])).
% 8.68/3.04  tff(c_2068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_2066])).
% 8.68/3.04  tff(c_2069, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1611])).
% 8.68/3.04  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.68/3.04  tff(c_2105, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_8])).
% 8.68/3.04  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.68/3.04  tff(c_2099, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_2069, c_18])).
% 8.68/3.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.68/3.04  tff(c_22, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.68/3.04  tff(c_24, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.68/3.04  tff(c_111, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 8.68/3.04  tff(c_488, plain, (![C_121, B_122, A_123]: (~v1_xboole_0(C_121) | ~m1_subset_1(B_122, k1_zfmisc_1(C_121)) | ~r2_hidden(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_498, plain, (![A_124, A_125]: (~v1_xboole_0(A_124) | ~r2_hidden(A_125, A_124))), inference(resolution, [status(thm)], [c_111, c_488])).
% 8.68/3.04  tff(c_503, plain, (![A_126, B_127]: (~v1_xboole_0(A_126) | r1_tarski(A_126, B_127))), inference(resolution, [status(thm)], [c_6, c_498])).
% 8.68/3.04  tff(c_30, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.68/3.04  tff(c_335, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_331])).
% 8.68/3.04  tff(c_527, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_503, c_335])).
% 8.68/3.04  tff(c_796, plain, (![A_152]: (k4_relat_1(A_152)=k2_funct_1(A_152) | ~v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.68/3.04  tff(c_802, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_796])).
% 8.68/3.04  tff(c_806, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_110, c_802])).
% 8.68/3.04  tff(c_40, plain, (![A_22]: (v1_xboole_0(k4_relat_1(A_22)) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.68/3.04  tff(c_819, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_806, c_40])).
% 8.68/3.04  tff(c_823, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_527, c_819])).
% 8.68/3.04  tff(c_1180, plain, (![A_189]: (m1_subset_1(A_189, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_189), k2_relat_1(A_189)))) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.68/3.04  tff(c_1206, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1149, c_1180])).
% 8.68/3.04  tff(c_1237, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_110, c_1206])).
% 8.68/3.04  tff(c_26, plain, (![B_14, A_12]: (v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.68/3.04  tff(c_1263, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_1237, c_26])).
% 8.68/3.04  tff(c_1278, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_823, c_1263])).
% 8.68/3.04  tff(c_2310, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2099, c_1278])).
% 8.68/3.04  tff(c_2318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2105, c_2310])).
% 8.68/3.04  tff(c_2319, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_293])).
% 8.68/3.04  tff(c_2320, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_293])).
% 8.68/3.04  tff(c_2373, plain, (![C_263, A_264, B_265]: (v1_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.68/3.04  tff(c_2392, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2320, c_2373])).
% 8.68/3.04  tff(c_2394, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_2373])).
% 8.68/3.04  tff(c_3470, plain, (![A_374, B_375, C_376]: (k1_relset_1(A_374, B_375, C_376)=k1_relat_1(C_376) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.68/3.04  tff(c_3501, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_3470])).
% 8.68/3.04  tff(c_3753, plain, (![B_399, A_400, C_401]: (k1_xboole_0=B_399 | k1_relset_1(A_400, B_399, C_401)=A_400 | ~v1_funct_2(C_401, A_400, B_399) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_400, B_399))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.68/3.04  tff(c_3769, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_106, c_3753])).
% 8.68/3.04  tff(c_3789, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3501, c_3769])).
% 8.68/3.04  tff(c_3792, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_3789])).
% 8.68/3.04  tff(c_2795, plain, (![C_308, A_309, B_310]: (v4_relat_1(C_308, A_309) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.68/3.04  tff(c_2816, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2320, c_2795])).
% 8.68/3.04  tff(c_2828, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2816, c_46])).
% 8.68/3.04  tff(c_2831, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_2828])).
% 8.68/3.04  tff(c_2934, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2831, c_44])).
% 8.68/3.04  tff(c_2938, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_2934])).
% 8.68/3.04  tff(c_3205, plain, (![A_356, B_357, C_358]: (k2_relset_1(A_356, B_357, C_358)=k2_relat_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.68/3.04  tff(c_3215, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_3205])).
% 8.68/3.04  tff(c_3229, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_3215])).
% 8.68/3.04  tff(c_2818, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_106, c_2795])).
% 8.68/3.04  tff(c_2822, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2818, c_46])).
% 8.68/3.04  tff(c_2825, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_2822])).
% 8.68/3.04  tff(c_2835, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2825, c_44])).
% 8.68/3.04  tff(c_2839, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_2835])).
% 8.68/3.04  tff(c_3231, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3229, c_2839])).
% 8.68/3.04  tff(c_3855, plain, (![A_404, B_405]: (k9_relat_1(k2_funct_1(A_404), k9_relat_1(A_404, B_405))=B_405 | ~r1_tarski(B_405, k1_relat_1(A_404)) | ~v2_funct_1(A_404) | ~v1_funct_1(A_404) | ~v1_relat_1(A_404))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.68/3.04  tff(c_3873, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3231, c_3855])).
% 8.68/3.04  tff(c_3888, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_110, c_104, c_14, c_3792, c_2938, c_3873])).
% 8.68/3.04  tff(c_3499, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2320, c_3470])).
% 8.68/3.04  tff(c_3955, plain, (![B_406, C_407, A_408]: (k1_xboole_0=B_406 | v1_funct_2(C_407, A_408, B_406) | k1_relset_1(A_408, B_406, C_407)!=A_408 | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_408, B_406))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.68/3.04  tff(c_3961, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_2320, c_3955])).
% 8.68/3.04  tff(c_3981, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3961])).
% 8.68/3.04  tff(c_3982, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2319, c_3981])).
% 8.68/3.04  tff(c_3989, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_3982])).
% 8.68/3.04  tff(c_3992, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70, c_3989])).
% 8.68/3.04  tff(c_3995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2394, c_110, c_104, c_3229, c_3992])).
% 8.68/3.04  tff(c_3997, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_3982])).
% 8.68/3.04  tff(c_96, plain, (![A_51]: (v1_funct_2(A_51, k1_relat_1(A_51), k2_relat_1(A_51)) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.68/3.04  tff(c_4060, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3997, c_96])).
% 8.68/3.04  tff(c_4078, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_294, c_3888, c_4060])).
% 8.68/3.04  tff(c_4080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2319, c_4078])).
% 8.68/3.04  tff(c_4081, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3789])).
% 8.68/3.04  tff(c_4122, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4081, c_8])).
% 8.68/3.04  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.68/3.04  tff(c_4118, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4081, c_4081, c_20])).
% 8.68/3.04  tff(c_2327, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_2320, c_26])).
% 8.68/3.04  tff(c_2333, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2327])).
% 8.68/3.04  tff(c_4313, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4118, c_2333])).
% 8.68/3.04  tff(c_4318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4122, c_4313])).
% 8.68/3.04  tff(c_4320, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2327])).
% 8.68/3.04  tff(c_4557, plain, (![C_452, B_453, A_454]: (~v1_xboole_0(C_452) | ~m1_subset_1(B_453, k1_zfmisc_1(C_452)) | ~r2_hidden(A_454, B_453))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_4657, plain, (![A_461, A_462]: (~v1_xboole_0(A_461) | ~r2_hidden(A_462, A_461))), inference(resolution, [status(thm)], [c_111, c_4557])).
% 8.68/3.04  tff(c_4739, plain, (![A_469, B_470]: (~v1_xboole_0(A_469) | r1_tarski(A_469, B_470))), inference(resolution, [status(thm)], [c_6, c_4657])).
% 8.68/3.04  tff(c_28, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.68/3.04  tff(c_2328, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_2320, c_28])).
% 8.68/3.04  tff(c_4321, plain, (![B_414, A_415]: (B_414=A_415 | ~r1_tarski(B_414, A_415) | ~r1_tarski(A_415, B_414))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.68/3.04  tff(c_4328, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2328, c_4321])).
% 8.68/3.04  tff(c_4556, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4328])).
% 8.68/3.04  tff(c_4742, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_4739, c_4556])).
% 8.68/3.04  tff(c_4766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4320, c_4742])).
% 8.68/3.04  tff(c_4767, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_4328])).
% 8.68/3.04  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.68/3.04  tff(c_4795, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k2_funct_1('#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4767, c_16])).
% 8.68/3.04  tff(c_4974, plain, (k2_funct_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4795])).
% 8.68/3.04  tff(c_4319, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2327])).
% 8.68/3.04  tff(c_4921, plain, (![C_481, B_482, A_483]: (~v1_xboole_0(C_481) | ~m1_subset_1(B_482, k1_zfmisc_1(C_481)) | ~r2_hidden(A_483, B_482))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_4931, plain, (![A_484, A_485]: (~v1_xboole_0(A_484) | ~r2_hidden(A_485, A_484))), inference(resolution, [status(thm)], [c_111, c_4921])).
% 8.68/3.04  tff(c_4935, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_4931])).
% 8.68/3.04  tff(c_4936, plain, (![A_486, B_487]: (~v1_xboole_0(A_486) | r1_tarski(A_486, B_487))), inference(resolution, [status(thm)], [c_6, c_4931])).
% 8.68/3.04  tff(c_5026, plain, (![B_496, A_497]: (B_496=A_497 | ~r1_tarski(B_496, A_497) | ~v1_xboole_0(A_497))), inference(resolution, [status(thm)], [c_4936, c_10])).
% 8.68/3.04  tff(c_5040, plain, (![B_498, A_499]: (B_498=A_499 | ~v1_xboole_0(B_498) | ~v1_xboole_0(A_499))), inference(resolution, [status(thm)], [c_4935, c_5026])).
% 8.68/3.04  tff(c_5053, plain, (![A_500]: (k1_xboole_0=A_500 | ~v1_xboole_0(A_500))), inference(resolution, [status(thm)], [c_8, c_5040])).
% 8.68/3.04  tff(c_5056, plain, (k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4319, c_5053])).
% 8.68/3.04  tff(c_5069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4974, c_5056])).
% 8.68/3.04  tff(c_5070, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4795])).
% 8.68/3.04  tff(c_5100, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_5070])).
% 8.68/3.04  tff(c_5132, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5100, c_8])).
% 8.68/3.04  tff(c_5128, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5100, c_5100, c_20])).
% 8.68/3.04  tff(c_297, plain, (![B_87, A_88]: (v1_xboole_0(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.68/3.04  tff(c_308, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_106, c_297])).
% 8.68/3.04  tff(c_321, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_308])).
% 8.68/3.04  tff(c_5311, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5128, c_321])).
% 8.68/3.04  tff(c_5316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5132, c_5311])).
% 8.68/3.04  tff(c_5317, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5070])).
% 8.68/3.04  tff(c_5336, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5317, c_8])).
% 8.68/3.04  tff(c_5330, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5317, c_5317, c_18])).
% 8.68/3.04  tff(c_5519, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5330, c_321])).
% 8.68/3.04  tff(c_5524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5336, c_5519])).
% 8.68/3.04  tff(c_5526, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_308])).
% 8.68/3.04  tff(c_8688, plain, (![C_870, B_871, A_872]: (~v1_xboole_0(C_870) | ~m1_subset_1(B_871, k1_zfmisc_1(C_870)) | ~r2_hidden(A_872, B_871))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_8761, plain, (![A_877, A_878]: (~v1_xboole_0(A_877) | ~r2_hidden(A_878, A_877))), inference(resolution, [status(thm)], [c_111, c_8688])).
% 8.68/3.04  tff(c_8766, plain, (![A_879, B_880]: (~v1_xboole_0(A_879) | r1_tarski(A_879, B_880))), inference(resolution, [status(thm)], [c_6, c_8761])).
% 8.68/3.04  tff(c_214, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.68/3.04  tff(c_225, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_106, c_214])).
% 8.68/3.04  tff(c_8581, plain, (![B_856, A_857]: (B_856=A_857 | ~r1_tarski(B_856, A_857) | ~r1_tarski(A_857, B_856))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.68/3.04  tff(c_8589, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_225, c_8581])).
% 8.68/3.04  tff(c_8640, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_8589])).
% 8.68/3.04  tff(c_8773, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8766, c_8640])).
% 8.68/3.04  tff(c_8787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5526, c_8773])).
% 8.68/3.04  tff(c_8788, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_8589])).
% 8.68/3.04  tff(c_8805, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8788, c_16])).
% 8.68/3.04  tff(c_8855, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_8805])).
% 8.68/3.04  tff(c_5525, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_308])).
% 8.68/3.04  tff(c_7483, plain, (![C_771, B_772, A_773]: (~v1_xboole_0(C_771) | ~m1_subset_1(B_772, k1_zfmisc_1(C_771)) | ~r2_hidden(A_773, B_772))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_7526, plain, (![A_776, A_777]: (~v1_xboole_0(A_776) | ~r2_hidden(A_777, A_776))), inference(resolution, [status(thm)], [c_111, c_7483])).
% 8.68/3.04  tff(c_7530, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_7526])).
% 8.68/3.04  tff(c_7489, plain, (![A_773]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_773, '#skF_4'))), inference(resolution, [status(thm)], [c_106, c_7483])).
% 8.68/3.04  tff(c_7498, plain, (![A_774]: (~r2_hidden(A_774, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5526, c_7489])).
% 8.68/3.04  tff(c_7505, plain, (![B_775]: (r1_tarski('#skF_4', B_775))), inference(resolution, [status(thm)], [c_6, c_7498])).
% 8.68/3.04  tff(c_7549, plain, (![B_780]: (B_780='#skF_4' | ~r1_tarski(B_780, '#skF_4'))), inference(resolution, [status(thm)], [c_7505, c_10])).
% 8.68/3.04  tff(c_7567, plain, (![A_781]: (A_781='#skF_4' | ~v1_xboole_0(A_781))), inference(resolution, [status(thm)], [c_7530, c_7549])).
% 8.68/3.04  tff(c_7588, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_7567])).
% 8.68/3.04  tff(c_7621, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7588, c_7588, c_20])).
% 8.68/3.04  tff(c_7619, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7588, c_7588, c_18])).
% 8.68/3.04  tff(c_7583, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_5526, c_7567])).
% 8.68/3.04  tff(c_8459, plain, (![B_853, A_854]: (B_853='#skF_4' | A_854='#skF_4' | k2_zfmisc_1(A_854, B_853)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7588, c_7588, c_7588, c_16])).
% 8.68/3.04  tff(c_8473, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7583, c_8459])).
% 8.68/3.04  tff(c_8529, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_8473])).
% 8.68/3.04  tff(c_34, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.68/3.04  tff(c_5533, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5525, c_34])).
% 8.68/3.04  tff(c_6828, plain, (![C_685, B_686, A_687]: (~v1_xboole_0(C_685) | ~m1_subset_1(B_686, k1_zfmisc_1(C_685)) | ~r2_hidden(A_687, B_686))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_6835, plain, (![A_688, A_689]: (~v1_xboole_0(A_688) | ~r2_hidden(A_689, A_688))), inference(resolution, [status(thm)], [c_111, c_6828])).
% 8.68/3.04  tff(c_6839, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_6835])).
% 8.68/3.04  tff(c_6840, plain, (![A_690, B_691]: (~v1_xboole_0(A_690) | r1_tarski(A_690, B_691))), inference(resolution, [status(thm)], [c_6, c_6835])).
% 8.68/3.04  tff(c_6863, plain, (![B_694, A_695]: (B_694=A_695 | ~r1_tarski(B_694, A_695) | ~v1_xboole_0(A_695))), inference(resolution, [status(thm)], [c_6840, c_10])).
% 8.68/3.04  tff(c_6873, plain, (![B_696, A_697]: (B_696=A_697 | ~v1_xboole_0(B_696) | ~v1_xboole_0(A_697))), inference(resolution, [status(thm)], [c_6839, c_6863])).
% 8.68/3.04  tff(c_6883, plain, (![A_698]: (A_698='#skF_4' | ~v1_xboole_0(A_698))), inference(resolution, [status(thm)], [c_5525, c_6873])).
% 8.68/3.04  tff(c_6911, plain, (![A_700]: (k4_relat_1(A_700)='#skF_4' | ~v1_xboole_0(A_700))), inference(resolution, [status(thm)], [c_40, c_6883])).
% 8.68/3.04  tff(c_6921, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5525, c_6911])).
% 8.68/3.04  tff(c_7313, plain, (![A_749]: (k4_relat_1(A_749)=k2_funct_1(A_749) | ~v2_funct_1(A_749) | ~v1_funct_1(A_749) | ~v1_relat_1(A_749))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.68/3.04  tff(c_7319, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_7313])).
% 8.68/3.04  tff(c_7323, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5533, c_110, c_6921, c_7319])).
% 8.68/3.04  tff(c_5725, plain, (![C_545, B_546, A_547]: (~v1_xboole_0(C_545) | ~m1_subset_1(B_546, k1_zfmisc_1(C_545)) | ~r2_hidden(A_547, B_546))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_5765, plain, (![A_550, A_551]: (~v1_xboole_0(A_550) | ~r2_hidden(A_551, A_550))), inference(resolution, [status(thm)], [c_111, c_5725])).
% 8.68/3.04  tff(c_5783, plain, (![A_553, B_554]: (~v1_xboole_0(A_553) | r1_tarski(A_553, B_554))), inference(resolution, [status(thm)], [c_6, c_5765])).
% 8.68/3.04  tff(c_5567, plain, (![B_517, A_518]: (B_517=A_518 | ~r1_tarski(B_517, A_518) | ~r1_tarski(A_518, B_517))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.68/3.04  tff(c_5572, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_225, c_5567])).
% 8.68/3.04  tff(c_5623, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5572])).
% 8.68/3.04  tff(c_5798, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5783, c_5623])).
% 8.68/3.04  tff(c_5813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5526, c_5798])).
% 8.68/3.04  tff(c_5814, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_5572])).
% 8.68/3.04  tff(c_5831, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5814, c_16])).
% 8.68/3.04  tff(c_5857, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_5831])).
% 8.68/3.04  tff(c_5891, plain, (![C_565, B_566, A_567]: (~v1_xboole_0(C_565) | ~m1_subset_1(B_566, k1_zfmisc_1(C_565)) | ~r2_hidden(A_567, B_566))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_5898, plain, (![A_568, A_569]: (~v1_xboole_0(A_568) | ~r2_hidden(A_569, A_568))), inference(resolution, [status(thm)], [c_111, c_5891])).
% 8.68/3.04  tff(c_5902, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_5898])).
% 8.68/3.04  tff(c_5935, plain, (![A_576, B_577]: (~v1_xboole_0(A_576) | r1_tarski(A_576, B_577))), inference(resolution, [status(thm)], [c_6, c_5898])).
% 8.68/3.04  tff(c_5977, plain, (![B_585, A_586]: (B_585=A_586 | ~r1_tarski(B_585, A_586) | ~v1_xboole_0(A_586))), inference(resolution, [status(thm)], [c_5935, c_10])).
% 8.68/3.04  tff(c_5987, plain, (![B_587, A_588]: (B_587=A_588 | ~v1_xboole_0(B_587) | ~v1_xboole_0(A_588))), inference(resolution, [status(thm)], [c_5902, c_5977])).
% 8.68/3.04  tff(c_6000, plain, (![A_589]: (A_589='#skF_4' | ~v1_xboole_0(A_589))), inference(resolution, [status(thm)], [c_5525, c_5987])).
% 8.68/3.04  tff(c_6012, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_6000])).
% 8.68/3.04  tff(c_6020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5857, c_6012])).
% 8.68/3.04  tff(c_6022, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5831])).
% 8.68/3.04  tff(c_6040, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6022, c_6022, c_18])).
% 8.68/3.04  tff(c_6144, plain, (![C_597, B_598, A_599]: (~v1_xboole_0(C_597) | ~m1_subset_1(B_598, k1_zfmisc_1(C_597)) | ~r2_hidden(A_599, B_598))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_6151, plain, (![A_600, A_601]: (~v1_xboole_0(A_600) | ~r2_hidden(A_601, A_600))), inference(resolution, [status(thm)], [c_111, c_6144])).
% 8.68/3.04  tff(c_6155, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_6151])).
% 8.68/3.04  tff(c_6156, plain, (![A_602, B_603]: (~v1_xboole_0(A_602) | r1_tarski(A_602, B_603))), inference(resolution, [status(thm)], [c_6, c_6151])).
% 8.68/3.04  tff(c_6195, plain, (![B_607, A_608]: (B_607=A_608 | ~r1_tarski(B_607, A_608) | ~v1_xboole_0(A_608))), inference(resolution, [status(thm)], [c_6156, c_10])).
% 8.68/3.04  tff(c_6205, plain, (![B_609, A_610]: (B_609=A_610 | ~v1_xboole_0(B_609) | ~v1_xboole_0(A_610))), inference(resolution, [status(thm)], [c_6155, c_6195])).
% 8.68/3.04  tff(c_6215, plain, (![A_611]: (A_611='#skF_4' | ~v1_xboole_0(A_611))), inference(resolution, [status(thm)], [c_5525, c_6205])).
% 8.68/3.04  tff(c_6255, plain, (![A_618]: (k4_relat_1(A_618)='#skF_4' | ~v1_xboole_0(A_618))), inference(resolution, [status(thm)], [c_40, c_6215])).
% 8.68/3.04  tff(c_6265, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5525, c_6255])).
% 8.68/3.04  tff(c_6718, plain, (![A_672]: (k4_relat_1(A_672)=k2_funct_1(A_672) | ~v2_funct_1(A_672) | ~v1_funct_1(A_672) | ~v1_relat_1(A_672))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.68/3.04  tff(c_6724, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_6718])).
% 8.68/3.04  tff(c_6728, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5533, c_110, c_6265, c_6724])).
% 8.68/3.04  tff(c_6042, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6022, c_6022, c_20])).
% 8.68/3.04  tff(c_6021, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5831])).
% 8.68/3.04  tff(c_6094, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6022, c_6022, c_6021])).
% 8.68/3.04  tff(c_6095, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_6094])).
% 8.68/3.04  tff(c_5551, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_293])).
% 8.68/3.04  tff(c_5555, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_5551])).
% 8.68/3.04  tff(c_6098, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6095, c_5555])).
% 8.68/3.04  tff(c_6169, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6042, c_6098])).
% 8.68/3.04  tff(c_6173, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6155, c_6169])).
% 8.68/3.04  tff(c_6729, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6728, c_6173])).
% 8.68/3.04  tff(c_6735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5525, c_6729])).
% 8.68/3.04  tff(c_6736, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_6094])).
% 8.68/3.04  tff(c_6739, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6736, c_5555])).
% 8.68/3.04  tff(c_6743, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6040, c_6739])).
% 8.68/3.04  tff(c_6859, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6840, c_6743])).
% 8.68/3.04  tff(c_7324, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7323, c_6859])).
% 8.68/3.04  tff(c_7330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5525, c_7324])).
% 8.68/3.04  tff(c_7332, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_293])).
% 8.68/3.04  tff(c_7339, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_7332, c_26])).
% 8.68/3.04  tff(c_7356, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7339])).
% 8.68/3.04  tff(c_8536, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8529, c_7356])).
% 8.68/3.04  tff(c_8543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5525, c_7619, c_8536])).
% 8.68/3.04  tff(c_8544, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_8473])).
% 8.68/3.04  tff(c_8552, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_7356])).
% 8.68/3.04  tff(c_8559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5525, c_7621, c_8552])).
% 8.68/3.04  tff(c_8561, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_7339])).
% 8.68/3.04  tff(c_8893, plain, (![C_891, B_892, A_893]: (~v1_xboole_0(C_891) | ~m1_subset_1(B_892, k1_zfmisc_1(C_891)) | ~r2_hidden(A_893, B_892))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_8895, plain, (![A_893]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_893, k2_funct_1('#skF_4')))), inference(resolution, [status(thm)], [c_7332, c_8893])).
% 8.68/3.04  tff(c_8905, plain, (![A_894]: (~r2_hidden(A_894, k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8561, c_8895])).
% 8.68/3.04  tff(c_8910, plain, (![B_2]: (r1_tarski(k2_funct_1('#skF_4'), B_2))), inference(resolution, [status(thm)], [c_6, c_8905])).
% 8.68/3.04  tff(c_9006, plain, (![A_903, A_904]: (~v1_xboole_0(A_903) | ~r2_hidden(A_904, A_903))), inference(resolution, [status(thm)], [c_111, c_8893])).
% 8.68/3.04  tff(c_9031, plain, (![A_905, B_906]: (~v1_xboole_0(A_905) | r1_tarski(A_905, B_906))), inference(resolution, [status(thm)], [c_6, c_9006])).
% 8.68/3.04  tff(c_9085, plain, (![B_909, A_910]: (B_909=A_910 | ~r1_tarski(B_909, A_910) | ~v1_xboole_0(A_910))), inference(resolution, [status(thm)], [c_9031, c_10])).
% 8.68/3.04  tff(c_9099, plain, (![B_911]: (k2_funct_1('#skF_4')=B_911 | ~v1_xboole_0(B_911))), inference(resolution, [status(thm)], [c_8910, c_9085])).
% 8.68/3.04  tff(c_9117, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5525, c_9099])).
% 8.68/3.04  tff(c_9120, plain, (k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_9099])).
% 8.68/3.04  tff(c_9168, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9117, c_9120])).
% 8.68/3.04  tff(c_9169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8855, c_9168])).
% 8.68/3.04  tff(c_9171, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8805])).
% 8.68/3.04  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.68/3.04  tff(c_9182, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_9171, c_50])).
% 8.68/3.04  tff(c_9179, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_9171, c_20])).
% 8.68/3.04  tff(c_11778, plain, (![A_1152, B_1153, C_1154]: (k1_relset_1(A_1152, B_1153, C_1154)=k1_relat_1(C_1154) | ~m1_subset_1(C_1154, k1_zfmisc_1(k2_zfmisc_1(A_1152, B_1153))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.68/3.04  tff(c_11795, plain, (![A_1155, B_1156]: (k1_relset_1(A_1155, B_1156, k2_zfmisc_1(A_1155, B_1156))=k1_relat_1(k2_zfmisc_1(A_1155, B_1156)))), inference(resolution, [status(thm)], [c_111, c_11778])).
% 8.68/3.04  tff(c_11804, plain, (![B_9]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_9))=k1_relset_1('#skF_4', B_9, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9179, c_11795])).
% 8.68/3.04  tff(c_11810, plain, (![B_9]: (k1_relset_1('#skF_4', B_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9182, c_9179, c_11804])).
% 8.68/3.04  tff(c_86, plain, (![C_50, B_49]: (v1_funct_2(C_50, k1_xboole_0, B_49) | k1_relset_1(k1_xboole_0, B_49, C_50)!=k1_xboole_0 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_49))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.68/3.04  tff(c_112, plain, (![C_50, B_49]: (v1_funct_2(C_50, k1_xboole_0, B_49) | k1_relset_1(k1_xboole_0, B_49, C_50)!=k1_xboole_0 | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_86])).
% 8.68/3.04  tff(c_12945, plain, (![C_1216, B_1217]: (v1_funct_2(C_1216, '#skF_4', B_1217) | k1_relset_1('#skF_4', B_1217, C_1216)!='#skF_4' | ~m1_subset_1(C_1216, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_9171, c_9171, c_9171, c_112])).
% 8.68/3.04  tff(c_12951, plain, (![B_1217]: (v1_funct_2('#skF_4', '#skF_4', B_1217) | k1_relset_1('#skF_4', B_1217, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_111, c_12945])).
% 8.68/3.04  tff(c_12955, plain, (![B_1217]: (v1_funct_2('#skF_4', '#skF_4', B_1217))), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_12951])).
% 8.68/3.04  tff(c_9170, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8805])).
% 8.68/3.04  tff(c_9982, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_9171, c_9170])).
% 8.68/3.04  tff(c_9983, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_9982])).
% 8.68/3.04  tff(c_9903, plain, (![C_1005, B_1006, A_1007]: (~v1_xboole_0(C_1005) | ~m1_subset_1(B_1006, k1_zfmisc_1(C_1005)) | ~r2_hidden(A_1007, B_1006))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_9943, plain, (![A_1010, A_1011]: (~v1_xboole_0(A_1010) | ~r2_hidden(A_1011, A_1010))), inference(resolution, [status(thm)], [c_111, c_9903])).
% 8.68/3.04  tff(c_9948, plain, (![A_1012, B_1013]: (~v1_xboole_0(A_1012) | r1_tarski(A_1012, B_1013))), inference(resolution, [status(thm)], [c_6, c_9943])).
% 8.68/3.04  tff(c_9177, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_9171, c_18])).
% 8.68/3.04  tff(c_9592, plain, (![C_967, B_968, A_969]: (~v1_xboole_0(C_967) | ~m1_subset_1(B_968, k1_zfmisc_1(C_967)) | ~r2_hidden(A_969, B_968))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.68/3.04  tff(c_9644, plain, (![A_972, A_973]: (~v1_xboole_0(A_972) | ~r2_hidden(A_973, A_972))), inference(resolution, [status(thm)], [c_111, c_9592])).
% 8.68/3.04  tff(c_9649, plain, (![A_974, B_975]: (~v1_xboole_0(A_974) | r1_tarski(A_974, B_975))), inference(resolution, [status(thm)], [c_6, c_9644])).
% 8.68/3.04  tff(c_9220, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_9171, c_9170])).
% 8.68/3.04  tff(c_9221, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_9220])).
% 8.68/3.04  tff(c_7340, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_7332, c_28])).
% 8.68/3.04  tff(c_8588, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7340, c_8581])).
% 8.68/3.04  tff(c_9210, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8588])).
% 8.68/3.04  tff(c_9279, plain, (~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9179, c_9221, c_9210])).
% 8.68/3.04  tff(c_9664, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_9649, c_9279])).
% 8.68/3.04  tff(c_9680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5525, c_9664])).
% 8.68/3.04  tff(c_9681, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_9220])).
% 8.68/3.04  tff(c_9766, plain, (~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9177, c_9681, c_9210])).
% 8.68/3.04  tff(c_9955, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_9948, c_9766])).
% 8.68/3.04  tff(c_9969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5525, c_9955])).
% 8.68/3.04  tff(c_9970, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_8588])).
% 8.68/3.04  tff(c_10066, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9179, c_9983, c_9970])).
% 8.68/3.04  tff(c_7331, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_293])).
% 8.68/3.04  tff(c_9989, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9983, c_7331])).
% 8.68/3.04  tff(c_10087, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10066, c_9989])).
% 8.68/3.04  tff(c_12959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12955, c_10087])).
% 8.68/3.04  tff(c_12961, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_9982])).
% 8.68/3.04  tff(c_82, plain, (![A_48]: (v1_funct_2(k1_xboole_0, A_48, k1_xboole_0) | k1_xboole_0=A_48 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_48, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.68/3.04  tff(c_115, plain, (![A_48]: (v1_funct_2(k1_xboole_0, A_48, k1_xboole_0) | k1_xboole_0=A_48 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_82])).
% 8.68/3.04  tff(c_117, plain, (![A_48]: (v1_funct_2(k1_xboole_0, A_48, k1_xboole_0) | k1_xboole_0=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_115])).
% 8.68/3.04  tff(c_13073, plain, (![A_1229]: (v1_funct_2('#skF_4', A_1229, '#skF_4') | A_1229='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_9171, c_9171, c_117])).
% 8.68/3.04  tff(c_12960, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_9982])).
% 8.68/3.04  tff(c_13045, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9177, c_12960, c_9970])).
% 8.68/3.04  tff(c_12967, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12960, c_7331])).
% 8.68/3.04  tff(c_13066, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13045, c_12967])).
% 8.68/3.04  tff(c_13076, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_13073, c_13066])).
% 8.68/3.04  tff(c_13080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12961, c_13076])).
% 8.68/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.68/3.04  
% 8.68/3.04  Inference rules
% 8.68/3.04  ----------------------
% 8.68/3.04  #Ref     : 0
% 8.68/3.04  #Sup     : 3048
% 8.68/3.04  #Fact    : 0
% 8.68/3.04  #Define  : 0
% 8.68/3.04  #Split   : 40
% 8.68/3.04  #Chain   : 0
% 8.68/3.04  #Close   : 0
% 8.68/3.04  
% 8.68/3.04  Ordering : KBO
% 8.68/3.04  
% 8.68/3.04  Simplification rules
% 8.68/3.04  ----------------------
% 8.68/3.04  #Subsume      : 446
% 8.68/3.04  #Demod        : 2380
% 8.68/3.04  #Tautology    : 1432
% 8.68/3.04  #SimpNegUnit  : 14
% 8.68/3.04  #BackRed      : 358
% 8.68/3.04  
% 8.68/3.04  #Partial instantiations: 0
% 8.68/3.04  #Strategies tried      : 1
% 8.68/3.04  
% 8.68/3.04  Timing (in seconds)
% 8.68/3.04  ----------------------
% 8.68/3.04  Preprocessing        : 0.36
% 8.68/3.04  Parsing              : 0.19
% 8.68/3.04  CNF conversion       : 0.03
% 8.68/3.04  Main loop            : 1.76
% 8.68/3.04  Inferencing          : 0.60
% 8.68/3.04  Reduction            : 0.58
% 8.68/3.04  Demodulation         : 0.41
% 8.68/3.04  BG Simplification    : 0.06
% 8.68/3.04  Subsumption          : 0.36
% 8.68/3.04  Abstraction          : 0.08
% 8.68/3.04  MUC search           : 0.00
% 8.68/3.04  Cooper               : 0.00
% 8.68/3.04  Total                : 2.26
% 8.68/3.04  Index Insertion      : 0.00
% 8.68/3.04  Index Deletion       : 0.00
% 8.68/3.04  Index Matching       : 0.00
% 8.68/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
