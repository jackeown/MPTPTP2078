%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:26 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :  216 (1090 expanded)
%              Number of leaves         :   45 ( 383 expanded)
%              Depth                    :   12
%              Number of atoms          :  381 (3118 expanded)
%              Number of equality atoms :   94 ( 607 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
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

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_166,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_124,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_3696,plain,(
    ! [C_274,A_275,B_276] :
      ( v1_relat_1(C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3708,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_3696])).

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_90,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_88,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4166,plain,(
    ! [A_345,B_346,C_347] :
      ( k2_relset_1(A_345,B_346,C_347) = k2_relat_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4172,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_4166])).

tff(c_4181,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4172])).

tff(c_50,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_368,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_376,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_368])).

tff(c_616,plain,(
    ! [A_121] :
      ( k4_relat_1(A_121) = k2_funct_1(A_121)
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_622,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_616])).

tff(c_626,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_96,c_622])).

tff(c_26,plain,(
    ! [A_16] :
      ( v1_relat_1(k4_relat_1(A_16))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_636,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_26])).

tff(c_644,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_636])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_773,plain,(
    ! [A_142,B_143,C_144] :
      ( k1_relset_1(A_142,B_143,C_144) = k1_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_783,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_773])).

tff(c_1362,plain,(
    ! [B_186,A_187,C_188] :
      ( k1_xboole_0 = B_186
      | k1_relset_1(A_187,B_186,C_188) = A_187
      | ~ v1_funct_2(C_188,A_187,B_186)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1368,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_1362])).

tff(c_1378,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_783,c_1368])).

tff(c_1380,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1378])).

tff(c_48,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_252,plain,(
    ! [A_58] :
      ( v1_funct_1(k2_funct_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_86,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_217,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_255,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_252,c_217])).

tff(c_258,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_255])).

tff(c_283,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_286,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_283])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_286])).

tff(c_296,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_745,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_748,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_745])).

tff(c_756,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_748])).

tff(c_853,plain,(
    ! [B_158,A_159] :
      ( v1_funct_2(B_158,k1_relat_1(B_158),A_159)
      | ~ r1_tarski(k2_relat_1(B_158),A_159)
      | ~ v1_funct_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2879,plain,(
    ! [A_227,A_228] :
      ( v1_funct_2(k2_funct_1(A_227),k2_relat_1(A_227),A_228)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_227)),A_228)
      | ~ v1_funct_1(k2_funct_1(A_227))
      | ~ v1_relat_1(k2_funct_1(A_227))
      | ~ v2_funct_1(A_227)
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_853])).

tff(c_2903,plain,(
    ! [A_228] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_228)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_228)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_2879])).

tff(c_2915,plain,(
    ! [A_228] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_228)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_228)
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_96,c_90,c_296,c_2903])).

tff(c_2920,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2915])).

tff(c_2923,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2920])).

tff(c_2927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_96,c_2923])).

tff(c_2929,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2915])).

tff(c_907,plain,(
    ! [B_167,A_168] :
      ( m1_subset_1(B_167,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_167),A_168)))
      | ~ r1_tarski(k2_relat_1(B_167),A_168)
      | ~ v1_funct_1(B_167)
      | ~ v1_relat_1(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2952,plain,(
    ! [A_231,A_232] :
      ( m1_subset_1(k2_funct_1(A_231),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_231),A_232)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_231)),A_232)
      | ~ v1_funct_1(k2_funct_1(A_231))
      | ~ v1_relat_1(k2_funct_1(A_231))
      | ~ v2_funct_1(A_231)
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_907])).

tff(c_2993,plain,(
    ! [A_232] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_232)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_232)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_2952])).

tff(c_3020,plain,(
    ! [A_233] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_233)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_96,c_90,c_2929,c_296,c_2993])).

tff(c_295,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_297,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_3056,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_3020,c_297])).

tff(c_3059,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_3056])).

tff(c_3062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_96,c_90,c_12,c_1380,c_3059])).

tff(c_3063,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_939,plain,(
    ! [B_169] :
      ( m1_subset_1(B_169,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_169),k1_xboole_0)
      | ~ v1_funct_1(B_169)
      | ~ v1_relat_1(B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_907])).

tff(c_942,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_939])).

tff(c_950,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_96,c_942])).

tff(c_953,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_950])).

tff(c_3071,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_953])).

tff(c_3108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3071])).

tff(c_3110,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_345,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_354,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_345])).

tff(c_3117,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3110,c_354])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [B_54,A_55] :
      ( ~ r1_tarski(B_54,A_55)
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_173,plain,(
    ! [A_56] :
      ( ~ r1_tarski(A_56,'#skF_1'(A_56))
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_4,c_168])).

tff(c_178,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_173])).

tff(c_3144,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3117,c_178])).

tff(c_3109,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_3283,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3117,c_3109])).

tff(c_645,plain,(
    ! [C_122,A_123,B_124] :
      ( r2_hidden(C_122,A_123)
      | ~ r2_hidden(C_122,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_688,plain,(
    ! [A_127,A_128] :
      ( r2_hidden('#skF_1'(A_127),A_128)
      | ~ m1_subset_1(A_127,k1_zfmisc_1(A_128))
      | v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_4,c_645])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_699,plain,(
    ! [A_128,A_127] :
      ( ~ v1_xboole_0(A_128)
      | ~ m1_subset_1(A_127,k1_zfmisc_1(A_128))
      | v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_688,c_2])).

tff(c_3288,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3283,c_699])).

tff(c_3292,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3144,c_3288])).

tff(c_3294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_644,c_3292])).

tff(c_3296,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_636])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3335,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3296,c_6])).

tff(c_68,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_100,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_379,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_56,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_577,plain,(
    ! [B_118,A_119] :
      ( m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_118),A_119)))
      | ~ r1_tarski(k2_relat_1(B_118),A_119)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_599,plain,(
    ! [A_119] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_119)))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),A_119)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_577])).

tff(c_605,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_14,c_30,c_20,c_599])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_605])).

tff(c_609,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_3340,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_3335,c_609])).

tff(c_3349,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_3335,c_20])).

tff(c_3353,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_3335,c_30])).

tff(c_3638,plain,(
    ! [A_268,B_269,C_270] :
      ( k2_relset_1(A_268,B_269,C_270) = k2_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3647,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_3638])).

tff(c_3649,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3353,c_88,c_3647])).

tff(c_139,plain,(
    ! [A_49] :
      ( v1_xboole_0(k4_relat_1(A_49))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_150,plain,(
    ! [A_49] :
      ( k4_relat_1(A_49) = k1_xboole_0
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_139,c_6])).

tff(c_3332,plain,(
    k4_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3296,c_150])).

tff(c_3400,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_3332])).

tff(c_3401,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3400,c_626])).

tff(c_3434,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_297])).

tff(c_3651,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3649,c_3434])).

tff(c_3657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3340,c_3349,c_3651])).

tff(c_3658,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_3659,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_4099,plain,(
    ! [A_334,B_335,C_336] :
      ( k1_relset_1(A_334,B_335,C_336) = k1_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4112,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3659,c_4099])).

tff(c_4345,plain,(
    ! [B_372,C_373,A_374] :
      ( k1_xboole_0 = B_372
      | v1_funct_2(C_373,A_374,B_372)
      | k1_relset_1(A_374,B_372,C_373) != A_374
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_374,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4351,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3659,c_4345])).

tff(c_4363,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4112,c_4351])).

tff(c_4364,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3658,c_4363])).

tff(c_4368,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4364])).

tff(c_4371,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4368])).

tff(c_4374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3708,c_96,c_90,c_4181,c_4371])).

tff(c_4375,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4364])).

tff(c_4401,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4375,c_178])).

tff(c_4405,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4375,c_4375,c_18])).

tff(c_3983,plain,(
    ! [C_323,A_324,B_325] :
      ( r2_hidden(C_323,A_324)
      | ~ r2_hidden(C_323,B_325)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(A_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4070,plain,(
    ! [A_330,A_331] :
      ( r2_hidden('#skF_1'(A_330),A_331)
      | ~ m1_subset_1(A_330,k1_zfmisc_1(A_331))
      | v1_xboole_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_4,c_3983])).

tff(c_4082,plain,(
    ! [A_332,A_333] :
      ( ~ v1_xboole_0(A_332)
      | ~ m1_subset_1(A_333,k1_zfmisc_1(A_332))
      | v1_xboole_0(A_333) ) ),
    inference(resolution,[status(thm)],[c_4070,c_2])).

tff(c_4095,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
    | v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3659,c_4082])).

tff(c_4118,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4095])).

tff(c_4544,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4405,c_4118])).

tff(c_4548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_4544])).

tff(c_4549,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4095])).

tff(c_4579,plain,(
    k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4549,c_6])).

tff(c_4594,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4579,c_50])).

tff(c_4607,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3708,c_96,c_90,c_32,c_4594])).

tff(c_4665,plain,(
    ! [A_383,B_384,C_385] :
      ( k2_relset_1(A_383,B_384,C_385) = k2_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4668,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_4665])).

tff(c_4676,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4607,c_88,c_4668])).

tff(c_4691,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4676,c_178])).

tff(c_4695,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4676,c_4676,c_18])).

tff(c_3987,plain,(
    ! [A_326] :
      ( k4_relat_1(A_326) = k2_funct_1(A_326)
      | ~ v2_funct_1(A_326)
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3993,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_3987])).

tff(c_3997,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3708,c_96,c_3993])).

tff(c_28,plain,(
    ! [A_16] :
      ( v1_xboole_0(k4_relat_1(A_16))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4010,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3997,c_28])).

tff(c_4025,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4010])).

tff(c_4091,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_4082])).

tff(c_4098,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_4025,c_4091])).

tff(c_4920,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4695,c_4098])).

tff(c_4924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4691,c_4920])).

tff(c_4926,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4010])).

tff(c_4951,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4926,c_6])).

tff(c_4969,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4951,c_14])).

tff(c_4968,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4951,c_4951,c_30])).

tff(c_4967,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4951,c_4951,c_32])).

tff(c_5252,plain,(
    ! [B_415,A_416] :
      ( v1_funct_2(B_415,k1_relat_1(B_415),A_416)
      | ~ r1_tarski(k2_relat_1(B_415),A_416)
      | ~ v1_funct_1(B_415)
      | ~ v1_relat_1(B_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_5258,plain,(
    ! [A_416] :
      ( v1_funct_2('#skF_4','#skF_4',A_416)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_416)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4967,c_5252])).

tff(c_5264,plain,(
    ! [A_416] : v1_funct_2('#skF_4','#skF_4',A_416) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3708,c_96,c_4969,c_4968,c_5258])).

tff(c_4948,plain,(
    k4_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4926,c_150])).

tff(c_5023,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4951,c_4948])).

tff(c_5024,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5023,c_3997])).

tff(c_5044,plain,(
    ! [A_397,B_398,C_399] :
      ( k2_relset_1(A_397,B_398,C_399) = k2_relat_1(C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5050,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_5044])).

tff(c_5053,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4968,c_88,c_5050])).

tff(c_5055,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5053,c_3658])).

tff(c_5168,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5024,c_5055])).

tff(c_5267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5264,c_5168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.57/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.29  
% 6.69/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.30  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.69/2.30  
% 6.69/2.30  %Foreground sorts:
% 6.69/2.30  
% 6.69/2.30  
% 6.69/2.30  %Background operators:
% 6.69/2.30  
% 6.69/2.30  
% 6.69/2.30  %Foreground operators:
% 6.69/2.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.69/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.69/2.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.69/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.69/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.69/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.69/2.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.69/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.69/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.69/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.69/2.30  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 6.69/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.69/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.69/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.69/2.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.69/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.69/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.69/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.69/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.69/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.69/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.69/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.69/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.69/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.69/2.30  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.69/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.69/2.30  
% 6.69/2.32  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.69/2.32  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.69/2.32  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.69/2.32  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.69/2.32  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.69/2.32  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.69/2.32  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 6.69/2.32  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.69/2.32  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.69/2.32  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.69/2.32  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.69/2.32  tff(f_166, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.69/2.32  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.69/2.32  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.69/2.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.69/2.32  tff(f_124, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.69/2.32  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.69/2.32  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.69/2.32  tff(f_119, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 6.69/2.32  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.69/2.32  tff(c_3696, plain, (![C_274, A_275, B_276]: (v1_relat_1(C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.69/2.32  tff(c_3708, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_3696])).
% 6.69/2.32  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.69/2.32  tff(c_90, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.69/2.32  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.69/2.32  tff(c_88, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.69/2.32  tff(c_4166, plain, (![A_345, B_346, C_347]: (k2_relset_1(A_345, B_346, C_347)=k2_relat_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.69/2.32  tff(c_4172, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_4166])).
% 6.69/2.32  tff(c_4181, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4172])).
% 6.69/2.32  tff(c_50, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.69/2.32  tff(c_368, plain, (![C_74, A_75, B_76]: (v1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.69/2.32  tff(c_376, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_368])).
% 6.69/2.32  tff(c_616, plain, (![A_121]: (k4_relat_1(A_121)=k2_funct_1(A_121) | ~v2_funct_1(A_121) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.69/2.32  tff(c_622, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_616])).
% 6.69/2.32  tff(c_626, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_96, c_622])).
% 6.69/2.32  tff(c_26, plain, (![A_16]: (v1_relat_1(k4_relat_1(A_16)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.69/2.32  tff(c_636, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_626, c_26])).
% 6.69/2.32  tff(c_644, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_636])).
% 6.69/2.32  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.69/2.32  tff(c_94, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.69/2.32  tff(c_773, plain, (![A_142, B_143, C_144]: (k1_relset_1(A_142, B_143, C_144)=k1_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.69/2.32  tff(c_783, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_773])).
% 6.69/2.32  tff(c_1362, plain, (![B_186, A_187, C_188]: (k1_xboole_0=B_186 | k1_relset_1(A_187, B_186, C_188)=A_187 | ~v1_funct_2(C_188, A_187, B_186) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.69/2.32  tff(c_1368, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_92, c_1362])).
% 6.69/2.32  tff(c_1378, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_783, c_1368])).
% 6.69/2.32  tff(c_1380, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1378])).
% 6.69/2.32  tff(c_48, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.69/2.32  tff(c_46, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.69/2.32  tff(c_252, plain, (![A_58]: (v1_funct_1(k2_funct_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.69/2.32  tff(c_86, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.69/2.32  tff(c_217, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_86])).
% 6.69/2.32  tff(c_255, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_252, c_217])).
% 6.69/2.32  tff(c_258, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_255])).
% 6.69/2.32  tff(c_283, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.69/2.32  tff(c_286, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_283])).
% 6.69/2.32  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_286])).
% 6.69/2.32  tff(c_296, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_86])).
% 6.69/2.32  tff(c_745, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.69/2.32  tff(c_748, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_745])).
% 6.69/2.32  tff(c_756, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_748])).
% 6.69/2.32  tff(c_853, plain, (![B_158, A_159]: (v1_funct_2(B_158, k1_relat_1(B_158), A_159) | ~r1_tarski(k2_relat_1(B_158), A_159) | ~v1_funct_1(B_158) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.69/2.32  tff(c_2879, plain, (![A_227, A_228]: (v1_funct_2(k2_funct_1(A_227), k2_relat_1(A_227), A_228) | ~r1_tarski(k2_relat_1(k2_funct_1(A_227)), A_228) | ~v1_funct_1(k2_funct_1(A_227)) | ~v1_relat_1(k2_funct_1(A_227)) | ~v2_funct_1(A_227) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(superposition, [status(thm), theory('equality')], [c_50, c_853])).
% 6.69/2.32  tff(c_2903, plain, (![A_228]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_228) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_228) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_756, c_2879])).
% 6.69/2.32  tff(c_2915, plain, (![A_228]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_228) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_228) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_96, c_90, c_296, c_2903])).
% 6.69/2.32  tff(c_2920, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2915])).
% 6.69/2.32  tff(c_2923, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2920])).
% 6.69/2.32  tff(c_2927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_96, c_2923])).
% 6.69/2.32  tff(c_2929, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2915])).
% 6.69/2.32  tff(c_907, plain, (![B_167, A_168]: (m1_subset_1(B_167, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_167), A_168))) | ~r1_tarski(k2_relat_1(B_167), A_168) | ~v1_funct_1(B_167) | ~v1_relat_1(B_167))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.69/2.32  tff(c_2952, plain, (![A_231, A_232]: (m1_subset_1(k2_funct_1(A_231), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_231), A_232))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_231)), A_232) | ~v1_funct_1(k2_funct_1(A_231)) | ~v1_relat_1(k2_funct_1(A_231)) | ~v2_funct_1(A_231) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(superposition, [status(thm), theory('equality')], [c_50, c_907])).
% 6.69/2.32  tff(c_2993, plain, (![A_232]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_232))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_232) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_756, c_2952])).
% 6.69/2.32  tff(c_3020, plain, (![A_233]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_233))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_233))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_96, c_90, c_2929, c_296, c_2993])).
% 6.69/2.32  tff(c_295, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_86])).
% 6.69/2.32  tff(c_297, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_295])).
% 6.69/2.32  tff(c_3056, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_3020, c_297])).
% 6.69/2.32  tff(c_3059, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_3056])).
% 6.69/2.32  tff(c_3062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_96, c_90, c_12, c_1380, c_3059])).
% 6.69/2.32  tff(c_3063, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1378])).
% 6.69/2.32  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.69/2.32  tff(c_939, plain, (![B_169]: (m1_subset_1(B_169, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_169), k1_xboole_0) | ~v1_funct_1(B_169) | ~v1_relat_1(B_169))), inference(superposition, [status(thm), theory('equality')], [c_18, c_907])).
% 6.69/2.32  tff(c_942, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_756, c_939])).
% 6.69/2.32  tff(c_950, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_376, c_96, c_942])).
% 6.69/2.32  tff(c_953, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_950])).
% 6.69/2.32  tff(c_3071, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_953])).
% 6.69/2.32  tff(c_3108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3071])).
% 6.69/2.32  tff(c_3110, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_950])).
% 6.69/2.32  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.69/2.32  tff(c_345, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.69/2.32  tff(c_354, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_345])).
% 6.69/2.32  tff(c_3117, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3110, c_354])).
% 6.69/2.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.69/2.32  tff(c_168, plain, (![B_54, A_55]: (~r1_tarski(B_54, A_55) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.69/2.32  tff(c_173, plain, (![A_56]: (~r1_tarski(A_56, '#skF_1'(A_56)) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_4, c_168])).
% 6.69/2.32  tff(c_178, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_173])).
% 6.69/2.32  tff(c_3144, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3117, c_178])).
% 6.69/2.32  tff(c_3109, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_950])).
% 6.69/2.32  tff(c_3283, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3117, c_3109])).
% 6.69/2.32  tff(c_645, plain, (![C_122, A_123, B_124]: (r2_hidden(C_122, A_123) | ~r2_hidden(C_122, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.69/2.32  tff(c_688, plain, (![A_127, A_128]: (r2_hidden('#skF_1'(A_127), A_128) | ~m1_subset_1(A_127, k1_zfmisc_1(A_128)) | v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_4, c_645])).
% 6.69/2.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.69/2.32  tff(c_699, plain, (![A_128, A_127]: (~v1_xboole_0(A_128) | ~m1_subset_1(A_127, k1_zfmisc_1(A_128)) | v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_688, c_2])).
% 6.69/2.32  tff(c_3288, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3283, c_699])).
% 6.69/2.32  tff(c_3292, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3144, c_3288])).
% 6.69/2.32  tff(c_3294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_644, c_3292])).
% 6.69/2.32  tff(c_3296, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_636])).
% 6.69/2.32  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.69/2.32  tff(c_3335, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3296, c_6])).
% 6.69/2.32  tff(c_68, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.69/2.32  tff(c_100, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_68])).
% 6.69/2.32  tff(c_379, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_100])).
% 6.69/2.32  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.69/2.32  tff(c_56, plain, (v1_funct_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.69/2.32  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.69/2.32  tff(c_20, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.69/2.32  tff(c_577, plain, (![B_118, A_119]: (m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_118), A_119))) | ~r1_tarski(k2_relat_1(B_118), A_119) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.69/2.32  tff(c_599, plain, (![A_119]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_119))) | ~r1_tarski(k2_relat_1(k1_xboole_0), A_119) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_577])).
% 6.69/2.32  tff(c_605, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_14, c_30, c_20, c_599])).
% 6.69/2.32  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_605])).
% 6.69/2.32  tff(c_609, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_100])).
% 6.69/2.32  tff(c_3340, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_3335, c_609])).
% 6.69/2.32  tff(c_3349, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_3335, c_20])).
% 6.69/2.32  tff(c_3353, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_3335, c_30])).
% 6.69/2.32  tff(c_3638, plain, (![A_268, B_269, C_270]: (k2_relset_1(A_268, B_269, C_270)=k2_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.69/2.32  tff(c_3647, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_3638])).
% 6.69/2.32  tff(c_3649, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3353, c_88, c_3647])).
% 6.69/2.32  tff(c_139, plain, (![A_49]: (v1_xboole_0(k4_relat_1(A_49)) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.69/2.32  tff(c_150, plain, (![A_49]: (k4_relat_1(A_49)=k1_xboole_0 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_139, c_6])).
% 6.69/2.32  tff(c_3332, plain, (k4_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3296, c_150])).
% 6.69/2.32  tff(c_3400, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_3332])).
% 6.69/2.32  tff(c_3401, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3400, c_626])).
% 6.69/2.32  tff(c_3434, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_297])).
% 6.69/2.32  tff(c_3651, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3649, c_3434])).
% 6.69/2.32  tff(c_3657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3340, c_3349, c_3651])).
% 6.69/2.32  tff(c_3658, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_295])).
% 6.69/2.32  tff(c_3659, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_295])).
% 6.69/2.32  tff(c_4099, plain, (![A_334, B_335, C_336]: (k1_relset_1(A_334, B_335, C_336)=k1_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.69/2.32  tff(c_4112, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3659, c_4099])).
% 6.69/2.32  tff(c_4345, plain, (![B_372, C_373, A_374]: (k1_xboole_0=B_372 | v1_funct_2(C_373, A_374, B_372) | k1_relset_1(A_374, B_372, C_373)!=A_374 | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_374, B_372))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.69/2.32  tff(c_4351, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_3659, c_4345])).
% 6.69/2.32  tff(c_4363, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4112, c_4351])).
% 6.69/2.32  tff(c_4364, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3658, c_4363])).
% 6.69/2.32  tff(c_4368, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_4364])).
% 6.69/2.32  tff(c_4371, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50, c_4368])).
% 6.69/2.32  tff(c_4374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3708, c_96, c_90, c_4181, c_4371])).
% 6.69/2.32  tff(c_4375, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4364])).
% 6.69/2.32  tff(c_4401, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4375, c_178])).
% 6.69/2.32  tff(c_4405, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4375, c_4375, c_18])).
% 6.69/2.32  tff(c_3983, plain, (![C_323, A_324, B_325]: (r2_hidden(C_323, A_324) | ~r2_hidden(C_323, B_325) | ~m1_subset_1(B_325, k1_zfmisc_1(A_324)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.69/2.32  tff(c_4070, plain, (![A_330, A_331]: (r2_hidden('#skF_1'(A_330), A_331) | ~m1_subset_1(A_330, k1_zfmisc_1(A_331)) | v1_xboole_0(A_330))), inference(resolution, [status(thm)], [c_4, c_3983])).
% 6.69/2.32  tff(c_4082, plain, (![A_332, A_333]: (~v1_xboole_0(A_332) | ~m1_subset_1(A_333, k1_zfmisc_1(A_332)) | v1_xboole_0(A_333))), inference(resolution, [status(thm)], [c_4070, c_2])).
% 6.69/2.32  tff(c_4095, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3659, c_4082])).
% 6.69/2.32  tff(c_4118, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_4095])).
% 6.69/2.32  tff(c_4544, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4405, c_4118])).
% 6.69/2.32  tff(c_4548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4401, c_4544])).
% 6.69/2.32  tff(c_4549, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4095])).
% 6.69/2.32  tff(c_4579, plain, (k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4549, c_6])).
% 6.69/2.32  tff(c_4594, plain, (k2_relat_1('#skF_4')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4579, c_50])).
% 6.69/2.32  tff(c_4607, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3708, c_96, c_90, c_32, c_4594])).
% 6.69/2.32  tff(c_4665, plain, (![A_383, B_384, C_385]: (k2_relset_1(A_383, B_384, C_385)=k2_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.69/2.32  tff(c_4668, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_4665])).
% 6.69/2.32  tff(c_4676, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4607, c_88, c_4668])).
% 6.69/2.32  tff(c_4691, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4676, c_178])).
% 6.69/2.32  tff(c_4695, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4676, c_4676, c_18])).
% 6.69/2.32  tff(c_3987, plain, (![A_326]: (k4_relat_1(A_326)=k2_funct_1(A_326) | ~v2_funct_1(A_326) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.69/2.32  tff(c_3993, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_3987])).
% 6.69/2.32  tff(c_3997, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3708, c_96, c_3993])).
% 6.69/2.32  tff(c_28, plain, (![A_16]: (v1_xboole_0(k4_relat_1(A_16)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.69/2.32  tff(c_4010, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3997, c_28])).
% 6.69/2.32  tff(c_4025, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4010])).
% 6.69/2.32  tff(c_4091, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_92, c_4082])).
% 6.69/2.32  tff(c_4098, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_4025, c_4091])).
% 6.69/2.32  tff(c_4920, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4695, c_4098])).
% 6.69/2.32  tff(c_4924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4691, c_4920])).
% 6.69/2.32  tff(c_4926, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4010])).
% 6.69/2.32  tff(c_4951, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4926, c_6])).
% 6.69/2.32  tff(c_4969, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4951, c_14])).
% 6.69/2.32  tff(c_4968, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4951, c_4951, c_30])).
% 6.69/2.32  tff(c_4967, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4951, c_4951, c_32])).
% 6.69/2.32  tff(c_5252, plain, (![B_415, A_416]: (v1_funct_2(B_415, k1_relat_1(B_415), A_416) | ~r1_tarski(k2_relat_1(B_415), A_416) | ~v1_funct_1(B_415) | ~v1_relat_1(B_415))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.69/2.32  tff(c_5258, plain, (![A_416]: (v1_funct_2('#skF_4', '#skF_4', A_416) | ~r1_tarski(k2_relat_1('#skF_4'), A_416) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4967, c_5252])).
% 6.69/2.32  tff(c_5264, plain, (![A_416]: (v1_funct_2('#skF_4', '#skF_4', A_416))), inference(demodulation, [status(thm), theory('equality')], [c_3708, c_96, c_4969, c_4968, c_5258])).
% 6.69/2.32  tff(c_4948, plain, (k4_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4926, c_150])).
% 6.69/2.32  tff(c_5023, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4951, c_4948])).
% 6.69/2.32  tff(c_5024, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5023, c_3997])).
% 6.69/2.32  tff(c_5044, plain, (![A_397, B_398, C_399]: (k2_relset_1(A_397, B_398, C_399)=k2_relat_1(C_399) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.69/2.32  tff(c_5050, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_5044])).
% 6.69/2.32  tff(c_5053, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4968, c_88, c_5050])).
% 6.69/2.32  tff(c_5055, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5053, c_3658])).
% 6.69/2.32  tff(c_5168, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5024, c_5055])).
% 6.69/2.32  tff(c_5267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5264, c_5168])).
% 6.69/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.32  
% 6.69/2.32  Inference rules
% 6.69/2.32  ----------------------
% 6.69/2.32  #Ref     : 0
% 6.69/2.32  #Sup     : 1185
% 6.69/2.32  #Fact    : 0
% 6.69/2.32  #Define  : 0
% 6.69/2.32  #Split   : 19
% 6.69/2.32  #Chain   : 0
% 6.69/2.32  #Close   : 0
% 6.69/2.32  
% 6.69/2.32  Ordering : KBO
% 6.69/2.32  
% 6.69/2.32  Simplification rules
% 6.69/2.32  ----------------------
% 6.69/2.32  #Subsume      : 125
% 6.69/2.32  #Demod        : 1686
% 6.69/2.32  #Tautology    : 718
% 6.69/2.32  #SimpNegUnit  : 12
% 6.69/2.32  #BackRed      : 215
% 6.69/2.32  
% 6.69/2.32  #Partial instantiations: 0
% 6.69/2.32  #Strategies tried      : 1
% 6.69/2.32  
% 6.69/2.32  Timing (in seconds)
% 6.69/2.32  ----------------------
% 6.86/2.33  Preprocessing        : 0.38
% 6.86/2.33  Parsing              : 0.20
% 6.86/2.33  CNF conversion       : 0.03
% 6.86/2.33  Main loop            : 1.15
% 6.86/2.33  Inferencing          : 0.38
% 6.86/2.33  Reduction            : 0.40
% 6.86/2.33  Demodulation         : 0.29
% 6.86/2.33  BG Simplification    : 0.05
% 6.86/2.33  Subsumption          : 0.22
% 6.86/2.33  Abstraction          : 0.05
% 6.86/2.33  MUC search           : 0.00
% 6.86/2.33  Cooper               : 0.00
% 6.86/2.33  Total                : 1.59
% 6.86/2.33  Index Insertion      : 0.00
% 6.86/2.33  Index Deletion       : 0.00
% 6.86/2.33  Index Matching       : 0.00
% 6.86/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
