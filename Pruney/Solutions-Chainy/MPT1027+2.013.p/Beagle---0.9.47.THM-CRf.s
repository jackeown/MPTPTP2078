%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  118 (1383 expanded)
%              Number of leaves         :   40 ( 486 expanded)
%              Depth                    :   16
%              Number of atoms          :  189 (3175 expanded)
%              Number of equality atoms :   61 ( 795 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_115,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_hidden(B,A)
         => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
            & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [A_13] : v5_relat_1(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_937,plain,(
    ! [B_147,A_148] :
      ( r1_tarski(k2_relat_1(B_147),A_148)
      | ~ v5_relat_1(B_147,A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_947,plain,(
    ! [A_148] :
      ( r1_tarski(k1_xboole_0,A_148)
      | ~ v5_relat_1(k1_xboole_0,A_148)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_937])).

tff(c_952,plain,(
    ! [A_148] : r1_tarski(k1_xboole_0,A_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_947])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [A_34,B_35] : ~ r2_hidden(A_34,k2_zfmisc_1(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_170,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_170])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_78,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70])).

tff(c_72,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_534,plain,(
    ! [B_103,C_104,A_105] :
      ( k1_xboole_0 = B_103
      | v1_funct_2(C_104,A_105,B_103)
      | k1_relset_1(A_105,B_103,C_104) != A_105
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_543,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_74,c_534])).

tff(c_557,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_543])).

tff(c_558,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_557])).

tff(c_28,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) = k1_xboole_0
      | k2_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_182,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_178,c_28])).

tff(c_190,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_579,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_190])).

tff(c_587,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_558,c_14])).

tff(c_683,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_74])).

tff(c_16,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_216,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_222,plain,(
    ! [C_59,B_7] :
      ( v5_relat_1(C_59,B_7)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_216])).

tff(c_806,plain,(
    ! [C_123,B_124] :
      ( v5_relat_1(C_123,B_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_222])).

tff(c_813,plain,(
    ! [B_124] : v5_relat_1('#skF_4',B_124) ),
    inference(resolution,[status(thm)],[c_683,c_806])).

tff(c_228,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(k2_relat_1(B_64),A_65)
      | ~ v5_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [A_42,B_43] :
      ( r2_xboole_0(A_42,B_43)
      | B_43 = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),B_40)
      | ~ r2_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_133,plain,(
    ! [A_39] : ~ r2_xboole_0(A_39,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_128,c_125])).

tff(c_147,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_135,c_133])).

tff(c_236,plain,(
    ! [B_64] :
      ( k2_relat_1(B_64) = k1_xboole_0
      | ~ v5_relat_1(B_64,k1_xboole_0)
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_228,c_147])).

tff(c_874,plain,(
    ! [B_133] :
      ( k2_relat_1(B_133) = '#skF_3'
      | ~ v5_relat_1(B_133,'#skF_3')
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_558,c_236])).

tff(c_878,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_813,c_874])).

tff(c_885,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_878])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_885])).

tff(c_888,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_993,plain,(
    ! [B_154,A_155] :
      ( r2_hidden(k1_mcart_1(B_154),k1_relat_1(A_155))
      | ~ r2_hidden(B_154,A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_996,plain,(
    ! [B_154] :
      ( r2_hidden(k1_mcart_1(B_154),k1_xboole_0)
      | ~ r2_hidden(B_154,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_993])).

tff(c_1001,plain,(
    ! [B_154] :
      ( r2_hidden(k1_mcart_1(B_154),k1_xboole_0)
      | ~ r2_hidden(B_154,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_996])).

tff(c_1006,plain,(
    ! [B_156] : ~ r2_hidden(B_156,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_1001])).

tff(c_1012,plain,(
    ! [A_157] : ~ r2_xboole_0(A_157,'#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1006])).

tff(c_1018,plain,(
    ! [A_158] :
      ( A_158 = '#skF_4'
      | ~ r1_tarski(A_158,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2,c_1012])).

tff(c_1027,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_952,c_1018])).

tff(c_1035,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_888])).

tff(c_52,plain,(
    ! [A_26] :
      ( v1_funct_2(k1_xboole_0,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_82,plain,(
    ! [A_26] :
      ( v1_funct_2(k1_xboole_0,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_1148,plain,(
    ! [A_26] :
      ( v1_funct_2('#skF_4',A_26,'#skF_4')
      | A_26 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1027,c_1027,c_1027,c_1027,c_82])).

tff(c_1149,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1148])).

tff(c_1043,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1027,c_14])).

tff(c_889,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_1034,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_889])).

tff(c_1192,plain,(
    ! [A_175] :
      ( m1_subset_1(A_175,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_175),k2_relat_1(A_175))))
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1204,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1('#skF_4'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_1192])).

tff(c_1212,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_76,c_1043,c_1034,c_1204])).

tff(c_1214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1149,c_1212])).

tff(c_1216,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1148])).

tff(c_1042,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1027,c_16])).

tff(c_1288,plain,(
    ! [A_191,B_192,C_193] :
      ( k1_relset_1(A_191,B_192,C_193) = k1_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1324,plain,(
    ! [B_197,C_198] :
      ( k1_relset_1('#skF_4',B_197,C_198) = k1_relat_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_1288])).

tff(c_1326,plain,(
    ! [B_197] : k1_relset_1('#skF_4',B_197,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1216,c_1324])).

tff(c_1328,plain,(
    ! [B_197] : k1_relset_1('#skF_4',B_197,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_1326])).

tff(c_56,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_80,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_1431,plain,(
    ! [C_209,B_210] :
      ( v1_funct_2(C_209,'#skF_4',B_210)
      | k1_relset_1('#skF_4',B_210,C_209) != '#skF_4'
      | ~ m1_subset_1(C_209,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1027,c_1027,c_1027,c_80])).

tff(c_1433,plain,(
    ! [B_210] :
      ( v1_funct_2('#skF_4','#skF_4',B_210)
      | k1_relset_1('#skF_4',B_210,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1216,c_1431])).

tff(c_1436,plain,(
    ! [B_210] : v1_funct_2('#skF_4','#skF_4',B_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1433])).

tff(c_1297,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1288])).

tff(c_1299,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1035,c_1297])).

tff(c_1302,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_78])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_1302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.65  
% 3.65/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.65/1.65  
% 3.65/1.65  %Foreground sorts:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Background operators:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Foreground operators:
% 3.65/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.65/1.65  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 3.65/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.65/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.65/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.65/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.65  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.65  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.65/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.65  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.65/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.65/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.65/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.65/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.65  
% 3.65/1.67  tff(f_74, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 3.65/1.67  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.65/1.67  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.65/1.67  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.65/1.67  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.65/1.67  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.65/1.67  tff(f_51, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.65/1.67  tff(f_138, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.65/1.67  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.65/1.67  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.65/1.67  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.65/1.67  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.65/1.67  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_mcart_1)).
% 3.65/1.67  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.65/1.67  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.65/1.67  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.65/1.67  tff(c_34, plain, (![A_13]: (v5_relat_1(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.65/1.67  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.65/1.67  tff(c_937, plain, (![B_147, A_148]: (r1_tarski(k2_relat_1(B_147), A_148) | ~v5_relat_1(B_147, A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.65/1.67  tff(c_947, plain, (![A_148]: (r1_tarski(k1_xboole_0, A_148) | ~v5_relat_1(k1_xboole_0, A_148) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_937])).
% 3.65/1.67  tff(c_952, plain, (![A_148]: (r1_tarski(k1_xboole_0, A_148))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_947])).
% 3.65/1.67  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.65/1.67  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.65/1.67  tff(c_14, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.65/1.67  tff(c_119, plain, (![A_34, B_35]: (~r2_hidden(A_34, k2_zfmisc_1(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.65/1.67  tff(c_125, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_119])).
% 3.65/1.67  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.65/1.67  tff(c_170, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.65/1.67  tff(c_178, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_170])).
% 3.65/1.67  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.65/1.67  tff(c_70, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.65/1.67  tff(c_78, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70])).
% 3.65/1.67  tff(c_72, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.65/1.67  tff(c_534, plain, (![B_103, C_104, A_105]: (k1_xboole_0=B_103 | v1_funct_2(C_104, A_105, B_103) | k1_relset_1(A_105, B_103, C_104)!=A_105 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.65/1.67  tff(c_543, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_74, c_534])).
% 3.65/1.67  tff(c_557, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_543])).
% 3.65/1.67  tff(c_558, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_78, c_557])).
% 3.65/1.67  tff(c_28, plain, (![A_12]: (k1_relat_1(A_12)=k1_xboole_0 | k2_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.65/1.67  tff(c_182, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_178, c_28])).
% 3.65/1.67  tff(c_190, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_182])).
% 3.65/1.67  tff(c_579, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_558, c_190])).
% 3.65/1.67  tff(c_587, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_558, c_14])).
% 3.65/1.67  tff(c_683, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_587, c_74])).
% 3.65/1.67  tff(c_16, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.65/1.67  tff(c_216, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.65/1.67  tff(c_222, plain, (![C_59, B_7]: (v5_relat_1(C_59, B_7) | ~m1_subset_1(C_59, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_216])).
% 3.65/1.67  tff(c_806, plain, (![C_123, B_124]: (v5_relat_1(C_123, B_124) | ~m1_subset_1(C_123, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_222])).
% 3.65/1.67  tff(c_813, plain, (![B_124]: (v5_relat_1('#skF_4', B_124))), inference(resolution, [status(thm)], [c_683, c_806])).
% 3.65/1.67  tff(c_228, plain, (![B_64, A_65]: (r1_tarski(k2_relat_1(B_64), A_65) | ~v5_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.65/1.67  tff(c_135, plain, (![A_42, B_43]: (r2_xboole_0(A_42, B_43) | B_43=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.65/1.67  tff(c_128, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), B_40) | ~r2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.65/1.67  tff(c_133, plain, (![A_39]: (~r2_xboole_0(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_128, c_125])).
% 3.65/1.67  tff(c_147, plain, (![A_42]: (k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_135, c_133])).
% 3.65/1.67  tff(c_236, plain, (![B_64]: (k2_relat_1(B_64)=k1_xboole_0 | ~v5_relat_1(B_64, k1_xboole_0) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_228, c_147])).
% 3.65/1.67  tff(c_874, plain, (![B_133]: (k2_relat_1(B_133)='#skF_3' | ~v5_relat_1(B_133, '#skF_3') | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_558, c_236])).
% 3.65/1.67  tff(c_878, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_813, c_874])).
% 3.65/1.67  tff(c_885, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_878])).
% 3.65/1.67  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_579, c_885])).
% 3.65/1.67  tff(c_888, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_182])).
% 3.65/1.67  tff(c_993, plain, (![B_154, A_155]: (r2_hidden(k1_mcart_1(B_154), k1_relat_1(A_155)) | ~r2_hidden(B_154, A_155) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.65/1.67  tff(c_996, plain, (![B_154]: (r2_hidden(k1_mcart_1(B_154), k1_xboole_0) | ~r2_hidden(B_154, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_888, c_993])).
% 3.65/1.67  tff(c_1001, plain, (![B_154]: (r2_hidden(k1_mcart_1(B_154), k1_xboole_0) | ~r2_hidden(B_154, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_996])).
% 3.65/1.67  tff(c_1006, plain, (![B_156]: (~r2_hidden(B_156, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_125, c_1001])).
% 3.65/1.67  tff(c_1012, plain, (![A_157]: (~r2_xboole_0(A_157, '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_1006])).
% 3.65/1.67  tff(c_1018, plain, (![A_158]: (A_158='#skF_4' | ~r1_tarski(A_158, '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_1012])).
% 3.65/1.67  tff(c_1027, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_952, c_1018])).
% 3.65/1.67  tff(c_1035, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_888])).
% 3.65/1.67  tff(c_52, plain, (![A_26]: (v1_funct_2(k1_xboole_0, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.65/1.67  tff(c_82, plain, (![A_26]: (v1_funct_2(k1_xboole_0, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_52])).
% 3.65/1.67  tff(c_1148, plain, (![A_26]: (v1_funct_2('#skF_4', A_26, '#skF_4') | A_26='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1027, c_1027, c_1027, c_1027, c_82])).
% 3.65/1.67  tff(c_1149, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1148])).
% 3.65/1.67  tff(c_1043, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1027, c_14])).
% 3.65/1.67  tff(c_889, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_182])).
% 3.65/1.67  tff(c_1034, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_889])).
% 3.65/1.67  tff(c_1192, plain, (![A_175]: (m1_subset_1(A_175, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_175), k2_relat_1(A_175)))) | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.65/1.67  tff(c_1204, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1('#skF_4')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1035, c_1192])).
% 3.65/1.67  tff(c_1212, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_76, c_1043, c_1034, c_1204])).
% 3.65/1.67  tff(c_1214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1149, c_1212])).
% 3.65/1.67  tff(c_1216, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1148])).
% 3.65/1.67  tff(c_1042, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1027, c_16])).
% 3.65/1.67  tff(c_1288, plain, (![A_191, B_192, C_193]: (k1_relset_1(A_191, B_192, C_193)=k1_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.65/1.67  tff(c_1324, plain, (![B_197, C_198]: (k1_relset_1('#skF_4', B_197, C_198)=k1_relat_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_1288])).
% 3.65/1.67  tff(c_1326, plain, (![B_197]: (k1_relset_1('#skF_4', B_197, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1216, c_1324])).
% 3.65/1.67  tff(c_1328, plain, (![B_197]: (k1_relset_1('#skF_4', B_197, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1035, c_1326])).
% 3.65/1.67  tff(c_56, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.65/1.67  tff(c_80, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 3.65/1.67  tff(c_1431, plain, (![C_209, B_210]: (v1_funct_2(C_209, '#skF_4', B_210) | k1_relset_1('#skF_4', B_210, C_209)!='#skF_4' | ~m1_subset_1(C_209, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1027, c_1027, c_1027, c_80])).
% 3.65/1.67  tff(c_1433, plain, (![B_210]: (v1_funct_2('#skF_4', '#skF_4', B_210) | k1_relset_1('#skF_4', B_210, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_1216, c_1431])).
% 3.65/1.67  tff(c_1436, plain, (![B_210]: (v1_funct_2('#skF_4', '#skF_4', B_210))), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1433])).
% 3.65/1.67  tff(c_1297, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1288])).
% 3.65/1.67  tff(c_1299, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1035, c_1297])).
% 3.65/1.67  tff(c_1302, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_78])).
% 3.65/1.67  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1436, c_1302])).
% 3.65/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.67  
% 3.65/1.67  Inference rules
% 3.65/1.67  ----------------------
% 3.65/1.67  #Ref     : 0
% 3.65/1.67  #Sup     : 272
% 3.65/1.67  #Fact    : 0
% 3.65/1.67  #Define  : 0
% 3.65/1.67  #Split   : 2
% 3.65/1.67  #Chain   : 0
% 3.65/1.67  #Close   : 0
% 3.65/1.67  
% 3.65/1.67  Ordering : KBO
% 3.65/1.67  
% 3.65/1.67  Simplification rules
% 3.65/1.67  ----------------------
% 3.65/1.67  #Subsume      : 50
% 3.65/1.67  #Demod        : 366
% 3.65/1.67  #Tautology    : 179
% 3.65/1.67  #SimpNegUnit  : 17
% 3.65/1.67  #BackRed      : 61
% 3.65/1.67  
% 3.65/1.67  #Partial instantiations: 0
% 3.65/1.67  #Strategies tried      : 1
% 3.65/1.67  
% 3.65/1.67  Timing (in seconds)
% 3.65/1.67  ----------------------
% 3.65/1.67  Preprocessing        : 0.37
% 3.65/1.67  Parsing              : 0.19
% 3.65/1.68  CNF conversion       : 0.03
% 3.65/1.68  Main loop            : 0.47
% 3.65/1.68  Inferencing          : 0.17
% 3.65/1.68  Reduction            : 0.16
% 3.65/1.68  Demodulation         : 0.11
% 3.65/1.68  BG Simplification    : 0.03
% 3.65/1.68  Subsumption          : 0.08
% 3.65/1.68  Abstraction          : 0.02
% 3.65/1.68  MUC search           : 0.00
% 3.65/1.68  Cooper               : 0.00
% 3.65/1.68  Total                : 0.89
% 3.65/1.68  Index Insertion      : 0.00
% 3.65/1.68  Index Deletion       : 0.00
% 3.65/1.68  Index Matching       : 0.00
% 3.65/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
