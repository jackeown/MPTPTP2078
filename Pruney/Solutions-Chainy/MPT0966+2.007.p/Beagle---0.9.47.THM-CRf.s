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
% DateTime   : Thu Dec  3 10:11:08 EST 2020

% Result     : Theorem 11.96s
% Output     : CNFRefutation 12.22s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 602 expanded)
%              Number of leaves         :   38 ( 204 expanded)
%              Depth                    :   13
%              Number of atoms          :  281 (1877 expanded)
%              Number of equality atoms :   73 ( 586 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_76,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_121,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_134,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_121])).

tff(c_20821,plain,(
    ! [C_1030,A_1031,B_1032] :
      ( v4_relat_1(C_1030,A_1031)
      | ~ m1_subset_1(C_1030,k1_zfmisc_1(k2_zfmisc_1(A_1031,B_1032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20834,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_20821])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21677,plain,(
    ! [A_1125,B_1126,C_1127] :
      ( k2_relset_1(A_1125,B_1126,C_1127) = k2_relat_1(C_1127)
      | ~ m1_subset_1(C_1127,k1_zfmisc_1(k2_zfmisc_1(A_1125,B_1126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_21694,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_21677])).

tff(c_72,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_21701,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21694,c_72])).

tff(c_22554,plain,(
    ! [C_1176,A_1177,B_1178] :
      ( m1_subset_1(C_1176,k1_zfmisc_1(k2_zfmisc_1(A_1177,B_1178)))
      | ~ r1_tarski(k2_relat_1(C_1176),B_1178)
      | ~ r1_tarski(k1_relat_1(C_1176),A_1177)
      | ~ v1_relat_1(C_1176) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68])).

tff(c_149,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_18777,plain,(
    ! [A_882,B_883,C_884] :
      ( k1_relset_1(A_882,B_883,C_884) = k1_relat_1(C_884)
      | ~ m1_subset_1(C_884,k1_zfmisc_1(k2_zfmisc_1(A_882,B_883))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18790,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_18777])).

tff(c_20679,plain,(
    ! [B_1005,A_1006,C_1007] :
      ( k1_xboole_0 = B_1005
      | k1_relset_1(A_1006,B_1005,C_1007) = A_1006
      | ~ v1_funct_2(C_1007,A_1006,B_1005)
      | ~ m1_subset_1(C_1007,k1_zfmisc_1(k2_zfmisc_1(A_1006,B_1005))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20695,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_20679])).

tff(c_20708,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_18790,c_20695])).

tff(c_20709,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_20708])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_805,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_822,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_805])).

tff(c_10856,plain,(
    ! [B_566,A_567,C_568] :
      ( k1_xboole_0 = B_566
      | k1_relset_1(A_567,B_566,C_568) = A_567
      | ~ v1_funct_2(C_568,A_567,B_566)
      | ~ m1_subset_1(C_568,k1_zfmisc_1(k2_zfmisc_1(A_567,B_566))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10869,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_10856])).

tff(c_10879,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_822,c_10869])).

tff(c_10880,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_10879])).

tff(c_586,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_599,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_586])).

tff(c_605,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_72])).

tff(c_10757,plain,(
    ! [C_560,A_561,B_562] :
      ( m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562)))
      | ~ r1_tarski(k2_relat_1(C_560),B_562)
      | ~ r1_tarski(k1_relat_1(C_560),A_561)
      | ~ v1_relat_1(C_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13495,plain,(
    ! [C_701,A_702,B_703] :
      ( r1_tarski(C_701,k2_zfmisc_1(A_702,B_703))
      | ~ r1_tarski(k2_relat_1(C_701),B_703)
      | ~ r1_tarski(k1_relat_1(C_701),A_702)
      | ~ v1_relat_1(C_701) ) ),
    inference(resolution,[status(thm)],[c_10757,c_14])).

tff(c_13516,plain,(
    ! [A_702] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_702,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_702)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_605,c_13495])).

tff(c_13539,plain,(
    ! [A_704] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_704,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_704) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_10880,c_13516])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_821,plain,(
    ! [A_139,B_140,A_8] :
      ( k1_relset_1(A_139,B_140,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_139,B_140)) ) ),
    inference(resolution,[status(thm)],[c_16,c_805])).

tff(c_13558,plain,(
    ! [A_704] :
      ( k1_relset_1(A_704,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_704) ) ),
    inference(resolution,[status(thm)],[c_13539,c_821])).

tff(c_13594,plain,(
    ! [A_705] :
      ( k1_relset_1(A_705,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_705) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10880,c_13558])).

tff(c_13629,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_13594])).

tff(c_36,plain,(
    ! [C_31,A_29,B_30] :
      ( m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r1_tarski(k2_relat_1(C_31),B_30)
      | ~ r1_tarski(k1_relat_1(C_31),A_29)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11123,plain,(
    ! [B_573,C_574,A_575] :
      ( k1_xboole_0 = B_573
      | v1_funct_2(C_574,A_575,B_573)
      | k1_relset_1(A_575,B_573,C_574) != A_575
      | ~ m1_subset_1(C_574,k1_zfmisc_1(k2_zfmisc_1(A_575,B_573))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17499,plain,(
    ! [B_814,C_815,A_816] :
      ( k1_xboole_0 = B_814
      | v1_funct_2(C_815,A_816,B_814)
      | k1_relset_1(A_816,B_814,C_815) != A_816
      | ~ r1_tarski(k2_relat_1(C_815),B_814)
      | ~ r1_tarski(k1_relat_1(C_815),A_816)
      | ~ v1_relat_1(C_815) ) ),
    inference(resolution,[status(thm)],[c_36,c_11123])).

tff(c_17537,plain,(
    ! [A_816] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_816,'#skF_4')
      | k1_relset_1(A_816,'#skF_4','#skF_5') != A_816
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_816)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_605,c_17499])).

tff(c_17565,plain,(
    ! [A_816] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_816,'#skF_4')
      | k1_relset_1(A_816,'#skF_4','#skF_5') != A_816
      | ~ r1_tarski('#skF_2',A_816) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_10880,c_17537])).

tff(c_17712,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_17565])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17770,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17712,c_10])).

tff(c_105,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_105])).

tff(c_322,plain,(
    ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_603,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_322])).

tff(c_17834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17770,c_603])).

tff(c_18399,plain,(
    ! [A_835] :
      ( v1_funct_2('#skF_5',A_835,'#skF_4')
      | k1_relset_1(A_835,'#skF_4','#skF_5') != A_835
      | ~ r1_tarski('#skF_2',A_835) ) ),
    inference(splitRight,[status(thm)],[c_17565])).

tff(c_18404,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_18399,c_149])).

tff(c_18412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13629,c_18404])).

tff(c_18413,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_19134,plain,(
    ! [A_917,B_918,C_919] :
      ( k2_relset_1(A_917,B_918,C_919) = k2_relat_1(C_919)
      | ~ m1_subset_1(C_919,k1_zfmisc_1(k2_zfmisc_1(A_917,B_918))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_19144,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_19134])).

tff(c_19152,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18413,c_19144])).

tff(c_52,plain,(
    ! [A_35] :
      ( v1_funct_2(A_35,k1_relat_1(A_35),k2_relat_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_19166,plain,
    ( v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_19152,c_52])).

tff(c_19176,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78,c_19166])).

tff(c_20725,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20709,c_19176])).

tff(c_20729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_20725])).

tff(c_20730,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_22583,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22554,c_20730])).

tff(c_22600,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_21701,c_22583])).

tff(c_22608,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_22600])).

tff(c_22615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_20834,c_22608])).

tff(c_22617,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_22616,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_22623,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22617,c_22616])).

tff(c_22639,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22623,c_74])).

tff(c_24818,plain,(
    ! [C_1374,A_1375,B_1376] :
      ( v1_relat_1(C_1374)
      | ~ m1_subset_1(C_1374,k1_zfmisc_1(k2_zfmisc_1(A_1375,B_1376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24831,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22639,c_24818])).

tff(c_22618,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22616,c_10])).

tff(c_22634,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22623,c_22618])).

tff(c_24978,plain,(
    ! [C_1401,A_1402,B_1403] :
      ( v4_relat_1(C_1401,A_1402)
      | ~ m1_subset_1(C_1401,k1_zfmisc_1(k2_zfmisc_1(A_1402,B_1403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24991,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_22639,c_24978])).

tff(c_24887,plain,(
    ! [B_1388,A_1389] :
      ( r1_tarski(k1_relat_1(B_1388),A_1389)
      | ~ v4_relat_1(B_1388,A_1389)
      | ~ v1_relat_1(B_1388) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24789,plain,(
    ! [B_1371,A_1372] :
      ( B_1371 = A_1372
      | ~ r1_tarski(B_1371,A_1372)
      | ~ r1_tarski(A_1372,B_1371) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24800,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ r1_tarski(A_6,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22634,c_24789])).

tff(c_24906,plain,(
    ! [B_1388] :
      ( k1_relat_1(B_1388) = '#skF_3'
      | ~ v4_relat_1(B_1388,'#skF_3')
      | ~ v1_relat_1(B_1388) ) ),
    inference(resolution,[status(thm)],[c_24887,c_24800])).

tff(c_24995,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24991,c_24906])).

tff(c_24998,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24831,c_24995])).

tff(c_25612,plain,(
    ! [A_1458,B_1459,C_1460] :
      ( k2_relset_1(A_1458,B_1459,C_1460) = k2_relat_1(C_1460)
      | ~ m1_subset_1(C_1460,k1_zfmisc_1(k2_zfmisc_1(A_1458,B_1459))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_25633,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22639,c_25612])).

tff(c_22628,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22623,c_72])).

tff(c_25640,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25633,c_22628])).

tff(c_26429,plain,(
    ! [C_1519,A_1520,B_1521] :
      ( m1_subset_1(C_1519,k1_zfmisc_1(k2_zfmisc_1(A_1520,B_1521)))
      | ~ r1_tarski(k2_relat_1(C_1519),B_1521)
      | ~ r1_tarski(k1_relat_1(C_1519),A_1520)
      | ~ v1_relat_1(C_1519) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22659,plain,(
    ! [C_1188,A_1189,B_1190] :
      ( v1_relat_1(C_1188)
      | ~ m1_subset_1(C_1188,k1_zfmisc_1(k2_zfmisc_1(A_1189,B_1190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22672,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22639,c_22659])).

tff(c_22841,plain,(
    ! [C_1218,A_1219,B_1220] :
      ( v4_relat_1(C_1218,A_1219)
      | ~ m1_subset_1(C_1218,k1_zfmisc_1(k2_zfmisc_1(A_1219,B_1220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22854,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_22639,c_22841])).

tff(c_22738,plain,(
    ! [B_1203,A_1204] :
      ( r1_tarski(k1_relat_1(B_1203),A_1204)
      | ~ v4_relat_1(B_1203,A_1204)
      | ~ v1_relat_1(B_1203) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22674,plain,(
    ! [B_1191,A_1192] :
      ( B_1191 = A_1192
      | ~ r1_tarski(B_1191,A_1192)
      | ~ r1_tarski(A_1192,B_1191) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22685,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ r1_tarski(A_6,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22634,c_22674])).

tff(c_22750,plain,(
    ! [B_1203] :
      ( k1_relat_1(B_1203) = '#skF_3'
      | ~ v4_relat_1(B_1203,'#skF_3')
      | ~ v1_relat_1(B_1203) ) ),
    inference(resolution,[status(thm)],[c_22738,c_22685])).

tff(c_22858,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22854,c_22750])).

tff(c_22861,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22672,c_22858])).

tff(c_24690,plain,(
    ! [C_1366,B_1367] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_1366),B_1367,C_1366),k1_relat_1(C_1366))
      | v1_funct_2(C_1366,k1_relat_1(C_1366),B_1367)
      | ~ v1_funct_1(C_1366)
      | ~ v1_relat_1(C_1366) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_24722,plain,(
    ! [B_1367] :
      ( r2_hidden('#skF_1'('#skF_3',B_1367,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_1367)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22861,c_24690])).

tff(c_24748,plain,(
    ! [B_1368] :
      ( r2_hidden('#skF_1'('#skF_3',B_1368,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_1368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22672,c_78,c_22861,c_22861,c_24722])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24755,plain,(
    ! [B_1368] :
      ( ~ r1_tarski('#skF_3','#skF_1'('#skF_3',B_1368,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_1368) ) ),
    inference(resolution,[status(thm)],[c_24748,c_24])).

tff(c_24762,plain,(
    ! [B_1368] : v1_funct_2('#skF_5','#skF_3',B_1368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22634,c_24755])).

tff(c_22643,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22623,c_22623,c_80])).

tff(c_22644,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22643])).

tff(c_24768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24762,c_22644])).

tff(c_24769,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_22643])).

tff(c_26464,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26429,c_24769])).

tff(c_26478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24831,c_22634,c_24998,c_25640,c_26464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.96/4.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.15/4.79  
% 12.15/4.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.15/4.79  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 12.15/4.79  
% 12.15/4.79  %Foreground sorts:
% 12.15/4.79  
% 12.15/4.79  
% 12.15/4.79  %Background operators:
% 12.15/4.79  
% 12.15/4.79  
% 12.15/4.79  %Foreground operators:
% 12.15/4.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.15/4.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.15/4.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.15/4.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.15/4.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.15/4.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.15/4.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.15/4.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.15/4.79  tff('#skF_5', type, '#skF_5': $i).
% 12.15/4.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.15/4.79  tff('#skF_2', type, '#skF_2': $i).
% 12.15/4.79  tff('#skF_3', type, '#skF_3': $i).
% 12.15/4.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.15/4.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.15/4.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.15/4.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.15/4.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.15/4.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.15/4.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.15/4.79  tff('#skF_4', type, '#skF_4': $i).
% 12.15/4.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.15/4.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.15/4.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.15/4.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.15/4.79  
% 12.22/4.81  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 12.22/4.81  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.22/4.81  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.22/4.81  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 12.22/4.81  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.22/4.81  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 12.22/4.81  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.22/4.81  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.22/4.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.22/4.81  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.22/4.81  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.22/4.81  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.22/4.81  tff(f_133, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 12.22/4.81  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 12.22/4.81  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.22/4.81  tff(c_121, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.22/4.81  tff(c_134, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_121])).
% 12.22/4.81  tff(c_20821, plain, (![C_1030, A_1031, B_1032]: (v4_relat_1(C_1030, A_1031) | ~m1_subset_1(C_1030, k1_zfmisc_1(k2_zfmisc_1(A_1031, B_1032))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.22/4.81  tff(c_20834, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_20821])).
% 12.22/4.81  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.22/4.81  tff(c_21677, plain, (![A_1125, B_1126, C_1127]: (k2_relset_1(A_1125, B_1126, C_1127)=k2_relat_1(C_1127) | ~m1_subset_1(C_1127, k1_zfmisc_1(k2_zfmisc_1(A_1125, B_1126))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.22/4.81  tff(c_21694, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_21677])).
% 12.22/4.81  tff(c_72, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.22/4.81  tff(c_21701, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21694, c_72])).
% 12.22/4.81  tff(c_22554, plain, (![C_1176, A_1177, B_1178]: (m1_subset_1(C_1176, k1_zfmisc_1(k2_zfmisc_1(A_1177, B_1178))) | ~r1_tarski(k2_relat_1(C_1176), B_1178) | ~r1_tarski(k1_relat_1(C_1176), A_1177) | ~v1_relat_1(C_1176))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.22/4.81  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.22/4.81  tff(c_68, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.22/4.81  tff(c_80, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68])).
% 12.22/4.81  tff(c_149, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 12.22/4.81  tff(c_70, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.22/4.81  tff(c_86, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 12.22/4.81  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.22/4.81  tff(c_18777, plain, (![A_882, B_883, C_884]: (k1_relset_1(A_882, B_883, C_884)=k1_relat_1(C_884) | ~m1_subset_1(C_884, k1_zfmisc_1(k2_zfmisc_1(A_882, B_883))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.22/4.81  tff(c_18790, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_18777])).
% 12.22/4.81  tff(c_20679, plain, (![B_1005, A_1006, C_1007]: (k1_xboole_0=B_1005 | k1_relset_1(A_1006, B_1005, C_1007)=A_1006 | ~v1_funct_2(C_1007, A_1006, B_1005) | ~m1_subset_1(C_1007, k1_zfmisc_1(k2_zfmisc_1(A_1006, B_1005))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.22/4.81  tff(c_20695, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_20679])).
% 12.22/4.81  tff(c_20708, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_18790, c_20695])).
% 12.22/4.81  tff(c_20709, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_20708])).
% 12.22/4.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.22/4.81  tff(c_805, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.22/4.81  tff(c_822, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_805])).
% 12.22/4.81  tff(c_10856, plain, (![B_566, A_567, C_568]: (k1_xboole_0=B_566 | k1_relset_1(A_567, B_566, C_568)=A_567 | ~v1_funct_2(C_568, A_567, B_566) | ~m1_subset_1(C_568, k1_zfmisc_1(k2_zfmisc_1(A_567, B_566))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.22/4.81  tff(c_10869, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_10856])).
% 12.22/4.81  tff(c_10879, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_822, c_10869])).
% 12.22/4.81  tff(c_10880, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_10879])).
% 12.22/4.81  tff(c_586, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.22/4.81  tff(c_599, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_586])).
% 12.22/4.81  tff(c_605, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_72])).
% 12.22/4.81  tff(c_10757, plain, (![C_560, A_561, B_562]: (m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))) | ~r1_tarski(k2_relat_1(C_560), B_562) | ~r1_tarski(k1_relat_1(C_560), A_561) | ~v1_relat_1(C_560))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.22/4.81  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.22/4.81  tff(c_13495, plain, (![C_701, A_702, B_703]: (r1_tarski(C_701, k2_zfmisc_1(A_702, B_703)) | ~r1_tarski(k2_relat_1(C_701), B_703) | ~r1_tarski(k1_relat_1(C_701), A_702) | ~v1_relat_1(C_701))), inference(resolution, [status(thm)], [c_10757, c_14])).
% 12.22/4.81  tff(c_13516, plain, (![A_702]: (r1_tarski('#skF_5', k2_zfmisc_1(A_702, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_702) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_605, c_13495])).
% 12.22/4.81  tff(c_13539, plain, (![A_704]: (r1_tarski('#skF_5', k2_zfmisc_1(A_704, '#skF_4')) | ~r1_tarski('#skF_2', A_704))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_10880, c_13516])).
% 12.22/4.81  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.22/4.81  tff(c_821, plain, (![A_139, B_140, A_8]: (k1_relset_1(A_139, B_140, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_139, B_140)))), inference(resolution, [status(thm)], [c_16, c_805])).
% 12.22/4.81  tff(c_13558, plain, (![A_704]: (k1_relset_1(A_704, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_704))), inference(resolution, [status(thm)], [c_13539, c_821])).
% 12.22/4.81  tff(c_13594, plain, (![A_705]: (k1_relset_1(A_705, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_705))), inference(demodulation, [status(thm), theory('equality')], [c_10880, c_13558])).
% 12.22/4.81  tff(c_13629, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_13594])).
% 12.22/4.81  tff(c_36, plain, (![C_31, A_29, B_30]: (m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r1_tarski(k2_relat_1(C_31), B_30) | ~r1_tarski(k1_relat_1(C_31), A_29) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.22/4.81  tff(c_11123, plain, (![B_573, C_574, A_575]: (k1_xboole_0=B_573 | v1_funct_2(C_574, A_575, B_573) | k1_relset_1(A_575, B_573, C_574)!=A_575 | ~m1_subset_1(C_574, k1_zfmisc_1(k2_zfmisc_1(A_575, B_573))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.22/4.81  tff(c_17499, plain, (![B_814, C_815, A_816]: (k1_xboole_0=B_814 | v1_funct_2(C_815, A_816, B_814) | k1_relset_1(A_816, B_814, C_815)!=A_816 | ~r1_tarski(k2_relat_1(C_815), B_814) | ~r1_tarski(k1_relat_1(C_815), A_816) | ~v1_relat_1(C_815))), inference(resolution, [status(thm)], [c_36, c_11123])).
% 12.22/4.81  tff(c_17537, plain, (![A_816]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_816, '#skF_4') | k1_relset_1(A_816, '#skF_4', '#skF_5')!=A_816 | ~r1_tarski(k1_relat_1('#skF_5'), A_816) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_605, c_17499])).
% 12.22/4.81  tff(c_17565, plain, (![A_816]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_816, '#skF_4') | k1_relset_1(A_816, '#skF_4', '#skF_5')!=A_816 | ~r1_tarski('#skF_2', A_816))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_10880, c_17537])).
% 12.22/4.81  tff(c_17712, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_17565])).
% 12.22/4.81  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.22/4.81  tff(c_17770, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_17712, c_10])).
% 12.22/4.81  tff(c_105, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.22/4.81  tff(c_115, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_105])).
% 12.22/4.81  tff(c_322, plain, (~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_115])).
% 12.22/4.81  tff(c_603, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_322])).
% 12.22/4.81  tff(c_17834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17770, c_603])).
% 12.22/4.81  tff(c_18399, plain, (![A_835]: (v1_funct_2('#skF_5', A_835, '#skF_4') | k1_relset_1(A_835, '#skF_4', '#skF_5')!=A_835 | ~r1_tarski('#skF_2', A_835))), inference(splitRight, [status(thm)], [c_17565])).
% 12.22/4.81  tff(c_18404, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_18399, c_149])).
% 12.22/4.81  tff(c_18412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13629, c_18404])).
% 12.22/4.81  tff(c_18413, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 12.22/4.81  tff(c_19134, plain, (![A_917, B_918, C_919]: (k2_relset_1(A_917, B_918, C_919)=k2_relat_1(C_919) | ~m1_subset_1(C_919, k1_zfmisc_1(k2_zfmisc_1(A_917, B_918))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.22/4.81  tff(c_19144, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_19134])).
% 12.22/4.81  tff(c_19152, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18413, c_19144])).
% 12.22/4.81  tff(c_52, plain, (![A_35]: (v1_funct_2(A_35, k1_relat_1(A_35), k2_relat_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_116])).
% 12.22/4.81  tff(c_19166, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_19152, c_52])).
% 12.22/4.81  tff(c_19176, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78, c_19166])).
% 12.22/4.81  tff(c_20725, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20709, c_19176])).
% 12.22/4.81  tff(c_20729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_20725])).
% 12.22/4.81  tff(c_20730, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_80])).
% 12.22/4.81  tff(c_22583, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22554, c_20730])).
% 12.22/4.81  tff(c_22600, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_21701, c_22583])).
% 12.22/4.81  tff(c_22608, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_22600])).
% 12.22/4.81  tff(c_22615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_20834, c_22608])).
% 12.22/4.81  tff(c_22617, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 12.22/4.81  tff(c_22616, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 12.22/4.81  tff(c_22623, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22617, c_22616])).
% 12.22/4.81  tff(c_22639, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22623, c_74])).
% 12.22/4.81  tff(c_24818, plain, (![C_1374, A_1375, B_1376]: (v1_relat_1(C_1374) | ~m1_subset_1(C_1374, k1_zfmisc_1(k2_zfmisc_1(A_1375, B_1376))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.22/4.81  tff(c_24831, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22639, c_24818])).
% 12.22/4.81  tff(c_22618, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_22616, c_10])).
% 12.22/4.81  tff(c_22634, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_22623, c_22618])).
% 12.22/4.81  tff(c_24978, plain, (![C_1401, A_1402, B_1403]: (v4_relat_1(C_1401, A_1402) | ~m1_subset_1(C_1401, k1_zfmisc_1(k2_zfmisc_1(A_1402, B_1403))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.22/4.81  tff(c_24991, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_22639, c_24978])).
% 12.22/4.81  tff(c_24887, plain, (![B_1388, A_1389]: (r1_tarski(k1_relat_1(B_1388), A_1389) | ~v4_relat_1(B_1388, A_1389) | ~v1_relat_1(B_1388))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.22/4.81  tff(c_24789, plain, (![B_1371, A_1372]: (B_1371=A_1372 | ~r1_tarski(B_1371, A_1372) | ~r1_tarski(A_1372, B_1371))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.22/4.81  tff(c_24800, plain, (![A_6]: (A_6='#skF_3' | ~r1_tarski(A_6, '#skF_3'))), inference(resolution, [status(thm)], [c_22634, c_24789])).
% 12.22/4.81  tff(c_24906, plain, (![B_1388]: (k1_relat_1(B_1388)='#skF_3' | ~v4_relat_1(B_1388, '#skF_3') | ~v1_relat_1(B_1388))), inference(resolution, [status(thm)], [c_24887, c_24800])).
% 12.22/4.81  tff(c_24995, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24991, c_24906])).
% 12.22/4.81  tff(c_24998, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24831, c_24995])).
% 12.22/4.81  tff(c_25612, plain, (![A_1458, B_1459, C_1460]: (k2_relset_1(A_1458, B_1459, C_1460)=k2_relat_1(C_1460) | ~m1_subset_1(C_1460, k1_zfmisc_1(k2_zfmisc_1(A_1458, B_1459))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.22/4.81  tff(c_25633, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22639, c_25612])).
% 12.22/4.81  tff(c_22628, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22623, c_72])).
% 12.22/4.81  tff(c_25640, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25633, c_22628])).
% 12.22/4.81  tff(c_26429, plain, (![C_1519, A_1520, B_1521]: (m1_subset_1(C_1519, k1_zfmisc_1(k2_zfmisc_1(A_1520, B_1521))) | ~r1_tarski(k2_relat_1(C_1519), B_1521) | ~r1_tarski(k1_relat_1(C_1519), A_1520) | ~v1_relat_1(C_1519))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.22/4.81  tff(c_22659, plain, (![C_1188, A_1189, B_1190]: (v1_relat_1(C_1188) | ~m1_subset_1(C_1188, k1_zfmisc_1(k2_zfmisc_1(A_1189, B_1190))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.22/4.81  tff(c_22672, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22639, c_22659])).
% 12.22/4.81  tff(c_22841, plain, (![C_1218, A_1219, B_1220]: (v4_relat_1(C_1218, A_1219) | ~m1_subset_1(C_1218, k1_zfmisc_1(k2_zfmisc_1(A_1219, B_1220))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.22/4.81  tff(c_22854, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_22639, c_22841])).
% 12.22/4.81  tff(c_22738, plain, (![B_1203, A_1204]: (r1_tarski(k1_relat_1(B_1203), A_1204) | ~v4_relat_1(B_1203, A_1204) | ~v1_relat_1(B_1203))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.22/4.81  tff(c_22674, plain, (![B_1191, A_1192]: (B_1191=A_1192 | ~r1_tarski(B_1191, A_1192) | ~r1_tarski(A_1192, B_1191))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.22/4.81  tff(c_22685, plain, (![A_6]: (A_6='#skF_3' | ~r1_tarski(A_6, '#skF_3'))), inference(resolution, [status(thm)], [c_22634, c_22674])).
% 12.22/4.81  tff(c_22750, plain, (![B_1203]: (k1_relat_1(B_1203)='#skF_3' | ~v4_relat_1(B_1203, '#skF_3') | ~v1_relat_1(B_1203))), inference(resolution, [status(thm)], [c_22738, c_22685])).
% 12.22/4.81  tff(c_22858, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22854, c_22750])).
% 12.22/4.81  tff(c_22861, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22672, c_22858])).
% 12.22/4.81  tff(c_24690, plain, (![C_1366, B_1367]: (r2_hidden('#skF_1'(k1_relat_1(C_1366), B_1367, C_1366), k1_relat_1(C_1366)) | v1_funct_2(C_1366, k1_relat_1(C_1366), B_1367) | ~v1_funct_1(C_1366) | ~v1_relat_1(C_1366))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.22/4.81  tff(c_24722, plain, (![B_1367]: (r2_hidden('#skF_1'('#skF_3', B_1367, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_1367) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_22861, c_24690])).
% 12.22/4.81  tff(c_24748, plain, (![B_1368]: (r2_hidden('#skF_1'('#skF_3', B_1368, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_1368))), inference(demodulation, [status(thm), theory('equality')], [c_22672, c_78, c_22861, c_22861, c_24722])).
% 12.22/4.81  tff(c_24, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.22/4.81  tff(c_24755, plain, (![B_1368]: (~r1_tarski('#skF_3', '#skF_1'('#skF_3', B_1368, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_1368))), inference(resolution, [status(thm)], [c_24748, c_24])).
% 12.22/4.81  tff(c_24762, plain, (![B_1368]: (v1_funct_2('#skF_5', '#skF_3', B_1368))), inference(demodulation, [status(thm), theory('equality')], [c_22634, c_24755])).
% 12.22/4.81  tff(c_22643, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22623, c_22623, c_80])).
% 12.22/4.81  tff(c_22644, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_22643])).
% 12.22/4.81  tff(c_24768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24762, c_22644])).
% 12.22/4.81  tff(c_24769, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_22643])).
% 12.22/4.81  tff(c_26464, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26429, c_24769])).
% 12.22/4.81  tff(c_26478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24831, c_22634, c_24998, c_25640, c_26464])).
% 12.22/4.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.22/4.81  
% 12.22/4.81  Inference rules
% 12.22/4.81  ----------------------
% 12.22/4.81  #Ref     : 0
% 12.22/4.81  #Sup     : 5281
% 12.22/4.81  #Fact    : 0
% 12.22/4.81  #Define  : 0
% 12.22/4.81  #Split   : 64
% 12.22/4.81  #Chain   : 0
% 12.22/4.81  #Close   : 0
% 12.22/4.81  
% 12.22/4.81  Ordering : KBO
% 12.22/4.81  
% 12.22/4.81  Simplification rules
% 12.22/4.81  ----------------------
% 12.22/4.81  #Subsume      : 1469
% 12.22/4.81  #Demod        : 5555
% 12.22/4.81  #Tautology    : 1729
% 12.22/4.81  #SimpNegUnit  : 109
% 12.22/4.81  #BackRed      : 289
% 12.22/4.81  
% 12.22/4.81  #Partial instantiations: 0
% 12.22/4.81  #Strategies tried      : 1
% 12.22/4.81  
% 12.22/4.81  Timing (in seconds)
% 12.22/4.81  ----------------------
% 12.22/4.82  Preprocessing        : 0.35
% 12.22/4.82  Parsing              : 0.19
% 12.22/4.82  CNF conversion       : 0.02
% 12.22/4.82  Main loop            : 3.69
% 12.22/4.82  Inferencing          : 1.02
% 12.22/4.82  Reduction            : 1.47
% 12.22/4.82  Demodulation         : 1.08
% 12.22/4.82  BG Simplification    : 0.08
% 12.22/4.82  Subsumption          : 0.87
% 12.22/4.82  Abstraction          : 0.12
% 12.22/4.82  MUC search           : 0.00
% 12.22/4.82  Cooper               : 0.00
% 12.22/4.82  Total                : 4.09
% 12.22/4.82  Index Insertion      : 0.00
% 12.22/4.82  Index Deletion       : 0.00
% 12.22/4.82  Index Matching       : 0.00
% 12.22/4.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
