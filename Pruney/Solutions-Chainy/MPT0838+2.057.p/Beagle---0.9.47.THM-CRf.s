%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:17 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 252 expanded)
%              Number of leaves         :   37 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  142 ( 539 expanded)
%              Number of equality atoms :   29 ( 104 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_26,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_117,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_120,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_117])).

tff(c_127,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_120])).

tff(c_28,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_135,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_127,c_28])).

tff(c_137,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1('#skF_2'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_200,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_187])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [C_72,B_73,A_74] :
      ( r2_hidden(C_72,B_73)
      | ~ r2_hidden(C_72,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_276,plain,(
    ! [A_92,B_93,B_94] :
      ( m1_subset_1('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_259,c_14])).

tff(c_352,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_370,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_352])).

tff(c_165,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_178,plain,(
    ! [B_63] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_63),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_63) ) ),
    inference(resolution,[status(thm)],[c_165,c_40])).

tff(c_412,plain,(
    ! [B_114] :
      ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5'),B_114),'#skF_4')
      | r1_tarski(k2_relat_1('#skF_5'),B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_370,c_178])).

tff(c_417,plain,(
    ! [B_93] :
      ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
      | r1_tarski(k2_relat_1('#skF_5'),B_93) ) ),
    inference(resolution,[status(thm)],[c_276,c_412])).

tff(c_429,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_432,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_429])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_200,c_432])).

tff(c_440,plain,(
    ! [B_117] : r1_tarski(k2_relat_1('#skF_5'),B_117) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_209,plain,(
    ! [A_11,B_73,B_12] :
      ( r2_hidden(A_11,B_73)
      | ~ r1_tarski(B_12,B_73)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_203])).

tff(c_446,plain,(
    ! [A_11,B_117] :
      ( r2_hidden(A_11,B_117)
      | v1_xboole_0(k2_relat_1('#skF_5'))
      | ~ m1_subset_1(A_11,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_440,c_209])).

tff(c_481,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_487,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_481,c_10])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_487])).

tff(c_504,plain,(
    ! [A_125,B_126] :
      ( r2_hidden(A_125,B_126)
      | ~ m1_subset_1(A_125,k2_relat_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_518,plain,(
    ! [B_127] : r2_hidden('#skF_2'(k2_relat_1('#skF_5')),B_127) ),
    inference(resolution,[status(thm)],[c_12,c_504])).

tff(c_531,plain,(
    ! [B_127] : m1_subset_1('#skF_2'(k2_relat_1('#skF_5')),B_127) ),
    inference(resolution,[status(thm)],[c_518,c_14])).

tff(c_150,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(A_60,B_61)
      | v1_xboole_0(B_61)
      | ~ m1_subset_1(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [A_60] :
      ( ~ m1_subset_1(A_60,'#skF_4')
      | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(A_60,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_150,c_40])).

tff(c_241,plain,(
    ! [A_89] :
      ( ~ m1_subset_1(A_89,'#skF_4')
      | ~ m1_subset_1(A_89,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_251,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_241])).

tff(c_373,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_251])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_373])).

tff(c_535,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_544,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_535,c_10])).

tff(c_588,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_595,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_588])).

tff(c_602,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_595])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_602])).

tff(c_605,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_42,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_612,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_42])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_47] :
      ( v1_xboole_0(k1_relat_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    ! [A_48] :
      ( k1_relat_1(A_48) = k1_xboole_0
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_57,c_10])).

tff(c_70,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_610,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_605,c_70])).

tff(c_882,plain,(
    ! [A_185,B_186,C_187] :
      ( k1_relset_1(A_185,B_186,C_187) = k1_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_889,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_882])).

tff(c_896,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_889])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:39:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.02/1.48  
% 3.02/1.48  %Foreground sorts:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Background operators:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Foreground operators:
% 3.02/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.02/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.02/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.02/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.02/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.48  
% 3.17/1.50  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.17/1.50  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.17/1.50  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.17/1.50  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.17/1.50  tff(f_40, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.17/1.50  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.17/1.50  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.17/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.17/1.50  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.17/1.50  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.17/1.50  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.17/1.50  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.17/1.50  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.17/1.50  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.17/1.50  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.17/1.50  tff(c_26, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.17/1.50  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.17/1.50  tff(c_117, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.17/1.50  tff(c_120, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_117])).
% 3.17/1.50  tff(c_127, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_120])).
% 3.17/1.50  tff(c_28, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.50  tff(c_135, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_127, c_28])).
% 3.17/1.50  tff(c_137, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_135])).
% 3.17/1.50  tff(c_12, plain, (![A_7]: (m1_subset_1('#skF_2'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.50  tff(c_187, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.17/1.50  tff(c_200, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_187])).
% 3.17/1.50  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.17/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.50  tff(c_203, plain, (![C_72, B_73, A_74]: (r2_hidden(C_72, B_73) | ~r2_hidden(C_72, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.50  tff(c_259, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_203])).
% 3.17/1.50  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.17/1.50  tff(c_276, plain, (![A_92, B_93, B_94]: (m1_subset_1('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_259, c_14])).
% 3.17/1.50  tff(c_352, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.50  tff(c_370, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_352])).
% 3.17/1.50  tff(c_165, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.50  tff(c_40, plain, (![D_42]: (~r2_hidden(D_42, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.17/1.50  tff(c_178, plain, (![B_63]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_63), '#skF_4') | r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_63))), inference(resolution, [status(thm)], [c_165, c_40])).
% 3.17/1.50  tff(c_412, plain, (![B_114]: (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5'), B_114), '#skF_4') | r1_tarski(k2_relat_1('#skF_5'), B_114))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_370, c_178])).
% 3.17/1.50  tff(c_417, plain, (![B_93]: (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | r1_tarski(k2_relat_1('#skF_5'), B_93))), inference(resolution, [status(thm)], [c_276, c_412])).
% 3.17/1.50  tff(c_429, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_417])).
% 3.17/1.50  tff(c_432, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_429])).
% 3.17/1.50  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_200, c_432])).
% 3.17/1.50  tff(c_440, plain, (![B_117]: (r1_tarski(k2_relat_1('#skF_5'), B_117))), inference(splitRight, [status(thm)], [c_417])).
% 3.17/1.50  tff(c_16, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.17/1.50  tff(c_209, plain, (![A_11, B_73, B_12]: (r2_hidden(A_11, B_73) | ~r1_tarski(B_12, B_73) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_203])).
% 3.17/1.50  tff(c_446, plain, (![A_11, B_117]: (r2_hidden(A_11, B_117) | v1_xboole_0(k2_relat_1('#skF_5')) | ~m1_subset_1(A_11, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_440, c_209])).
% 3.17/1.50  tff(c_481, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_446])).
% 3.17/1.50  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.50  tff(c_487, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_481, c_10])).
% 3.17/1.50  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_487])).
% 3.17/1.50  tff(c_504, plain, (![A_125, B_126]: (r2_hidden(A_125, B_126) | ~m1_subset_1(A_125, k2_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_446])).
% 3.17/1.50  tff(c_518, plain, (![B_127]: (r2_hidden('#skF_2'(k2_relat_1('#skF_5')), B_127))), inference(resolution, [status(thm)], [c_12, c_504])).
% 3.17/1.50  tff(c_531, plain, (![B_127]: (m1_subset_1('#skF_2'(k2_relat_1('#skF_5')), B_127))), inference(resolution, [status(thm)], [c_518, c_14])).
% 3.17/1.50  tff(c_150, plain, (![A_60, B_61]: (r2_hidden(A_60, B_61) | v1_xboole_0(B_61) | ~m1_subset_1(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.17/1.50  tff(c_163, plain, (![A_60]: (~m1_subset_1(A_60, '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(A_60, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_150, c_40])).
% 3.17/1.50  tff(c_241, plain, (![A_89]: (~m1_subset_1(A_89, '#skF_4') | ~m1_subset_1(A_89, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_163])).
% 3.17/1.50  tff(c_251, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_12, c_241])).
% 3.17/1.50  tff(c_373, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_370, c_251])).
% 3.17/1.50  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_531, c_373])).
% 3.17/1.50  tff(c_535, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_163])).
% 3.17/1.50  tff(c_544, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_535, c_10])).
% 3.17/1.50  tff(c_588, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.50  tff(c_595, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_588])).
% 3.17/1.50  tff(c_602, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_544, c_595])).
% 3.17/1.50  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_602])).
% 3.17/1.50  tff(c_605, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_135])).
% 3.17/1.50  tff(c_42, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.17/1.50  tff(c_612, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_605, c_42])).
% 3.17/1.50  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.17/1.50  tff(c_57, plain, (![A_47]: (v1_xboole_0(k1_relat_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.17/1.50  tff(c_62, plain, (![A_48]: (k1_relat_1(A_48)=k1_xboole_0 | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_57, c_10])).
% 3.17/1.50  tff(c_70, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_62])).
% 3.17/1.50  tff(c_610, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_605, c_605, c_70])).
% 3.17/1.50  tff(c_882, plain, (![A_185, B_186, C_187]: (k1_relset_1(A_185, B_186, C_187)=k1_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.17/1.50  tff(c_889, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_882])).
% 3.17/1.50  tff(c_896, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_610, c_889])).
% 3.17/1.50  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_612, c_896])).
% 3.17/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.50  
% 3.17/1.50  Inference rules
% 3.17/1.50  ----------------------
% 3.17/1.50  #Ref     : 0
% 3.17/1.50  #Sup     : 165
% 3.17/1.50  #Fact    : 0
% 3.17/1.50  #Define  : 0
% 3.17/1.50  #Split   : 6
% 3.17/1.50  #Chain   : 0
% 3.17/1.50  #Close   : 0
% 3.17/1.50  
% 3.17/1.50  Ordering : KBO
% 3.17/1.50  
% 3.17/1.50  Simplification rules
% 3.17/1.50  ----------------------
% 3.17/1.50  #Subsume      : 12
% 3.17/1.50  #Demod        : 86
% 3.17/1.50  #Tautology    : 66
% 3.17/1.50  #SimpNegUnit  : 3
% 3.17/1.50  #BackRed      : 20
% 3.17/1.50  
% 3.17/1.50  #Partial instantiations: 0
% 3.17/1.50  #Strategies tried      : 1
% 3.17/1.50  
% 3.17/1.50  Timing (in seconds)
% 3.17/1.50  ----------------------
% 3.17/1.50  Preprocessing        : 0.34
% 3.17/1.50  Parsing              : 0.19
% 3.17/1.50  CNF conversion       : 0.02
% 3.17/1.50  Main loop            : 0.38
% 3.17/1.50  Inferencing          : 0.15
% 3.17/1.50  Reduction            : 0.11
% 3.17/1.50  Demodulation         : 0.08
% 3.17/1.50  BG Simplification    : 0.02
% 3.17/1.50  Subsumption          : 0.06
% 3.17/1.50  Abstraction          : 0.02
% 3.17/1.50  MUC search           : 0.00
% 3.17/1.50  Cooper               : 0.00
% 3.17/1.50  Total                : 0.75
% 3.17/1.50  Index Insertion      : 0.00
% 3.17/1.50  Index Deletion       : 0.00
% 3.17/1.50  Index Matching       : 0.00
% 3.17/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
