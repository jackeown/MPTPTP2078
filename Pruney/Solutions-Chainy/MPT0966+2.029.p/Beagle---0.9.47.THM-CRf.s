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
% DateTime   : Thu Dec  3 10:11:12 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  237 (2071 expanded)
%              Number of leaves         :   40 ( 680 expanded)
%              Depth                    :   14
%              Number of atoms          :  379 (5657 expanded)
%              Number of equality atoms :  122 (1696 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_136,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_98,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4694,plain,(
    ! [A_445,B_446,C_447] :
      ( k1_relset_1(A_445,B_446,C_447) = k1_relat_1(C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4714,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4694])).

tff(c_5170,plain,(
    ! [B_498,A_499,C_500] :
      ( k1_xboole_0 = B_498
      | k1_relset_1(A_499,B_498,C_500) = A_499
      | ~ v1_funct_2(C_500,A_499,B_498)
      | ~ m1_subset_1(C_500,k1_zfmisc_1(k2_zfmisc_1(A_499,B_498))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5186,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_5170])).

tff(c_5197,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4714,c_5186])).

tff(c_5198,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5197])).

tff(c_24,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4314,plain,(
    ! [B_398,A_399] :
      ( v1_relat_1(B_398)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(A_399))
      | ~ v1_relat_1(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4326,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_4314])).

tff(c_4336,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4326])).

tff(c_4799,plain,(
    ! [A_459,B_460,C_461] :
      ( k2_relset_1(A_459,B_460,C_461) = k2_relat_1(C_461)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4819,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4799])).

tff(c_62,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4837,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4819,c_62])).

tff(c_4886,plain,(
    ! [C_469,A_470,B_471] :
      ( m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471)))
      | ~ r1_tarski(k2_relat_1(C_469),B_471)
      | ~ r1_tarski(k1_relat_1(C_469),A_470)
      | ~ v1_relat_1(C_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_567,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_587,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_567])).

tff(c_943,plain,(
    ! [B_157,A_158,C_159] :
      ( k1_xboole_0 = B_157
      | k1_relset_1(A_158,B_157,C_159) = A_158
      | ~ v1_funct_2(C_159,A_158,B_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_959,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_943])).

tff(c_970,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_587,c_959])).

tff(c_971,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_970])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_145,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_157,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_38,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_185,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_194,plain,(
    ! [A_27] :
      ( v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k2_zfmisc_1(A_27,A_27)) ) ),
    inference(resolution,[status(thm)],[c_38,c_185])).

tff(c_204,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194])).

tff(c_28,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_759,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ r1_tarski(k2_relat_1(C_135),B_137)
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1161,plain,(
    ! [C_178,A_179] :
      ( m1_subset_1(C_178,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_178),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_178),A_179)
      | ~ v1_relat_1(C_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_759])).

tff(c_1172,plain,(
    ! [A_17,A_179] :
      ( m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(A_17,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(A_17)),A_179)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1161])).

tff(c_1184,plain,(
    ! [A_180,A_181] :
      ( m1_subset_1(k6_relat_1(A_180),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(A_180,k1_xboole_0)
      | ~ r1_tarski(A_180,A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_28,c_1172])).

tff(c_1202,plain,
    ( m1_subset_1(k6_relat_1('#skF_5'),k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_157,c_1184])).

tff(c_1205,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1202])).

tff(c_197,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_185])).

tff(c_207,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_197])).

tff(c_625,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_645,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_625])).

tff(c_663,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_62])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1362,plain,(
    ! [C_189,A_190,B_191] :
      ( r1_tarski(C_189,k2_zfmisc_1(A_190,B_191))
      | ~ r1_tarski(k2_relat_1(C_189),B_191)
      | ~ r1_tarski(k1_relat_1(C_189),A_190)
      | ~ v1_relat_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_759,c_16])).

tff(c_1366,plain,(
    ! [A_190] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_190,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_190)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_663,c_1362])).

tff(c_1458,plain,(
    ! [A_193] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_193,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_971,c_1366])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_584,plain,(
    ! [A_112,B_113,A_5] :
      ( k1_relset_1(A_112,B_113,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_112,B_113)) ) ),
    inference(resolution,[status(thm)],[c_18,c_567])).

tff(c_1461,plain,(
    ! [A_193] :
      ( k1_relset_1(A_193,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_193) ) ),
    inference(resolution,[status(thm)],[c_1458,c_584])).

tff(c_1486,plain,(
    ! [A_194] :
      ( k1_relset_1(A_194,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_1461])).

tff(c_1491,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_1486])).

tff(c_1382,plain,(
    ! [A_190] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_190,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_971,c_1366])).

tff(c_1103,plain,(
    ! [B_172,C_173,A_174] :
      ( k1_xboole_0 = B_172
      | v1_funct_2(C_173,A_174,B_172)
      | k1_relset_1(A_174,B_172,C_173) != A_174
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1546,plain,(
    ! [B_199,A_200,A_201] :
      ( k1_xboole_0 = B_199
      | v1_funct_2(A_200,A_201,B_199)
      | k1_relset_1(A_201,B_199,A_200) != A_201
      | ~ r1_tarski(A_200,k2_zfmisc_1(A_201,B_199)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1103])).

tff(c_1574,plain,(
    ! [A_190] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_190,'#skF_4')
      | k1_relset_1(A_190,'#skF_4','#skF_5') != A_190
      | ~ r1_tarski('#skF_2',A_190) ) ),
    inference(resolution,[status(thm)],[c_1382,c_1546])).

tff(c_1806,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1574])).

tff(c_1197,plain,
    ( m1_subset_1(k6_relat_1(k2_relat_1('#skF_5')),k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_663,c_1184])).

tff(c_1244,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1197])).

tff(c_1821,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1244])).

tff(c_1869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_1821])).

tff(c_2439,plain,(
    ! [A_247] :
      ( v1_funct_2('#skF_5',A_247,'#skF_4')
      | k1_relset_1(A_247,'#skF_4','#skF_5') != A_247
      | ~ r1_tarski('#skF_2',A_247) ) ),
    inference(splitRight,[status(thm)],[c_1574])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_58])).

tff(c_143,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_2448,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2439,c_143])).

tff(c_2454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1491,c_2448])).

tff(c_2456,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1197])).

tff(c_776,plain,(
    ! [C_135,A_3] :
      ( m1_subset_1(C_135,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_135),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_135),A_3)
      | ~ v1_relat_1(C_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_759])).

tff(c_2463,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_3)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2456,c_776])).

tff(c_2491,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_971,c_2463])).

tff(c_2565,plain,(
    ! [A_251] : ~ r1_tarski('#skF_2',A_251) ),
    inference(splitLeft,[status(thm)],[c_2491])).

tff(c_2570,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_2565])).

tff(c_2571,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_2491])).

tff(c_2590,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2571,c_16])).

tff(c_2609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1205,c_2590])).

tff(c_2611,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1202])).

tff(c_422,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_466,plain,(
    ! [B_86,A_87,A_88] :
      ( ~ v1_xboole_0(B_86)
      | ~ r2_hidden(A_87,A_88)
      | ~ r1_tarski(A_88,B_86) ) ),
    inference(resolution,[status(thm)],[c_18,c_422])).

tff(c_469,plain,(
    ! [B_86,A_28] :
      ( ~ v1_xboole_0(B_86)
      | ~ r1_tarski(A_28,B_86)
      | k1_xboole_0 = A_28 ) ),
    inference(resolution,[status(thm)],[c_40,c_466])).

tff(c_2624,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2611,c_469])).

tff(c_2644,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2624])).

tff(c_134,plain,(
    ! [A_56] : m1_subset_1(k6_relat_1(A_56),k1_zfmisc_1(k2_zfmisc_1(A_56,A_56))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_138,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_134])).

tff(c_334,plain,(
    ! [C_76,B_77,A_78] :
      ( ~ v1_xboole_0(C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_338,plain,(
    ! [A_78] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_78,k6_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_138,c_334])).

tff(c_349,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k6_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_354,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_349])).

tff(c_155,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_138,c_145])).

tff(c_290,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_307,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_155,c_290])).

tff(c_333,plain,(
    ~ r1_tarski(k1_xboole_0,k6_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_356,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_333])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_356])).

tff(c_362,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_381,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_28])).

tff(c_2687,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2644,c_2644,c_381])).

tff(c_2698,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_2687])).

tff(c_2696,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2644,c_2])).

tff(c_2728,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_2696])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2694,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_5',B_4) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2644,c_2644,c_14])).

tff(c_2858,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_2698,c_2694])).

tff(c_436,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_83,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_422])).

tff(c_464,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_2859,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2858,c_464])).

tff(c_2862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2728,c_2859])).

tff(c_2868,plain,(
    ! [A_260] : ~ r2_hidden(A_260,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_2873,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_2868])).

tff(c_2887,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2873,c_86])).

tff(c_2864,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_2883,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | A_28 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2873,c_40])).

tff(c_3155,plain,(
    ! [B_285,A_286,A_287] :
      ( ~ v1_xboole_0(B_285)
      | ~ r2_hidden(A_286,A_287)
      | ~ r1_tarski(A_287,B_285) ) ),
    inference(resolution,[status(thm)],[c_18,c_422])).

tff(c_3167,plain,(
    ! [B_290,A_291] :
      ( ~ v1_xboole_0(B_290)
      | ~ r1_tarski(A_291,B_290)
      | A_291 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_2883,c_3155])).

tff(c_3185,plain,(
    ! [B_292] :
      ( ~ v1_xboole_0(B_292)
      | B_292 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_8,c_3167])).

tff(c_3194,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2864,c_3185])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3274,plain,(
    ! [B_297,A_298] :
      ( B_297 = '#skF_5'
      | A_298 = '#skF_5'
      | k2_zfmisc_1(A_298,B_297) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2873,c_2873,c_2873,c_10])).

tff(c_3277,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3194,c_3274])).

tff(c_3286,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2887,c_3277])).

tff(c_378,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_30])).

tff(c_125,plain,(
    ! [A_53,B_54] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_53,B_54)),B_54) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,(
    ! [B_4] : r1_tarski(k2_relat_1(k1_xboole_0),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_125])).

tff(c_391,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_131])).

tff(c_2878,plain,(
    ! [B_4] : r1_tarski('#skF_5',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2873,c_391])).

tff(c_3314,plain,(
    ! [B_4] : r1_tarski('#skF_2',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_2878])).

tff(c_2881,plain,(
    k6_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2873,c_2873,c_362])).

tff(c_2908,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2881,c_28])).

tff(c_3313,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_3286,c_2908])).

tff(c_3068,plain,(
    ! [A_277,B_278,C_279] :
      ( k1_relset_1(A_277,B_278,C_279) = k1_relat_1(C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4033,plain,(
    ! [A_359,B_360,A_361] :
      ( k1_relset_1(A_359,B_360,A_361) = k1_relat_1(A_361)
      | ~ r1_tarski(A_361,k2_zfmisc_1(A_359,B_360)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3068])).

tff(c_4043,plain,(
    ! [A_359,B_360] : k1_relset_1(A_359,B_360,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3314,c_4033])).

tff(c_4056,plain,(
    ! [A_359,B_360] : k1_relset_1(A_359,B_360,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_4043])).

tff(c_3318,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_2873])).

tff(c_50,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3328,plain,(
    ! [C_299,B_300] :
      ( v1_funct_2(C_299,k1_xboole_0,B_300)
      | k1_relset_1(k1_xboole_0,B_300,C_299) != k1_xboole_0
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_3332,plain,(
    ! [A_5,B_300] :
      ( v1_funct_2(A_5,k1_xboole_0,B_300)
      | k1_relset_1(k1_xboole_0,B_300,A_5) != k1_xboole_0
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_3328])).

tff(c_4225,plain,(
    ! [A_388,B_389] :
      ( v1_funct_2(A_388,'#skF_2',B_389)
      | k1_relset_1('#skF_2',B_389,A_388) != '#skF_2'
      | ~ r1_tarski(A_388,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3318,c_3318,c_3318,c_3318,c_3332])).

tff(c_3321,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_143])).

tff(c_4228,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_2') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_4225,c_3321])).

tff(c_4234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3314,c_4056,c_4228])).

tff(c_4235,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4903,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4886,c_4235])).

tff(c_4919,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4336,c_4837,c_4903])).

tff(c_5199,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5198,c_4919])).

tff(c_5203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5199])).

tff(c_5205,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_5264,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | A_28 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_40])).

tff(c_5204,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_5211,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5204])).

tff(c_5206,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5204,c_2])).

tff(c_5222,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5211,c_5206])).

tff(c_5240,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5205,c_14])).

tff(c_5285,plain,(
    ! [A_514] : m1_subset_1(k6_relat_1(A_514),k1_zfmisc_1(k2_zfmisc_1(A_514,A_514))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5292,plain,(
    m1_subset_1(k6_relat_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5240,c_5285])).

tff(c_5620,plain,(
    ! [C_540,B_541,A_542] :
      ( ~ v1_xboole_0(C_540)
      | ~ m1_subset_1(B_541,k1_zfmisc_1(C_540))
      | ~ r2_hidden(A_542,B_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5624,plain,(
    ! [A_542] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_542,k6_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5292,c_5620])).

tff(c_5644,plain,(
    ! [A_544] : ~ r2_hidden(A_544,k6_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5222,c_5624])).

tff(c_5649,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5264,c_5644])).

tff(c_5669,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5649,c_28])).

tff(c_5666,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5649,c_30])).

tff(c_5266,plain,(
    ! [A_507,B_508] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_507,B_508)),B_508) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5269,plain,(
    ! [B_4] : r1_tarski(k2_relat_1('#skF_3'),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_5240,c_5266])).

tff(c_5679,plain,(
    ! [B_4] : r1_tarski('#skF_3',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5666,c_5269])).

tff(c_5815,plain,(
    ! [A_567,B_568,C_569] :
      ( k1_relset_1(A_567,B_568,C_569) = k1_relat_1(C_569)
      | ~ m1_subset_1(C_569,k1_zfmisc_1(k2_zfmisc_1(A_567,B_568))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6198,plain,(
    ! [A_618,B_619,A_620] :
      ( k1_relset_1(A_618,B_619,A_620) = k1_relat_1(A_620)
      | ~ r1_tarski(A_620,k2_zfmisc_1(A_618,B_619)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5815])).

tff(c_6202,plain,(
    ! [A_618,B_619] : k1_relset_1(A_618,B_619,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5679,c_6198])).

tff(c_6221,plain,(
    ! [A_618,B_619] : k1_relset_1(A_618,B_619,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_6202])).

tff(c_5223,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5205,c_12])).

tff(c_5216,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5211,c_64])).

tff(c_5263,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5223,c_5216])).

tff(c_5486,plain,(
    ! [C_531,B_532,A_533] :
      ( ~ v1_xboole_0(C_531)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(C_531))
      | ~ r2_hidden(A_533,B_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5494,plain,(
    ! [A_533] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_533,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5263,c_5486])).

tff(c_5503,plain,(
    ! [A_534] : ~ r2_hidden(A_534,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5222,c_5494])).

tff(c_5508,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5264,c_5503])).

tff(c_5276,plain,(
    ! [A_512,B_513] :
      ( r1_tarski(A_512,B_513)
      | ~ m1_subset_1(A_512,k1_zfmisc_1(B_513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5284,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_5263,c_5276])).

tff(c_5339,plain,(
    ! [B_518,A_519] :
      ( B_518 = A_519
      | ~ r1_tarski(B_518,A_519)
      | ~ r1_tarski(A_519,B_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5356,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_5284,c_5339])).

tff(c_5367,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5356])).

tff(c_5511,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5508,c_5367])).

tff(c_5521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5511])).

tff(c_5522,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5356])).

tff(c_5528,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5522,c_5263])).

tff(c_72,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_6330,plain,(
    ! [C_635,B_636] :
      ( v1_funct_2(C_635,'#skF_3',B_636)
      | k1_relset_1('#skF_3',B_636,C_635) != '#skF_3'
      | ~ m1_subset_1(C_635,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5205,c_5205,c_5205,c_72])).

tff(c_6332,plain,(
    ! [B_636] :
      ( v1_funct_2('#skF_3','#skF_3',B_636)
      | k1_relset_1('#skF_3',B_636,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_5528,c_6330])).

tff(c_6338,plain,(
    ! [B_636] : v1_funct_2('#skF_3','#skF_3',B_636) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6221,c_6332])).

tff(c_5299,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5211,c_5263,c_5240,c_5211,c_70])).

tff(c_5526,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5522,c_5299])).

tff(c_6343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6338,c_5526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.18  
% 5.75/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.18  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.75/2.18  
% 5.75/2.18  %Foreground sorts:
% 5.75/2.18  
% 5.75/2.18  
% 5.75/2.18  %Background operators:
% 5.75/2.18  
% 5.75/2.18  
% 5.75/2.18  %Foreground operators:
% 5.75/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.75/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.75/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.18  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.75/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.75/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.75/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.18  
% 5.75/2.21  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.75/2.21  tff(f_136, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 5.75/2.21  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.75/2.21  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.75/2.21  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.75/2.21  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.75/2.21  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.21  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.75/2.21  tff(f_98, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.75/2.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.75/2.21  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.75/2.21  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.75/2.21  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.75/2.21  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.75/2.21  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.75/2.21  tff(f_60, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 5.75/2.21  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.21  tff(c_60, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.75/2.21  tff(c_86, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_60])).
% 5.75/2.21  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.75/2.21  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.75/2.21  tff(c_4694, plain, (![A_445, B_446, C_447]: (k1_relset_1(A_445, B_446, C_447)=k1_relat_1(C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.75/2.21  tff(c_4714, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4694])).
% 5.75/2.21  tff(c_5170, plain, (![B_498, A_499, C_500]: (k1_xboole_0=B_498 | k1_relset_1(A_499, B_498, C_500)=A_499 | ~v1_funct_2(C_500, A_499, B_498) | ~m1_subset_1(C_500, k1_zfmisc_1(k2_zfmisc_1(A_499, B_498))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.75/2.21  tff(c_5186, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_5170])).
% 5.75/2.21  tff(c_5197, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4714, c_5186])).
% 5.75/2.21  tff(c_5198, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_5197])).
% 5.75/2.21  tff(c_24, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.75/2.21  tff(c_4314, plain, (![B_398, A_399]: (v1_relat_1(B_398) | ~m1_subset_1(B_398, k1_zfmisc_1(A_399)) | ~v1_relat_1(A_399))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.75/2.21  tff(c_4326, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_4314])).
% 5.75/2.21  tff(c_4336, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4326])).
% 5.75/2.21  tff(c_4799, plain, (![A_459, B_460, C_461]: (k2_relset_1(A_459, B_460, C_461)=k2_relat_1(C_461) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.75/2.21  tff(c_4819, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4799])).
% 5.75/2.21  tff(c_62, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.75/2.21  tff(c_4837, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4819, c_62])).
% 5.75/2.21  tff(c_4886, plain, (![C_469, A_470, B_471]: (m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))) | ~r1_tarski(k2_relat_1(C_469), B_471) | ~r1_tarski(k1_relat_1(C_469), A_470) | ~v1_relat_1(C_469))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.75/2.21  tff(c_40, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.75/2.21  tff(c_567, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.75/2.21  tff(c_587, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_567])).
% 5.75/2.21  tff(c_943, plain, (![B_157, A_158, C_159]: (k1_xboole_0=B_157 | k1_relset_1(A_158, B_157, C_159)=A_158 | ~v1_funct_2(C_159, A_158, B_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.75/2.21  tff(c_959, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_943])).
% 5.75/2.21  tff(c_970, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_587, c_959])).
% 5.75/2.21  tff(c_971, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_970])).
% 5.75/2.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.75/2.21  tff(c_145, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.75/2.21  tff(c_157, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_145])).
% 5.75/2.21  tff(c_38, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.21  tff(c_185, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.75/2.21  tff(c_194, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k2_zfmisc_1(A_27, A_27)))), inference(resolution, [status(thm)], [c_38, c_185])).
% 5.75/2.21  tff(c_204, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194])).
% 5.75/2.21  tff(c_28, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.75/2.21  tff(c_30, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.75/2.21  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.21  tff(c_759, plain, (![C_135, A_136, B_137]: (m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~r1_tarski(k2_relat_1(C_135), B_137) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.75/2.21  tff(c_1161, plain, (![C_178, A_179]: (m1_subset_1(C_178, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_178), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_178), A_179) | ~v1_relat_1(C_178))), inference(superposition, [status(thm), theory('equality')], [c_12, c_759])).
% 5.75/2.21  tff(c_1172, plain, (![A_17, A_179]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(A_17, k1_xboole_0) | ~r1_tarski(k1_relat_1(k6_relat_1(A_17)), A_179) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1161])).
% 5.75/2.21  tff(c_1184, plain, (![A_180, A_181]: (m1_subset_1(k6_relat_1(A_180), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(A_180, k1_xboole_0) | ~r1_tarski(A_180, A_181))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_28, c_1172])).
% 5.75/2.21  tff(c_1202, plain, (m1_subset_1(k6_relat_1('#skF_5'), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_157, c_1184])).
% 5.75/2.21  tff(c_1205, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1202])).
% 5.75/2.21  tff(c_197, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_185])).
% 5.75/2.21  tff(c_207, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_197])).
% 5.75/2.21  tff(c_625, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.75/2.21  tff(c_645, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_625])).
% 5.75/2.21  tff(c_663, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_62])).
% 5.75/2.21  tff(c_16, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.75/2.21  tff(c_1362, plain, (![C_189, A_190, B_191]: (r1_tarski(C_189, k2_zfmisc_1(A_190, B_191)) | ~r1_tarski(k2_relat_1(C_189), B_191) | ~r1_tarski(k1_relat_1(C_189), A_190) | ~v1_relat_1(C_189))), inference(resolution, [status(thm)], [c_759, c_16])).
% 5.75/2.21  tff(c_1366, plain, (![A_190]: (r1_tarski('#skF_5', k2_zfmisc_1(A_190, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_190) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_663, c_1362])).
% 5.75/2.21  tff(c_1458, plain, (![A_193]: (r1_tarski('#skF_5', k2_zfmisc_1(A_193, '#skF_4')) | ~r1_tarski('#skF_2', A_193))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_971, c_1366])).
% 5.75/2.21  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.75/2.21  tff(c_584, plain, (![A_112, B_113, A_5]: (k1_relset_1(A_112, B_113, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_112, B_113)))), inference(resolution, [status(thm)], [c_18, c_567])).
% 5.75/2.21  tff(c_1461, plain, (![A_193]: (k1_relset_1(A_193, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_193))), inference(resolution, [status(thm)], [c_1458, c_584])).
% 5.75/2.21  tff(c_1486, plain, (![A_194]: (k1_relset_1(A_194, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_194))), inference(demodulation, [status(thm), theory('equality')], [c_971, c_1461])).
% 5.75/2.21  tff(c_1491, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_1486])).
% 5.75/2.21  tff(c_1382, plain, (![A_190]: (r1_tarski('#skF_5', k2_zfmisc_1(A_190, '#skF_4')) | ~r1_tarski('#skF_2', A_190))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_971, c_1366])).
% 5.75/2.21  tff(c_1103, plain, (![B_172, C_173, A_174]: (k1_xboole_0=B_172 | v1_funct_2(C_173, A_174, B_172) | k1_relset_1(A_174, B_172, C_173)!=A_174 | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_172))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.75/2.21  tff(c_1546, plain, (![B_199, A_200, A_201]: (k1_xboole_0=B_199 | v1_funct_2(A_200, A_201, B_199) | k1_relset_1(A_201, B_199, A_200)!=A_201 | ~r1_tarski(A_200, k2_zfmisc_1(A_201, B_199)))), inference(resolution, [status(thm)], [c_18, c_1103])).
% 5.75/2.21  tff(c_1574, plain, (![A_190]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_190, '#skF_4') | k1_relset_1(A_190, '#skF_4', '#skF_5')!=A_190 | ~r1_tarski('#skF_2', A_190))), inference(resolution, [status(thm)], [c_1382, c_1546])).
% 5.75/2.21  tff(c_1806, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1574])).
% 5.75/2.21  tff(c_1197, plain, (m1_subset_1(k6_relat_1(k2_relat_1('#skF_5')), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_xboole_0)), inference(resolution, [status(thm)], [c_663, c_1184])).
% 5.75/2.21  tff(c_1244, plain, (~r1_tarski(k2_relat_1('#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1197])).
% 5.75/2.21  tff(c_1821, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1244])).
% 5.75/2.21  tff(c_1869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_663, c_1821])).
% 5.75/2.21  tff(c_2439, plain, (![A_247]: (v1_funct_2('#skF_5', A_247, '#skF_4') | k1_relset_1(A_247, '#skF_4', '#skF_5')!=A_247 | ~r1_tarski('#skF_2', A_247))), inference(splitRight, [status(thm)], [c_1574])).
% 5.75/2.21  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.75/2.21  tff(c_58, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.75/2.21  tff(c_70, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_58])).
% 5.75/2.21  tff(c_143, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 5.75/2.21  tff(c_2448, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2439, c_143])).
% 5.75/2.21  tff(c_2454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1491, c_2448])).
% 5.75/2.21  tff(c_2456, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1197])).
% 5.75/2.21  tff(c_776, plain, (![C_135, A_3]: (m1_subset_1(C_135, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_135), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_135), A_3) | ~v1_relat_1(C_135))), inference(superposition, [status(thm), theory('equality')], [c_12, c_759])).
% 5.75/2.21  tff(c_2463, plain, (![A_3]: (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_5'), A_3) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2456, c_776])).
% 5.75/2.21  tff(c_2491, plain, (![A_3]: (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_971, c_2463])).
% 5.75/2.21  tff(c_2565, plain, (![A_251]: (~r1_tarski('#skF_2', A_251))), inference(splitLeft, [status(thm)], [c_2491])).
% 5.75/2.21  tff(c_2570, plain, $false, inference(resolution, [status(thm)], [c_8, c_2565])).
% 5.75/2.21  tff(c_2571, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_2491])).
% 5.75/2.21  tff(c_2590, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_2571, c_16])).
% 5.75/2.21  tff(c_2609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1205, c_2590])).
% 5.75/2.21  tff(c_2611, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1202])).
% 5.75/2.21  tff(c_422, plain, (![C_81, B_82, A_83]: (~v1_xboole_0(C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.75/2.21  tff(c_466, plain, (![B_86, A_87, A_88]: (~v1_xboole_0(B_86) | ~r2_hidden(A_87, A_88) | ~r1_tarski(A_88, B_86))), inference(resolution, [status(thm)], [c_18, c_422])).
% 5.75/2.21  tff(c_469, plain, (![B_86, A_28]: (~v1_xboole_0(B_86) | ~r1_tarski(A_28, B_86) | k1_xboole_0=A_28)), inference(resolution, [status(thm)], [c_40, c_466])).
% 5.75/2.21  tff(c_2624, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2611, c_469])).
% 5.75/2.21  tff(c_2644, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2624])).
% 5.75/2.21  tff(c_134, plain, (![A_56]: (m1_subset_1(k6_relat_1(A_56), k1_zfmisc_1(k2_zfmisc_1(A_56, A_56))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.21  tff(c_138, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_134])).
% 5.75/2.21  tff(c_334, plain, (![C_76, B_77, A_78]: (~v1_xboole_0(C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.75/2.21  tff(c_338, plain, (![A_78]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_78, k6_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_138, c_334])).
% 5.75/2.21  tff(c_349, plain, (![A_79]: (~r2_hidden(A_79, k6_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_338])).
% 5.75/2.21  tff(c_354, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_349])).
% 5.75/2.21  tff(c_155, plain, (r1_tarski(k6_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_138, c_145])).
% 5.75/2.21  tff(c_290, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.21  tff(c_307, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_155, c_290])).
% 5.75/2.21  tff(c_333, plain, (~r1_tarski(k1_xboole_0, k6_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_307])).
% 5.75/2.21  tff(c_356, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_354, c_333])).
% 5.75/2.21  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_356])).
% 5.75/2.21  tff(c_362, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_307])).
% 5.75/2.21  tff(c_381, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_362, c_28])).
% 5.75/2.21  tff(c_2687, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2644, c_2644, c_381])).
% 5.75/2.21  tff(c_2698, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_971, c_2687])).
% 5.75/2.21  tff(c_2696, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2644, c_2])).
% 5.75/2.21  tff(c_2728, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2698, c_2696])).
% 5.75/2.21  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.21  tff(c_2694, plain, (![B_4]: (k2_zfmisc_1('#skF_5', B_4)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2644, c_2644, c_14])).
% 5.75/2.21  tff(c_2858, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2698, c_2698, c_2694])).
% 5.75/2.21  tff(c_436, plain, (![A_83]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_83, '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_422])).
% 5.75/2.21  tff(c_464, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_436])).
% 5.75/2.21  tff(c_2859, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2858, c_464])).
% 5.75/2.21  tff(c_2862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2728, c_2859])).
% 5.75/2.21  tff(c_2868, plain, (![A_260]: (~r2_hidden(A_260, '#skF_5'))), inference(splitRight, [status(thm)], [c_436])).
% 5.75/2.21  tff(c_2873, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_2868])).
% 5.75/2.21  tff(c_2887, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2873, c_86])).
% 5.75/2.21  tff(c_2864, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_436])).
% 5.75/2.21  tff(c_2883, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | A_28='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2873, c_40])).
% 5.75/2.21  tff(c_3155, plain, (![B_285, A_286, A_287]: (~v1_xboole_0(B_285) | ~r2_hidden(A_286, A_287) | ~r1_tarski(A_287, B_285))), inference(resolution, [status(thm)], [c_18, c_422])).
% 5.75/2.21  tff(c_3167, plain, (![B_290, A_291]: (~v1_xboole_0(B_290) | ~r1_tarski(A_291, B_290) | A_291='#skF_5')), inference(resolution, [status(thm)], [c_2883, c_3155])).
% 5.75/2.21  tff(c_3185, plain, (![B_292]: (~v1_xboole_0(B_292) | B_292='#skF_5')), inference(resolution, [status(thm)], [c_8, c_3167])).
% 5.75/2.21  tff(c_3194, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_2864, c_3185])).
% 5.75/2.21  tff(c_10, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.21  tff(c_3274, plain, (![B_297, A_298]: (B_297='#skF_5' | A_298='#skF_5' | k2_zfmisc_1(A_298, B_297)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2873, c_2873, c_2873, c_10])).
% 5.75/2.21  tff(c_3277, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3194, c_3274])).
% 5.75/2.21  tff(c_3286, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2887, c_3277])).
% 5.75/2.21  tff(c_378, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_362, c_30])).
% 5.75/2.21  tff(c_125, plain, (![A_53, B_54]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_53, B_54)), B_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.75/2.21  tff(c_131, plain, (![B_4]: (r1_tarski(k2_relat_1(k1_xboole_0), B_4))), inference(superposition, [status(thm), theory('equality')], [c_14, c_125])).
% 5.75/2.21  tff(c_391, plain, (![B_4]: (r1_tarski(k1_xboole_0, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_131])).
% 5.75/2.21  tff(c_2878, plain, (![B_4]: (r1_tarski('#skF_5', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_2873, c_391])).
% 5.75/2.21  tff(c_3314, plain, (![B_4]: (r1_tarski('#skF_2', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_3286, c_2878])).
% 5.75/2.21  tff(c_2881, plain, (k6_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2873, c_2873, c_362])).
% 5.75/2.21  tff(c_2908, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2881, c_28])).
% 5.75/2.21  tff(c_3313, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3286, c_3286, c_2908])).
% 5.75/2.21  tff(c_3068, plain, (![A_277, B_278, C_279]: (k1_relset_1(A_277, B_278, C_279)=k1_relat_1(C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.75/2.21  tff(c_4033, plain, (![A_359, B_360, A_361]: (k1_relset_1(A_359, B_360, A_361)=k1_relat_1(A_361) | ~r1_tarski(A_361, k2_zfmisc_1(A_359, B_360)))), inference(resolution, [status(thm)], [c_18, c_3068])).
% 5.75/2.21  tff(c_4043, plain, (![A_359, B_360]: (k1_relset_1(A_359, B_360, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3314, c_4033])).
% 5.75/2.21  tff(c_4056, plain, (![A_359, B_360]: (k1_relset_1(A_359, B_360, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3313, c_4043])).
% 5.75/2.21  tff(c_3318, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3286, c_2873])).
% 5.75/2.21  tff(c_50, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_43))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.75/2.21  tff(c_3328, plain, (![C_299, B_300]: (v1_funct_2(C_299, k1_xboole_0, B_300) | k1_relset_1(k1_xboole_0, B_300, C_299)!=k1_xboole_0 | ~m1_subset_1(C_299, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 5.75/2.21  tff(c_3332, plain, (![A_5, B_300]: (v1_funct_2(A_5, k1_xboole_0, B_300) | k1_relset_1(k1_xboole_0, B_300, A_5)!=k1_xboole_0 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_3328])).
% 5.75/2.21  tff(c_4225, plain, (![A_388, B_389]: (v1_funct_2(A_388, '#skF_2', B_389) | k1_relset_1('#skF_2', B_389, A_388)!='#skF_2' | ~r1_tarski(A_388, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3318, c_3318, c_3318, c_3318, c_3332])).
% 5.75/2.21  tff(c_3321, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3286, c_143])).
% 5.75/2.21  tff(c_4228, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_2')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_4225, c_3321])).
% 5.75/2.21  tff(c_4234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3314, c_4056, c_4228])).
% 5.75/2.21  tff(c_4235, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_70])).
% 5.75/2.21  tff(c_4903, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4886, c_4235])).
% 5.75/2.21  tff(c_4919, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4336, c_4837, c_4903])).
% 5.75/2.21  tff(c_5199, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5198, c_4919])).
% 5.75/2.21  tff(c_5203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_5199])).
% 5.75/2.21  tff(c_5205, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_60])).
% 5.75/2.21  tff(c_5264, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | A_28='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_40])).
% 5.75/2.21  tff(c_5204, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 5.75/2.21  tff(c_5211, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5204])).
% 5.75/2.21  tff(c_5206, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5204, c_2])).
% 5.75/2.21  tff(c_5222, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5211, c_5206])).
% 5.75/2.21  tff(c_5240, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5205, c_14])).
% 5.75/2.21  tff(c_5285, plain, (![A_514]: (m1_subset_1(k6_relat_1(A_514), k1_zfmisc_1(k2_zfmisc_1(A_514, A_514))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.21  tff(c_5292, plain, (m1_subset_1(k6_relat_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5240, c_5285])).
% 5.75/2.21  tff(c_5620, plain, (![C_540, B_541, A_542]: (~v1_xboole_0(C_540) | ~m1_subset_1(B_541, k1_zfmisc_1(C_540)) | ~r2_hidden(A_542, B_541))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.75/2.21  tff(c_5624, plain, (![A_542]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_542, k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_5292, c_5620])).
% 5.75/2.21  tff(c_5644, plain, (![A_544]: (~r2_hidden(A_544, k6_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5222, c_5624])).
% 5.75/2.21  tff(c_5649, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_5264, c_5644])).
% 5.75/2.21  tff(c_5669, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5649, c_28])).
% 5.75/2.21  tff(c_5666, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5649, c_30])).
% 5.75/2.21  tff(c_5266, plain, (![A_507, B_508]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_507, B_508)), B_508))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.75/2.21  tff(c_5269, plain, (![B_4]: (r1_tarski(k2_relat_1('#skF_3'), B_4))), inference(superposition, [status(thm), theory('equality')], [c_5240, c_5266])).
% 5.75/2.21  tff(c_5679, plain, (![B_4]: (r1_tarski('#skF_3', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_5666, c_5269])).
% 5.75/2.21  tff(c_5815, plain, (![A_567, B_568, C_569]: (k1_relset_1(A_567, B_568, C_569)=k1_relat_1(C_569) | ~m1_subset_1(C_569, k1_zfmisc_1(k2_zfmisc_1(A_567, B_568))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.75/2.21  tff(c_6198, plain, (![A_618, B_619, A_620]: (k1_relset_1(A_618, B_619, A_620)=k1_relat_1(A_620) | ~r1_tarski(A_620, k2_zfmisc_1(A_618, B_619)))), inference(resolution, [status(thm)], [c_18, c_5815])).
% 5.75/2.21  tff(c_6202, plain, (![A_618, B_619]: (k1_relset_1(A_618, B_619, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5679, c_6198])).
% 5.75/2.21  tff(c_6221, plain, (![A_618, B_619]: (k1_relset_1(A_618, B_619, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_6202])).
% 5.75/2.21  tff(c_5223, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5205, c_12])).
% 5.75/2.21  tff(c_5216, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5211, c_64])).
% 5.75/2.21  tff(c_5263, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5223, c_5216])).
% 5.75/2.21  tff(c_5486, plain, (![C_531, B_532, A_533]: (~v1_xboole_0(C_531) | ~m1_subset_1(B_532, k1_zfmisc_1(C_531)) | ~r2_hidden(A_533, B_532))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.75/2.21  tff(c_5494, plain, (![A_533]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_533, '#skF_5'))), inference(resolution, [status(thm)], [c_5263, c_5486])).
% 5.75/2.21  tff(c_5503, plain, (![A_534]: (~r2_hidden(A_534, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5222, c_5494])).
% 5.75/2.21  tff(c_5508, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_5264, c_5503])).
% 5.75/2.21  tff(c_5276, plain, (![A_512, B_513]: (r1_tarski(A_512, B_513) | ~m1_subset_1(A_512, k1_zfmisc_1(B_513)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.75/2.21  tff(c_5284, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_5263, c_5276])).
% 5.75/2.21  tff(c_5339, plain, (![B_518, A_519]: (B_518=A_519 | ~r1_tarski(B_518, A_519) | ~r1_tarski(A_519, B_518))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.21  tff(c_5356, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_5284, c_5339])).
% 5.75/2.21  tff(c_5367, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_5356])).
% 5.75/2.21  tff(c_5511, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5508, c_5367])).
% 5.75/2.21  tff(c_5521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_5511])).
% 5.75/2.21  tff(c_5522, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_5356])).
% 5.75/2.21  tff(c_5528, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5522, c_5263])).
% 5.75/2.21  tff(c_72, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 5.75/2.21  tff(c_6330, plain, (![C_635, B_636]: (v1_funct_2(C_635, '#skF_3', B_636) | k1_relset_1('#skF_3', B_636, C_635)!='#skF_3' | ~m1_subset_1(C_635, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5205, c_5205, c_5205, c_72])).
% 5.75/2.21  tff(c_6332, plain, (![B_636]: (v1_funct_2('#skF_3', '#skF_3', B_636) | k1_relset_1('#skF_3', B_636, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_5528, c_6330])).
% 5.75/2.21  tff(c_6338, plain, (![B_636]: (v1_funct_2('#skF_3', '#skF_3', B_636))), inference(demodulation, [status(thm), theory('equality')], [c_6221, c_6332])).
% 5.75/2.21  tff(c_5299, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5211, c_5263, c_5240, c_5211, c_70])).
% 5.75/2.21  tff(c_5526, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5522, c_5299])).
% 5.75/2.21  tff(c_6343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6338, c_5526])).
% 5.75/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.21  
% 5.75/2.21  Inference rules
% 5.75/2.21  ----------------------
% 5.75/2.21  #Ref     : 0
% 5.75/2.21  #Sup     : 1305
% 5.75/2.21  #Fact    : 0
% 5.75/2.21  #Define  : 0
% 5.75/2.21  #Split   : 33
% 5.75/2.21  #Chain   : 0
% 5.75/2.21  #Close   : 0
% 5.75/2.21  
% 5.75/2.21  Ordering : KBO
% 5.75/2.21  
% 5.75/2.21  Simplification rules
% 5.75/2.21  ----------------------
% 5.75/2.21  #Subsume      : 151
% 5.75/2.21  #Demod        : 1601
% 5.75/2.21  #Tautology    : 806
% 5.75/2.21  #SimpNegUnit  : 34
% 5.75/2.21  #BackRed      : 251
% 5.75/2.21  
% 5.75/2.21  #Partial instantiations: 0
% 5.75/2.21  #Strategies tried      : 1
% 5.75/2.21  
% 5.75/2.21  Timing (in seconds)
% 5.75/2.21  ----------------------
% 5.75/2.22  Preprocessing        : 0.33
% 5.75/2.22  Parsing              : 0.17
% 5.75/2.22  CNF conversion       : 0.02
% 5.75/2.22  Main loop            : 1.04
% 5.75/2.22  Inferencing          : 0.36
% 5.75/2.22  Reduction            : 0.37
% 5.75/2.22  Demodulation         : 0.26
% 5.75/2.22  BG Simplification    : 0.04
% 5.75/2.22  Subsumption          : 0.18
% 5.75/2.22  Abstraction          : 0.05
% 5.75/2.22  MUC search           : 0.00
% 5.75/2.22  Cooper               : 0.00
% 5.75/2.22  Total                : 1.44
% 5.75/2.22  Index Insertion      : 0.00
% 5.75/2.22  Index Deletion       : 0.00
% 5.75/2.22  Index Matching       : 0.00
% 5.75/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
