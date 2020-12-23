%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:15 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 314 expanded)
%              Number of leaves         :   49 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          :  191 ( 678 expanded)
%              Number of equality atoms :   56 ( 168 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_138,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_150,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1('#skF_1'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_65,B_66] : ~ r2_hidden(A_65,k2_zfmisc_1(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_137,plain,(
    ! [A_72] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_124,c_94])).

tff(c_140,plain,(
    ! [A_74] : ~ m1_subset_1(A_74,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_145,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_140])).

tff(c_146,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_159,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_171,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_159])).

tff(c_178,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_192,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_178])).

tff(c_282,plain,(
    ! [B_107,A_108] :
      ( k7_relat_1(B_107,A_108) = B_107
      | ~ v4_relat_1(B_107,A_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_291,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_192,c_282])).

tff(c_300,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_291])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_304,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_24])).

tff(c_308,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_304])).

tff(c_22,plain,(
    ! [A_16,B_18] :
      ( k9_relat_1(A_16,k1_tarski(B_18)) = k11_relat_1(A_16,B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_313,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_22])).

tff(c_320,plain,(
    k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_313])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_433,plain,(
    ! [A_135,B_136] :
      ( k1_funct_1(A_135,B_136) = k1_xboole_0
      | r2_hidden(B_136,k1_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( k11_relat_1(B_25,A_24) != k1_xboole_0
      | ~ r2_hidden(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_444,plain,(
    ! [A_137,B_138] :
      ( k11_relat_1(A_137,B_138) != k1_xboole_0
      | k1_funct_1(A_137,B_138) = k1_xboole_0
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(resolution,[status(thm)],[c_433,c_30])).

tff(c_450,plain,(
    ! [B_138] :
      ( k11_relat_1('#skF_6',B_138) != k1_xboole_0
      | k1_funct_1('#skF_6',B_138) = k1_xboole_0
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_171,c_444])).

tff(c_457,plain,(
    ! [B_139] :
      ( k11_relat_1('#skF_6',B_139) != k1_xboole_0
      | k1_funct_1('#skF_6',B_139) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_450])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_466,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_5')
    | k11_relat_1('#skF_6','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_58])).

tff(c_472,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_5')
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_466])).

tff(c_474,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,k1_relat_1(B_25))
      | k11_relat_1(B_25,A_24) = k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_235,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_249,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_235])).

tff(c_586,plain,(
    ! [B_160,C_161,A_162] :
      ( r2_hidden(k1_funct_1(B_160,C_161),A_162)
      | ~ r2_hidden(C_161,k1_relat_1(B_160))
      | ~ v1_funct_1(B_160)
      | ~ v5_relat_1(B_160,A_162)
      | ~ v1_relat_1(B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_597,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_586,c_58])).

tff(c_614,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_249,c_66,c_597])).

tff(c_651,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_614])).

tff(c_660,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_320,c_651])).

tff(c_662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_660])).

tff(c_663,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40,plain,(
    ! [A_28,B_31] :
      ( k1_funct_1(A_28,B_31) = k1_xboole_0
      | r2_hidden(B_31,k1_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_664,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_2'(A_21,B_22),k2_relat_1(B_22))
      | ~ r2_hidden(A_21,k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_674,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_2'(A_21,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden(A_21,k1_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_26])).

tff(c_678,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_2'(A_21,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden(A_21,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_674])).

tff(c_686,plain,(
    ! [A_166] : ~ r2_hidden(A_166,k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_678])).

tff(c_690,plain,(
    ! [B_31] :
      ( k1_funct_1('#skF_6',B_31) = k1_xboole_0
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_686])).

tff(c_705,plain,(
    ! [B_31] : k1_funct_1('#skF_6',B_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_66,c_690])).

tff(c_50,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_3'(A_43),A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_964,plain,(
    ! [D_188,C_189,B_190,A_191] :
      ( r2_hidden(k1_funct_1(D_188,C_189),B_190)
      | k1_xboole_0 = B_190
      | ~ r2_hidden(C_189,A_191)
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190)))
      | ~ v1_funct_2(D_188,A_191,B_190)
      | ~ v1_funct_1(D_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1372,plain,(
    ! [D_293,A_294,B_295] :
      ( r2_hidden(k1_funct_1(D_293,'#skF_3'(A_294)),B_295)
      | k1_xboole_0 = B_295
      | ~ m1_subset_1(D_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ v1_funct_2(D_293,A_294,B_295)
      | ~ v1_funct_1(D_293)
      | k1_xboole_0 = A_294 ) ),
    inference(resolution,[status(thm)],[c_50,c_964])).

tff(c_1408,plain,(
    ! [B_295,A_294] :
      ( r2_hidden(k1_xboole_0,B_295)
      | k1_xboole_0 = B_295
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ v1_funct_2('#skF_6',A_294,B_295)
      | ~ v1_funct_1('#skF_6')
      | k1_xboole_0 = A_294 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_1372])).

tff(c_1423,plain,(
    ! [B_296,A_297] :
      ( r2_hidden(k1_xboole_0,B_296)
      | k1_xboole_0 = B_296
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_297,B_296)))
      | ~ v1_funct_2('#skF_6',A_297,B_296)
      | k1_xboole_0 = A_297 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1408])).

tff(c_1426,plain,
    ( r2_hidden(k1_xboole_0,'#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_1423])).

tff(c_1435,plain,
    ( r2_hidden(k1_xboole_0,'#skF_5')
    | k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1426])).

tff(c_1436,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_663,c_1435])).

tff(c_8,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1454,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_8])).

tff(c_1460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:37:26 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.71  
% 3.89/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 3.89/1.71  
% 3.89/1.71  %Foreground sorts:
% 3.89/1.71  
% 3.89/1.71  
% 3.89/1.71  %Background operators:
% 3.89/1.71  
% 3.89/1.71  
% 3.89/1.71  %Foreground operators:
% 3.89/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.89/1.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.89/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.89/1.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.89/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.71  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.89/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.89/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.89/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.89/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.71  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.89/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.89/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.89/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.89/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.89/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.89/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.71  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.89/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.89/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.89/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.89/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.89/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.71  
% 3.89/1.73  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.89/1.73  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.89/1.73  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.89/1.73  tff(f_43, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.89/1.73  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.89/1.73  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.89/1.73  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.89/1.73  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.89/1.73  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.89/1.73  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.89/1.73  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 3.89/1.73  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.89/1.73  tff(f_112, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.89/1.73  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 3.89/1.73  tff(f_138, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.89/1.73  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.89/1.73  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.89/1.73  tff(c_18, plain, (![A_12]: (m1_subset_1('#skF_1'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.89/1.73  tff(c_124, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | v1_xboole_0(B_73) | ~m1_subset_1(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.89/1.73  tff(c_12, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.89/1.73  tff(c_91, plain, (![A_65, B_66]: (~r2_hidden(A_65, k2_zfmisc_1(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.73  tff(c_94, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_91])).
% 3.89/1.73  tff(c_137, plain, (![A_72]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_124, c_94])).
% 3.89/1.73  tff(c_140, plain, (![A_74]: (~m1_subset_1(A_74, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_137])).
% 3.89/1.73  tff(c_145, plain, $false, inference(resolution, [status(thm)], [c_18, c_140])).
% 3.89/1.73  tff(c_146, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_137])).
% 3.89/1.73  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.89/1.73  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.89/1.73  tff(c_159, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.73  tff(c_171, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_159])).
% 3.89/1.73  tff(c_178, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.89/1.73  tff(c_192, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_178])).
% 3.89/1.73  tff(c_282, plain, (![B_107, A_108]: (k7_relat_1(B_107, A_108)=B_107 | ~v4_relat_1(B_107, A_108) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.89/1.73  tff(c_291, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_192, c_282])).
% 3.89/1.73  tff(c_300, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_291])).
% 3.89/1.73  tff(c_24, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.89/1.73  tff(c_304, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_300, c_24])).
% 3.89/1.73  tff(c_308, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_304])).
% 3.89/1.73  tff(c_22, plain, (![A_16, B_18]: (k9_relat_1(A_16, k1_tarski(B_18))=k11_relat_1(A_16, B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.89/1.73  tff(c_313, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_308, c_22])).
% 3.89/1.73  tff(c_320, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_313])).
% 3.89/1.73  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.89/1.73  tff(c_433, plain, (![A_135, B_136]: (k1_funct_1(A_135, B_136)=k1_xboole_0 | r2_hidden(B_136, k1_relat_1(A_135)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.89/1.73  tff(c_30, plain, (![B_25, A_24]: (k11_relat_1(B_25, A_24)!=k1_xboole_0 | ~r2_hidden(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.89/1.73  tff(c_444, plain, (![A_137, B_138]: (k11_relat_1(A_137, B_138)!=k1_xboole_0 | k1_funct_1(A_137, B_138)=k1_xboole_0 | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(resolution, [status(thm)], [c_433, c_30])).
% 3.89/1.73  tff(c_450, plain, (![B_138]: (k11_relat_1('#skF_6', B_138)!=k1_xboole_0 | k1_funct_1('#skF_6', B_138)=k1_xboole_0 | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_171, c_444])).
% 3.89/1.73  tff(c_457, plain, (![B_139]: (k11_relat_1('#skF_6', B_139)!=k1_xboole_0 | k1_funct_1('#skF_6', B_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_450])).
% 3.89/1.73  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.89/1.73  tff(c_466, plain, (~r2_hidden(k1_xboole_0, '#skF_5') | k11_relat_1('#skF_6', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_457, c_58])).
% 3.89/1.73  tff(c_472, plain, (~r2_hidden(k1_xboole_0, '#skF_5') | k2_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_320, c_466])).
% 3.89/1.73  tff(c_474, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_472])).
% 3.89/1.73  tff(c_28, plain, (![A_24, B_25]: (r2_hidden(A_24, k1_relat_1(B_25)) | k11_relat_1(B_25, A_24)=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.89/1.73  tff(c_235, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.89/1.73  tff(c_249, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_235])).
% 3.89/1.73  tff(c_586, plain, (![B_160, C_161, A_162]: (r2_hidden(k1_funct_1(B_160, C_161), A_162) | ~r2_hidden(C_161, k1_relat_1(B_160)) | ~v1_funct_1(B_160) | ~v5_relat_1(B_160, A_162) | ~v1_relat_1(B_160))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.89/1.73  tff(c_597, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_586, c_58])).
% 3.89/1.73  tff(c_614, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_249, c_66, c_597])).
% 3.89/1.73  tff(c_651, plain, (k11_relat_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_614])).
% 3.89/1.73  tff(c_660, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_171, c_320, c_651])).
% 3.89/1.73  tff(c_662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_660])).
% 3.89/1.73  tff(c_663, plain, (~r2_hidden(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_472])).
% 3.89/1.73  tff(c_64, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.89/1.73  tff(c_40, plain, (![A_28, B_31]: (k1_funct_1(A_28, B_31)=k1_xboole_0 | r2_hidden(B_31, k1_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.89/1.73  tff(c_664, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_472])).
% 3.89/1.73  tff(c_26, plain, (![A_21, B_22]: (r2_hidden('#skF_2'(A_21, B_22), k2_relat_1(B_22)) | ~r2_hidden(A_21, k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.89/1.73  tff(c_674, plain, (![A_21]: (r2_hidden('#skF_2'(A_21, '#skF_6'), k1_xboole_0) | ~r2_hidden(A_21, k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_664, c_26])).
% 3.89/1.73  tff(c_678, plain, (![A_21]: (r2_hidden('#skF_2'(A_21, '#skF_6'), k1_xboole_0) | ~r2_hidden(A_21, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_674])).
% 3.89/1.73  tff(c_686, plain, (![A_166]: (~r2_hidden(A_166, k1_relat_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_94, c_678])).
% 3.89/1.73  tff(c_690, plain, (![B_31]: (k1_funct_1('#skF_6', B_31)=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_686])).
% 3.89/1.73  tff(c_705, plain, (![B_31]: (k1_funct_1('#skF_6', B_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_66, c_690])).
% 3.89/1.73  tff(c_50, plain, (![A_43]: (r2_hidden('#skF_3'(A_43), A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.89/1.73  tff(c_964, plain, (![D_188, C_189, B_190, A_191]: (r2_hidden(k1_funct_1(D_188, C_189), B_190) | k1_xboole_0=B_190 | ~r2_hidden(C_189, A_191) | ~m1_subset_1(D_188, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))) | ~v1_funct_2(D_188, A_191, B_190) | ~v1_funct_1(D_188))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.73  tff(c_1372, plain, (![D_293, A_294, B_295]: (r2_hidden(k1_funct_1(D_293, '#skF_3'(A_294)), B_295) | k1_xboole_0=B_295 | ~m1_subset_1(D_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~v1_funct_2(D_293, A_294, B_295) | ~v1_funct_1(D_293) | k1_xboole_0=A_294)), inference(resolution, [status(thm)], [c_50, c_964])).
% 3.89/1.73  tff(c_1408, plain, (![B_295, A_294]: (r2_hidden(k1_xboole_0, B_295) | k1_xboole_0=B_295 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~v1_funct_2('#skF_6', A_294, B_295) | ~v1_funct_1('#skF_6') | k1_xboole_0=A_294)), inference(superposition, [status(thm), theory('equality')], [c_705, c_1372])).
% 3.89/1.73  tff(c_1423, plain, (![B_296, A_297]: (r2_hidden(k1_xboole_0, B_296) | k1_xboole_0=B_296 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_297, B_296))) | ~v1_funct_2('#skF_6', A_297, B_296) | k1_xboole_0=A_297)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1408])).
% 3.89/1.73  tff(c_1426, plain, (r2_hidden(k1_xboole_0, '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_1423])).
% 3.89/1.73  tff(c_1435, plain, (r2_hidden(k1_xboole_0, '#skF_5') | k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1426])).
% 3.89/1.73  tff(c_1436, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_663, c_1435])).
% 3.89/1.73  tff(c_8, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.89/1.73  tff(c_1454, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1436, c_8])).
% 3.89/1.73  tff(c_1460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_1454])).
% 3.89/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.73  
% 3.89/1.73  Inference rules
% 3.89/1.73  ----------------------
% 3.89/1.73  #Ref     : 0
% 3.89/1.73  #Sup     : 293
% 3.89/1.73  #Fact    : 0
% 3.89/1.73  #Define  : 0
% 3.89/1.73  #Split   : 8
% 3.89/1.73  #Chain   : 0
% 3.89/1.73  #Close   : 0
% 3.89/1.73  
% 3.89/1.73  Ordering : KBO
% 3.89/1.73  
% 3.89/1.73  Simplification rules
% 3.89/1.73  ----------------------
% 3.89/1.73  #Subsume      : 52
% 3.89/1.73  #Demod        : 257
% 3.89/1.73  #Tautology    : 106
% 3.89/1.73  #SimpNegUnit  : 13
% 3.89/1.73  #BackRed      : 10
% 3.89/1.73  
% 3.89/1.73  #Partial instantiations: 0
% 3.89/1.73  #Strategies tried      : 1
% 3.89/1.73  
% 3.89/1.73  Timing (in seconds)
% 3.89/1.73  ----------------------
% 3.89/1.73  Preprocessing        : 0.36
% 3.89/1.73  Parsing              : 0.19
% 3.89/1.74  CNF conversion       : 0.02
% 3.89/1.74  Main loop            : 0.53
% 3.89/1.74  Inferencing          : 0.19
% 3.89/1.74  Reduction            : 0.18
% 3.89/1.74  Demodulation         : 0.12
% 3.89/1.74  BG Simplification    : 0.03
% 3.89/1.74  Subsumption          : 0.10
% 3.89/1.74  Abstraction          : 0.03
% 3.89/1.74  MUC search           : 0.00
% 3.89/1.74  Cooper               : 0.00
% 3.89/1.74  Total                : 0.93
% 3.89/1.74  Index Insertion      : 0.00
% 3.89/1.74  Index Deletion       : 0.00
% 3.89/1.74  Index Matching       : 0.00
% 3.89/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
