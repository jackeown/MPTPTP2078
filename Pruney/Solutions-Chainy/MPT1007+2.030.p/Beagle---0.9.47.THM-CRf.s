%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:15 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 328 expanded)
%              Number of leaves         :   45 ( 128 expanded)
%              Depth                    :   17
%              Number of atoms          :  182 ( 674 expanded)
%              Number of equality atoms :   67 ( 229 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(c_12,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_166,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_174,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_166])).

tff(c_32,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_184,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_174,c_32])).

tff(c_194,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_239,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_247,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_239])).

tff(c_250,plain,(
    ! [B_83,A_84] :
      ( k7_relat_1(B_83,A_84) = B_83
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_253,plain,
    ( k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_247,c_250])).

tff(c_259,plain,(
    k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_253])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_316,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_20])).

tff(c_320,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_316])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( k9_relat_1(A_14,k1_tarski(B_16)) = k11_relat_1(A_14,B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_326,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_18])).

tff(c_333,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_326])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,k1_relat_1(B_20))
      | k11_relat_1(B_20,A_19) = k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_219,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_227,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_219])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_473,plain,(
    ! [B_114,C_115,A_116] :
      ( r2_hidden(k1_funct_1(B_114,C_115),A_116)
      | ~ r2_hidden(C_115,k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v5_relat_1(B_114,A_116)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_493,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_473,c_58])).

tff(c_504,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_227,c_66,c_493])).

tff(c_509,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_504])).

tff(c_512,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_333,c_509])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_512])).

tff(c_515,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_527,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_515,c_30])).

tff(c_34,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_183,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_174,c_34])).

tff(c_193,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_517,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_193])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_517])).

tff(c_563,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_575,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_60])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_724,plain,(
    ! [A_140,B_141] :
      ( k9_relat_1(A_140,k1_tarski(B_141)) = k11_relat_1(A_140,B_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_573,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_563,c_28])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_571,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_14])).

tff(c_670,plain,(
    ! [C_128,A_129,B_130] :
      ( v4_relat_1(C_128,A_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_675,plain,(
    ! [A_129] : v4_relat_1('#skF_5',A_129) ),
    inference(resolution,[status(thm)],[c_571,c_670])).

tff(c_677,plain,(
    ! [B_132,A_133] :
      ( k7_relat_1(B_132,A_133) = B_132
      | ~ v4_relat_1(B_132,A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_680,plain,(
    ! [A_129] :
      ( k7_relat_1('#skF_5',A_129) = '#skF_5'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_675,c_677])).

tff(c_683,plain,(
    ! [A_129] : k7_relat_1('#skF_5',A_129) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_680])).

tff(c_691,plain,(
    ! [B_135,A_136] :
      ( k2_relat_1(k7_relat_1(B_135,A_136)) = k9_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_700,plain,(
    ! [A_129] :
      ( k9_relat_1('#skF_5',A_129) = k2_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_691])).

tff(c_704,plain,(
    ! [A_129] : k9_relat_1('#skF_5',A_129) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_573,c_700])).

tff(c_731,plain,(
    ! [B_141] :
      ( k11_relat_1('#skF_5',B_141) = '#skF_5'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_704])).

tff(c_741,plain,(
    ! [B_141] : k11_relat_1('#skF_5',B_141) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_731])).

tff(c_564,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_582,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_564])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( k11_relat_1(B_20,A_19) != k1_xboole_0
      | ~ r2_hidden(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_761,plain,(
    ! [B_147,A_148] :
      ( k11_relat_1(B_147,A_148) != '#skF_5'
      | ~ r2_hidden(A_148,k1_relat_1(B_147))
      | ~ v1_relat_1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_24])).

tff(c_764,plain,(
    ! [A_148] :
      ( k11_relat_1('#skF_5',A_148) != '#skF_5'
      | ~ r2_hidden(A_148,'#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_761])).

tff(c_773,plain,(
    ! [A_148] : ~ r2_hidden(A_148,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_741,c_764])).

tff(c_837,plain,(
    ! [A_161,B_162,C_163] :
      ( k2_relset_1(A_161,B_162,C_163) = k2_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_841,plain,(
    ! [A_161,B_162] : k2_relset_1(A_161,B_162,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_571,c_837])).

tff(c_843,plain,(
    ! [A_161,B_162] : k2_relset_1(A_161,B_162,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_841])).

tff(c_56,plain,(
    ! [D_48,C_47,A_45,B_46] :
      ( r2_hidden(k1_funct_1(D_48,C_47),k2_relset_1(A_45,B_46,D_48))
      | k1_xboole_0 = B_46
      | ~ r2_hidden(C_47,A_45)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(D_48,A_45,B_46)
      | ~ v1_funct_1(D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_985,plain,(
    ! [D_179,C_180,A_181,B_182] :
      ( r2_hidden(k1_funct_1(D_179,C_180),k2_relset_1(A_181,B_182,D_179))
      | B_182 = '#skF_5'
      | ~ r2_hidden(C_180,A_181)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(D_179,A_181,B_182)
      | ~ v1_funct_1(D_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_56])).

tff(c_997,plain,(
    ! [C_180,B_162,A_161] :
      ( r2_hidden(k1_funct_1('#skF_5',C_180),'#skF_5')
      | B_162 = '#skF_5'
      | ~ r2_hidden(C_180,A_161)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_2('#skF_5',A_161,B_162)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_985])).

tff(c_1005,plain,(
    ! [C_180,B_162,A_161] :
      ( r2_hidden(k1_funct_1('#skF_5',C_180),'#skF_5')
      | B_162 = '#skF_5'
      | ~ r2_hidden(C_180,A_161)
      | ~ v1_funct_2('#skF_5',A_161,B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_571,c_997])).

tff(c_1009,plain,(
    ! [B_183,C_184,A_185] :
      ( B_183 = '#skF_5'
      | ~ r2_hidden(C_184,A_185)
      | ~ v1_funct_2('#skF_5',A_185,B_183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_773,c_1005])).

tff(c_1022,plain,(
    ! [B_186,A_187] :
      ( B_186 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_187,B_186)
      | v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_4,c_1009])).

tff(c_1025,plain,
    ( '#skF_5' = '#skF_4'
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_1022])).

tff(c_1029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_575,c_1025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:54:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.39  
% 3.07/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.07/1.39  
% 3.07/1.39  %Foreground sorts:
% 3.07/1.39  
% 3.07/1.39  
% 3.07/1.39  %Background operators:
% 3.07/1.39  
% 3.07/1.39  
% 3.07/1.39  %Foreground operators:
% 3.07/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.07/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.07/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.07/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.39  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.39  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.07/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.07/1.39  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.07/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.39  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.07/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.39  
% 3.07/1.41  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.07/1.41  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.07/1.41  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.41  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.07/1.41  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.07/1.41  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.07/1.41  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.07/1.41  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.07/1.41  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.07/1.41  tff(f_92, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.07/1.41  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.07/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.07/1.41  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.07/1.41  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.07/1.41  tff(f_135, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.07/1.41  tff(c_12, plain, (![A_9]: (~v1_xboole_0(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.41  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.07/1.41  tff(c_166, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.07/1.41  tff(c_174, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_166])).
% 3.07/1.41  tff(c_32, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.07/1.41  tff(c_184, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_174, c_32])).
% 3.07/1.41  tff(c_194, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_184])).
% 3.07/1.41  tff(c_239, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.07/1.41  tff(c_247, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_239])).
% 3.07/1.41  tff(c_250, plain, (![B_83, A_84]: (k7_relat_1(B_83, A_84)=B_83 | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.07/1.41  tff(c_253, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_247, c_250])).
% 3.07/1.41  tff(c_259, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_253])).
% 3.07/1.41  tff(c_20, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.07/1.41  tff(c_316, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_259, c_20])).
% 3.07/1.41  tff(c_320, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_316])).
% 3.07/1.41  tff(c_18, plain, (![A_14, B_16]: (k9_relat_1(A_14, k1_tarski(B_16))=k11_relat_1(A_14, B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.07/1.41  tff(c_326, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_320, c_18])).
% 3.07/1.41  tff(c_333, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_326])).
% 3.07/1.41  tff(c_22, plain, (![A_19, B_20]: (r2_hidden(A_19, k1_relat_1(B_20)) | k11_relat_1(B_20, A_19)=k1_xboole_0 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.41  tff(c_219, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.07/1.41  tff(c_227, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_219])).
% 3.07/1.41  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.07/1.41  tff(c_473, plain, (![B_114, C_115, A_116]: (r2_hidden(k1_funct_1(B_114, C_115), A_116) | ~r2_hidden(C_115, k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v5_relat_1(B_114, A_116) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.07/1.41  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.07/1.41  tff(c_493, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_473, c_58])).
% 3.07/1.41  tff(c_504, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_227, c_66, c_493])).
% 3.07/1.41  tff(c_509, plain, (k11_relat_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_504])).
% 3.07/1.41  tff(c_512, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_174, c_333, c_509])).
% 3.07/1.41  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_512])).
% 3.07/1.41  tff(c_515, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_184])).
% 3.07/1.41  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.41  tff(c_527, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_515, c_515, c_30])).
% 3.07/1.41  tff(c_34, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.07/1.41  tff(c_183, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_174, c_34])).
% 3.07/1.41  tff(c_193, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_183])).
% 3.07/1.41  tff(c_517, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_515, c_193])).
% 3.07/1.41  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_527, c_517])).
% 3.07/1.41  tff(c_563, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_183])).
% 3.07/1.41  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.07/1.41  tff(c_575, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_563, c_60])).
% 3.07/1.41  tff(c_64, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.07/1.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.41  tff(c_724, plain, (![A_140, B_141]: (k9_relat_1(A_140, k1_tarski(B_141))=k11_relat_1(A_140, B_141) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.07/1.41  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.41  tff(c_573, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_563, c_563, c_28])).
% 3.07/1.41  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.41  tff(c_571, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_14])).
% 3.07/1.41  tff(c_670, plain, (![C_128, A_129, B_130]: (v4_relat_1(C_128, A_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.07/1.41  tff(c_675, plain, (![A_129]: (v4_relat_1('#skF_5', A_129))), inference(resolution, [status(thm)], [c_571, c_670])).
% 3.07/1.41  tff(c_677, plain, (![B_132, A_133]: (k7_relat_1(B_132, A_133)=B_132 | ~v4_relat_1(B_132, A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.07/1.41  tff(c_680, plain, (![A_129]: (k7_relat_1('#skF_5', A_129)='#skF_5' | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_675, c_677])).
% 3.07/1.41  tff(c_683, plain, (![A_129]: (k7_relat_1('#skF_5', A_129)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_680])).
% 3.07/1.41  tff(c_691, plain, (![B_135, A_136]: (k2_relat_1(k7_relat_1(B_135, A_136))=k9_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.07/1.41  tff(c_700, plain, (![A_129]: (k9_relat_1('#skF_5', A_129)=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_683, c_691])).
% 3.07/1.41  tff(c_704, plain, (![A_129]: (k9_relat_1('#skF_5', A_129)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_573, c_700])).
% 3.07/1.41  tff(c_731, plain, (![B_141]: (k11_relat_1('#skF_5', B_141)='#skF_5' | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_724, c_704])).
% 3.07/1.41  tff(c_741, plain, (![B_141]: (k11_relat_1('#skF_5', B_141)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_731])).
% 3.07/1.41  tff(c_564, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_183])).
% 3.07/1.41  tff(c_582, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_563, c_564])).
% 3.07/1.41  tff(c_24, plain, (![B_20, A_19]: (k11_relat_1(B_20, A_19)!=k1_xboole_0 | ~r2_hidden(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.41  tff(c_761, plain, (![B_147, A_148]: (k11_relat_1(B_147, A_148)!='#skF_5' | ~r2_hidden(A_148, k1_relat_1(B_147)) | ~v1_relat_1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_24])).
% 3.07/1.41  tff(c_764, plain, (![A_148]: (k11_relat_1('#skF_5', A_148)!='#skF_5' | ~r2_hidden(A_148, '#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_761])).
% 3.07/1.41  tff(c_773, plain, (![A_148]: (~r2_hidden(A_148, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_741, c_764])).
% 3.07/1.41  tff(c_837, plain, (![A_161, B_162, C_163]: (k2_relset_1(A_161, B_162, C_163)=k2_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.07/1.41  tff(c_841, plain, (![A_161, B_162]: (k2_relset_1(A_161, B_162, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_571, c_837])).
% 3.07/1.41  tff(c_843, plain, (![A_161, B_162]: (k2_relset_1(A_161, B_162, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_841])).
% 3.07/1.41  tff(c_56, plain, (![D_48, C_47, A_45, B_46]: (r2_hidden(k1_funct_1(D_48, C_47), k2_relset_1(A_45, B_46, D_48)) | k1_xboole_0=B_46 | ~r2_hidden(C_47, A_45) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(D_48, A_45, B_46) | ~v1_funct_1(D_48))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.07/1.41  tff(c_985, plain, (![D_179, C_180, A_181, B_182]: (r2_hidden(k1_funct_1(D_179, C_180), k2_relset_1(A_181, B_182, D_179)) | B_182='#skF_5' | ~r2_hidden(C_180, A_181) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_2(D_179, A_181, B_182) | ~v1_funct_1(D_179))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_56])).
% 3.07/1.41  tff(c_997, plain, (![C_180, B_162, A_161]: (r2_hidden(k1_funct_1('#skF_5', C_180), '#skF_5') | B_162='#skF_5' | ~r2_hidden(C_180, A_161) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_2('#skF_5', A_161, B_162) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_843, c_985])).
% 3.07/1.41  tff(c_1005, plain, (![C_180, B_162, A_161]: (r2_hidden(k1_funct_1('#skF_5', C_180), '#skF_5') | B_162='#skF_5' | ~r2_hidden(C_180, A_161) | ~v1_funct_2('#skF_5', A_161, B_162))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_571, c_997])).
% 3.07/1.41  tff(c_1009, plain, (![B_183, C_184, A_185]: (B_183='#skF_5' | ~r2_hidden(C_184, A_185) | ~v1_funct_2('#skF_5', A_185, B_183))), inference(negUnitSimplification, [status(thm)], [c_773, c_1005])).
% 3.07/1.41  tff(c_1022, plain, (![B_186, A_187]: (B_186='#skF_5' | ~v1_funct_2('#skF_5', A_187, B_186) | v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_4, c_1009])).
% 3.07/1.41  tff(c_1025, plain, ('#skF_5'='#skF_4' | v1_xboole_0(k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_1022])).
% 3.07/1.41  tff(c_1029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_575, c_1025])).
% 3.07/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.41  
% 3.07/1.41  Inference rules
% 3.07/1.41  ----------------------
% 3.07/1.41  #Ref     : 0
% 3.07/1.41  #Sup     : 199
% 3.07/1.41  #Fact    : 0
% 3.07/1.41  #Define  : 0
% 3.07/1.41  #Split   : 4
% 3.07/1.41  #Chain   : 0
% 3.07/1.41  #Close   : 0
% 3.07/1.41  
% 3.07/1.41  Ordering : KBO
% 3.07/1.41  
% 3.07/1.41  Simplification rules
% 3.07/1.41  ----------------------
% 3.07/1.41  #Subsume      : 19
% 3.07/1.41  #Demod        : 137
% 3.07/1.41  #Tautology    : 121
% 3.07/1.41  #SimpNegUnit  : 15
% 3.07/1.41  #BackRed      : 27
% 3.07/1.41  
% 3.07/1.41  #Partial instantiations: 0
% 3.07/1.41  #Strategies tried      : 1
% 3.07/1.41  
% 3.07/1.41  Timing (in seconds)
% 3.07/1.41  ----------------------
% 3.07/1.42  Preprocessing        : 0.32
% 3.07/1.42  Parsing              : 0.17
% 3.07/1.42  CNF conversion       : 0.02
% 3.07/1.42  Main loop            : 0.37
% 3.07/1.42  Inferencing          : 0.14
% 3.07/1.42  Reduction            : 0.12
% 3.07/1.42  Demodulation         : 0.08
% 3.07/1.42  BG Simplification    : 0.02
% 3.07/1.42  Subsumption          : 0.05
% 3.07/1.42  Abstraction          : 0.02
% 3.07/1.42  MUC search           : 0.00
% 3.07/1.42  Cooper               : 0.00
% 3.07/1.42  Total                : 0.74
% 3.07/1.42  Index Insertion      : 0.00
% 3.07/1.42  Index Deletion       : 0.00
% 3.07/1.42  Index Matching       : 0.00
% 3.07/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
