%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:20 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 773 expanded)
%              Number of leaves         :   25 ( 243 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 (2230 expanded)
%              Number of equality atoms :   63 ( 302 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,A_23)
      | ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_176,plain,(
    ! [B_67,A_68] :
      ( r2_hidden(B_67,A_68)
      | ~ m1_subset_1(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [C_30] :
      ( ~ r2_hidden(C_30,'#skF_3')
      | ~ m1_subset_1(C_30,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_188,plain,(
    ! [B_67] :
      ( ~ m1_subset_1(B_67,'#skF_2')
      | ~ m1_subset_1(B_67,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_176,c_38])).

tff(c_191,plain,(
    ! [B_69] :
      ( ~ m1_subset_1(B_69,'#skF_2')
      | ~ m1_subset_1(B_69,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_196,plain,(
    ! [B_24] :
      ( ~ m1_subset_1(B_24,'#skF_3')
      | ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_191])).

tff(c_197,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( r2_hidden(B_24,A_23)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_221,plain,(
    ! [C_77,A_78,B_79] :
      ( r2_hidden(C_77,A_78)
      | ~ r2_hidden(C_77,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_360,plain,(
    ! [B_112,A_113,A_114] :
      ( r2_hidden(B_112,A_113)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_112,A_114)
      | v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_367,plain,(
    ! [B_112] :
      ( r2_hidden(B_112,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_360])).

tff(c_368,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_199,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),A_72)
      | k1_xboole_0 = A_72
      | k1_tarski(B_73) = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,A_23)
      | ~ r2_hidden(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_309,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1('#skF_1'(A_98,B_99),A_98)
      | v1_xboole_0(A_98)
      | k1_xboole_0 = A_98
      | k1_tarski(B_99) = A_98 ) ),
    inference(resolution,[status(thm)],[c_199,c_28])).

tff(c_190,plain,(
    ! [B_67] :
      ( ~ m1_subset_1(B_67,'#skF_2')
      | ~ m1_subset_1(B_67,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_313,plain,(
    ! [B_99] :
      ( ~ m1_subset_1('#skF_1'('#skF_2',B_99),'#skF_3')
      | v1_xboole_0('#skF_2')
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(B_99) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_309,c_190])).

tff(c_319,plain,(
    ! [B_99] :
      ( ~ m1_subset_1('#skF_1'('#skF_2',B_99),'#skF_3')
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(B_99) = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_313])).

tff(c_321,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_326,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_40])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_214,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | k1_xboole_0 = A_72
      | k1_tarski(B_73) = A_72 ) ),
    inference(resolution,[status(thm)],[c_199,c_8])).

tff(c_323,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | A_72 = '#skF_2'
      | k1_tarski(B_73) = A_72 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_214])).

tff(c_370,plain,(
    ! [B_73] :
      ( '#skF_2' = '#skF_3'
      | k1_tarski(B_73) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_368,c_323])).

tff(c_373,plain,(
    ! [B_73] : k1_tarski(B_73) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_370])).

tff(c_10,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [B_44,C_45,A_46] :
      ( r2_hidden(B_44,C_45)
      | ~ r1_tarski(k2_tarski(A_46,B_44),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [B_47,A_48] : r2_hidden(B_47,k2_tarski(A_48,B_47)) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_100,plain,(
    ! [A_49,B_50] : ~ v1_xboole_0(k2_tarski(A_49,B_50)) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_102,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_384,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_102])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_384])).

tff(c_409,plain,(
    ! [B_118] :
      ( r2_hidden(B_118,'#skF_2')
      | ~ m1_subset_1(B_118,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_414,plain,(
    ! [B_118] :
      ( m1_subset_1(B_118,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_118,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_409,c_28])).

tff(c_423,plain,(
    ! [B_119] :
      ( m1_subset_1(B_119,'#skF_2')
      | ~ m1_subset_1(B_119,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_414])).

tff(c_434,plain,(
    ! [B_119] : ~ m1_subset_1(B_119,'#skF_3') ),
    inference(resolution,[status(thm)],[c_423,c_190])).

tff(c_390,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_210,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1('#skF_1'(A_72,B_73),A_72)
      | v1_xboole_0(A_72)
      | k1_xboole_0 = A_72
      | k1_tarski(B_73) = A_72 ) ),
    inference(resolution,[status(thm)],[c_199,c_28])).

tff(c_456,plain,(
    ! [A_126,B_127] :
      ( m1_subset_1('#skF_1'(A_126,B_127),A_126)
      | v1_xboole_0(A_126)
      | A_126 = '#skF_2'
      | k1_tarski(B_127) = A_126 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_210])).

tff(c_467,plain,(
    ! [B_127] :
      ( v1_xboole_0('#skF_3')
      | '#skF_2' = '#skF_3'
      | k1_tarski(B_127) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_456,c_434])).

tff(c_481,plain,(
    ! [B_127] : k1_tarski(B_127) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_390,c_467])).

tff(c_98,plain,(
    ! [A_5] : r2_hidden(A_5,k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_127,plain,(
    ! [B_58,A_59] :
      ( m1_subset_1(B_58,A_59)
      | ~ r2_hidden(B_58,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_133,plain,(
    ! [A_5] :
      ( m1_subset_1(A_5,k1_tarski(A_5))
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_98,c_127])).

tff(c_142,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_tarski(A_5)) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_133])).

tff(c_496,plain,(
    ! [A_5] : m1_subset_1(A_5,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_142])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_496])).

tff(c_513,plain,(
    ! [B_134] :
      ( ~ m1_subset_1('#skF_1'('#skF_2',B_134),'#skF_3')
      | k1_tarski(B_134) = '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_517,plain,(
    ! [B_134] :
      ( k1_tarski(B_134) = '#skF_2'
      | ~ v1_xboole_0('#skF_1'('#skF_2',B_134))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_513])).

tff(c_518,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_519,plain,(
    ! [B_135,A_136,A_137] :
      ( r2_hidden(B_135,A_136)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_135,A_137)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_527,plain,(
    ! [B_135] :
      ( r2_hidden(B_135,'#skF_2')
      | ~ m1_subset_1(B_135,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_519])).

tff(c_533,plain,(
    ! [B_138] :
      ( r2_hidden(B_138,'#skF_2')
      | ~ m1_subset_1(B_138,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_527])).

tff(c_538,plain,(
    ! [B_138] :
      ( m1_subset_1(B_138,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_138,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_533,c_28])).

tff(c_547,plain,(
    ! [B_139] :
      ( m1_subset_1(B_139,'#skF_2')
      | ~ m1_subset_1(B_139,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_538])).

tff(c_558,plain,(
    ! [B_139] : ~ m1_subset_1(B_139,'#skF_3') ),
    inference(resolution,[status(thm)],[c_547,c_190])).

tff(c_560,plain,(
    ! [B_140] : ~ m1_subset_1(B_140,'#skF_3') ),
    inference(resolution,[status(thm)],[c_547,c_190])).

tff(c_564,plain,(
    ! [B_73] :
      ( v1_xboole_0('#skF_3')
      | k1_xboole_0 = '#skF_3'
      | k1_tarski(B_73) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_210,c_560])).

tff(c_571,plain,(
    ! [B_73] : k1_tarski(B_73) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_518,c_564])).

tff(c_582,plain,(
    ! [A_5] : m1_subset_1(A_5,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_142])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_582])).

tff(c_589,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_603,plain,(
    ! [B_73] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski(B_73) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_589,c_214])).

tff(c_606,plain,(
    ! [B_73] : k1_tarski(B_73) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_603])).

tff(c_619,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_102])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_619])).

tff(c_625,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_626,plain,(
    ! [B_144] :
      ( ~ m1_subset_1(B_144,'#skF_3')
      | ~ v1_xboole_0(B_144) ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_631,plain,(
    ! [B_24] :
      ( ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_626])).

tff(c_632,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_654,plain,(
    ! [C_151,A_152,B_153] :
      ( r2_hidden(C_151,A_152)
      | ~ r2_hidden(C_151,B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_802,plain,(
    ! [B_182,A_183,A_184] :
      ( r2_hidden(B_182,A_183)
      | ~ m1_subset_1(A_184,k1_zfmisc_1(A_183))
      | ~ m1_subset_1(B_182,A_184)
      | v1_xboole_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_30,c_654])).

tff(c_810,plain,(
    ! [B_182] :
      ( r2_hidden(B_182,'#skF_2')
      | ~ m1_subset_1(B_182,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_802])).

tff(c_816,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,'#skF_2')
      | ~ m1_subset_1(B_185,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_810])).

tff(c_824,plain,(
    ! [B_185] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_185,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_816,c_8])).

tff(c_830,plain,(
    ! [B_185] : ~ m1_subset_1(B_185,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_824])).

tff(c_634,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_1'(A_147,B_148),A_147)
      | k1_xboole_0 = A_147
      | k1_tarski(B_148) = A_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_650,plain,(
    ! [A_149,B_150] :
      ( ~ v1_xboole_0(A_149)
      | k1_xboole_0 = A_149
      | k1_tarski(B_150) = A_149 ) ),
    inference(resolution,[status(thm)],[c_634,c_8])).

tff(c_653,plain,(
    ! [B_150] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(B_150) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_625,c_650])).

tff(c_670,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_674,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_40])).

tff(c_645,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1('#skF_1'(A_147,B_148),A_147)
      | v1_xboole_0(A_147)
      | k1_xboole_0 = A_147
      | k1_tarski(B_148) = A_147 ) ),
    inference(resolution,[status(thm)],[c_634,c_28])).

tff(c_783,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1('#skF_1'(A_147,B_148),A_147)
      | v1_xboole_0(A_147)
      | A_147 = '#skF_2'
      | k1_tarski(B_148) = A_147 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_645])).

tff(c_831,plain,(
    ! [B_186] : ~ m1_subset_1(B_186,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_824])).

tff(c_835,plain,(
    ! [B_148] :
      ( v1_xboole_0('#skF_3')
      | '#skF_2' = '#skF_3'
      | k1_tarski(B_148) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_783,c_831])).

tff(c_842,plain,(
    ! [B_148] : k1_tarski(B_148) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_632,c_835])).

tff(c_863,plain,(
    ! [A_5] : m1_subset_1(A_5,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_142])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_863])).

tff(c_869,plain,(
    ! [B_150] : k1_tarski(B_150) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_877,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_102])).

tff(c_881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_877])).

tff(c_882,plain,(
    ! [B_24] : ~ v1_xboole_0(B_24) ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_882,c_625])).

tff(c_889,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_891,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_1'(A_195,B_196),A_195)
      | k1_xboole_0 = A_195
      | k1_tarski(B_196) = A_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_907,plain,(
    ! [A_197,B_198] :
      ( ~ v1_xboole_0(A_197)
      | k1_xboole_0 = A_197
      | k1_tarski(B_198) = A_197 ) ),
    inference(resolution,[status(thm)],[c_891,c_8])).

tff(c_909,plain,(
    ! [B_198] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski(B_198) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_889,c_907])).

tff(c_912,plain,(
    ! [B_198] : k1_tarski(B_198) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_909])).

tff(c_919,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_102])).

tff(c_923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:52:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.58  
% 3.30/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.58  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.30/1.58  
% 3.30/1.58  %Foreground sorts:
% 3.30/1.58  
% 3.30/1.58  
% 3.30/1.58  %Background operators:
% 3.30/1.58  
% 3.30/1.58  
% 3.30/1.58  %Foreground operators:
% 3.30/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.30/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.58  
% 3.30/1.60  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.30/1.60  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 3.30/1.60  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.30/1.60  tff(f_64, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.30/1.60  tff(f_36, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 3.30/1.60  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.30/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.30/1.60  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.30/1.60  tff(c_32, plain, (![B_24, A_23]: (m1_subset_1(B_24, A_23) | ~v1_xboole_0(B_24) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.60  tff(c_176, plain, (![B_67, A_68]: (r2_hidden(B_67, A_68) | ~m1_subset_1(B_67, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.60  tff(c_38, plain, (![C_30]: (~r2_hidden(C_30, '#skF_3') | ~m1_subset_1(C_30, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.30/1.60  tff(c_188, plain, (![B_67]: (~m1_subset_1(B_67, '#skF_2') | ~m1_subset_1(B_67, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_176, c_38])).
% 3.30/1.60  tff(c_191, plain, (![B_69]: (~m1_subset_1(B_69, '#skF_2') | ~m1_subset_1(B_69, '#skF_3'))), inference(splitLeft, [status(thm)], [c_188])).
% 3.30/1.60  tff(c_196, plain, (![B_24]: (~m1_subset_1(B_24, '#skF_3') | ~v1_xboole_0(B_24) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_191])).
% 3.30/1.60  tff(c_197, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_196])).
% 3.30/1.60  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.30/1.60  tff(c_30, plain, (![B_24, A_23]: (r2_hidden(B_24, A_23) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.60  tff(c_221, plain, (![C_77, A_78, B_79]: (r2_hidden(C_77, A_78) | ~r2_hidden(C_77, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.30/1.60  tff(c_360, plain, (![B_112, A_113, A_114]: (r2_hidden(B_112, A_113) | ~m1_subset_1(A_114, k1_zfmisc_1(A_113)) | ~m1_subset_1(B_112, A_114) | v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_30, c_221])).
% 3.30/1.60  tff(c_367, plain, (![B_112]: (r2_hidden(B_112, '#skF_2') | ~m1_subset_1(B_112, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_360])).
% 3.30/1.60  tff(c_368, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_367])).
% 3.30/1.60  tff(c_199, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), A_72) | k1_xboole_0=A_72 | k1_tarski(B_73)=A_72)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.60  tff(c_28, plain, (![B_24, A_23]: (m1_subset_1(B_24, A_23) | ~r2_hidden(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.60  tff(c_309, plain, (![A_98, B_99]: (m1_subset_1('#skF_1'(A_98, B_99), A_98) | v1_xboole_0(A_98) | k1_xboole_0=A_98 | k1_tarski(B_99)=A_98)), inference(resolution, [status(thm)], [c_199, c_28])).
% 3.30/1.60  tff(c_190, plain, (![B_67]: (~m1_subset_1(B_67, '#skF_2') | ~m1_subset_1(B_67, '#skF_3'))), inference(splitLeft, [status(thm)], [c_188])).
% 3.30/1.60  tff(c_313, plain, (![B_99]: (~m1_subset_1('#skF_1'('#skF_2', B_99), '#skF_3') | v1_xboole_0('#skF_2') | k1_xboole_0='#skF_2' | k1_tarski(B_99)='#skF_2')), inference(resolution, [status(thm)], [c_309, c_190])).
% 3.30/1.60  tff(c_319, plain, (![B_99]: (~m1_subset_1('#skF_1'('#skF_2', B_99), '#skF_3') | k1_xboole_0='#skF_2' | k1_tarski(B_99)='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_197, c_313])).
% 3.30/1.60  tff(c_321, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_319])).
% 3.30/1.60  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.30/1.60  tff(c_326, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_321, c_40])).
% 3.30/1.60  tff(c_8, plain, (![B_4, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.30/1.60  tff(c_214, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | k1_xboole_0=A_72 | k1_tarski(B_73)=A_72)), inference(resolution, [status(thm)], [c_199, c_8])).
% 3.30/1.60  tff(c_323, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | A_72='#skF_2' | k1_tarski(B_73)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_321, c_214])).
% 3.30/1.60  tff(c_370, plain, (![B_73]: ('#skF_2'='#skF_3' | k1_tarski(B_73)='#skF_3')), inference(resolution, [status(thm)], [c_368, c_323])).
% 3.30/1.60  tff(c_373, plain, (![B_73]: (k1_tarski(B_73)='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_326, c_370])).
% 3.30/1.60  tff(c_10, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.30/1.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.60  tff(c_83, plain, (![B_44, C_45, A_46]: (r2_hidden(B_44, C_45) | ~r1_tarski(k2_tarski(A_46, B_44), C_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.60  tff(c_92, plain, (![B_47, A_48]: (r2_hidden(B_47, k2_tarski(A_48, B_47)))), inference(resolution, [status(thm)], [c_6, c_83])).
% 3.30/1.60  tff(c_100, plain, (![A_49, B_50]: (~v1_xboole_0(k2_tarski(A_49, B_50)))), inference(resolution, [status(thm)], [c_92, c_8])).
% 3.30/1.60  tff(c_102, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 3.30/1.60  tff(c_384, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_102])).
% 3.30/1.60  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_368, c_384])).
% 3.30/1.60  tff(c_409, plain, (![B_118]: (r2_hidden(B_118, '#skF_2') | ~m1_subset_1(B_118, '#skF_3'))), inference(splitRight, [status(thm)], [c_367])).
% 3.30/1.60  tff(c_414, plain, (![B_118]: (m1_subset_1(B_118, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_118, '#skF_3'))), inference(resolution, [status(thm)], [c_409, c_28])).
% 3.30/1.60  tff(c_423, plain, (![B_119]: (m1_subset_1(B_119, '#skF_2') | ~m1_subset_1(B_119, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_197, c_414])).
% 3.30/1.60  tff(c_434, plain, (![B_119]: (~m1_subset_1(B_119, '#skF_3'))), inference(resolution, [status(thm)], [c_423, c_190])).
% 3.30/1.60  tff(c_390, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_367])).
% 3.30/1.60  tff(c_210, plain, (![A_72, B_73]: (m1_subset_1('#skF_1'(A_72, B_73), A_72) | v1_xboole_0(A_72) | k1_xboole_0=A_72 | k1_tarski(B_73)=A_72)), inference(resolution, [status(thm)], [c_199, c_28])).
% 3.30/1.60  tff(c_456, plain, (![A_126, B_127]: (m1_subset_1('#skF_1'(A_126, B_127), A_126) | v1_xboole_0(A_126) | A_126='#skF_2' | k1_tarski(B_127)=A_126)), inference(demodulation, [status(thm), theory('equality')], [c_321, c_210])).
% 3.30/1.60  tff(c_467, plain, (![B_127]: (v1_xboole_0('#skF_3') | '#skF_2'='#skF_3' | k1_tarski(B_127)='#skF_3')), inference(resolution, [status(thm)], [c_456, c_434])).
% 3.30/1.60  tff(c_481, plain, (![B_127]: (k1_tarski(B_127)='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_326, c_390, c_467])).
% 3.30/1.60  tff(c_98, plain, (![A_5]: (r2_hidden(A_5, k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_92])).
% 3.30/1.60  tff(c_127, plain, (![B_58, A_59]: (m1_subset_1(B_58, A_59) | ~r2_hidden(B_58, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.60  tff(c_133, plain, (![A_5]: (m1_subset_1(A_5, k1_tarski(A_5)) | v1_xboole_0(k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_98, c_127])).
% 3.30/1.60  tff(c_142, plain, (![A_5]: (m1_subset_1(A_5, k1_tarski(A_5)))), inference(negUnitSimplification, [status(thm)], [c_102, c_133])).
% 3.30/1.60  tff(c_496, plain, (![A_5]: (m1_subset_1(A_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_142])).
% 3.30/1.60  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_496])).
% 3.30/1.60  tff(c_513, plain, (![B_134]: (~m1_subset_1('#skF_1'('#skF_2', B_134), '#skF_3') | k1_tarski(B_134)='#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 3.30/1.60  tff(c_517, plain, (![B_134]: (k1_tarski(B_134)='#skF_2' | ~v1_xboole_0('#skF_1'('#skF_2', B_134)) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_513])).
% 3.30/1.60  tff(c_518, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_517])).
% 3.30/1.60  tff(c_519, plain, (![B_135, A_136, A_137]: (r2_hidden(B_135, A_136) | ~m1_subset_1(A_137, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_135, A_137) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_30, c_221])).
% 3.30/1.60  tff(c_527, plain, (![B_135]: (r2_hidden(B_135, '#skF_2') | ~m1_subset_1(B_135, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_519])).
% 3.30/1.60  tff(c_533, plain, (![B_138]: (r2_hidden(B_138, '#skF_2') | ~m1_subset_1(B_138, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_518, c_527])).
% 3.30/1.60  tff(c_538, plain, (![B_138]: (m1_subset_1(B_138, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_138, '#skF_3'))), inference(resolution, [status(thm)], [c_533, c_28])).
% 3.30/1.60  tff(c_547, plain, (![B_139]: (m1_subset_1(B_139, '#skF_2') | ~m1_subset_1(B_139, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_197, c_538])).
% 3.30/1.60  tff(c_558, plain, (![B_139]: (~m1_subset_1(B_139, '#skF_3'))), inference(resolution, [status(thm)], [c_547, c_190])).
% 3.30/1.60  tff(c_560, plain, (![B_140]: (~m1_subset_1(B_140, '#skF_3'))), inference(resolution, [status(thm)], [c_547, c_190])).
% 3.30/1.60  tff(c_564, plain, (![B_73]: (v1_xboole_0('#skF_3') | k1_xboole_0='#skF_3' | k1_tarski(B_73)='#skF_3')), inference(resolution, [status(thm)], [c_210, c_560])).
% 3.30/1.60  tff(c_571, plain, (![B_73]: (k1_tarski(B_73)='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_518, c_564])).
% 3.30/1.60  tff(c_582, plain, (![A_5]: (m1_subset_1(A_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_142])).
% 3.30/1.60  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_558, c_582])).
% 3.30/1.60  tff(c_589, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_517])).
% 3.30/1.60  tff(c_603, plain, (![B_73]: (k1_xboole_0='#skF_3' | k1_tarski(B_73)='#skF_3')), inference(resolution, [status(thm)], [c_589, c_214])).
% 3.30/1.60  tff(c_606, plain, (![B_73]: (k1_tarski(B_73)='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_603])).
% 3.30/1.60  tff(c_619, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_606, c_102])).
% 3.30/1.60  tff(c_623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_589, c_619])).
% 3.30/1.60  tff(c_625, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_196])).
% 3.30/1.60  tff(c_626, plain, (![B_144]: (~m1_subset_1(B_144, '#skF_3') | ~v1_xboole_0(B_144))), inference(splitRight, [status(thm)], [c_196])).
% 3.30/1.60  tff(c_631, plain, (![B_24]: (~v1_xboole_0(B_24) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_626])).
% 3.30/1.60  tff(c_632, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_631])).
% 3.30/1.60  tff(c_654, plain, (![C_151, A_152, B_153]: (r2_hidden(C_151, A_152) | ~r2_hidden(C_151, B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.30/1.60  tff(c_802, plain, (![B_182, A_183, A_184]: (r2_hidden(B_182, A_183) | ~m1_subset_1(A_184, k1_zfmisc_1(A_183)) | ~m1_subset_1(B_182, A_184) | v1_xboole_0(A_184))), inference(resolution, [status(thm)], [c_30, c_654])).
% 3.30/1.60  tff(c_810, plain, (![B_182]: (r2_hidden(B_182, '#skF_2') | ~m1_subset_1(B_182, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_802])).
% 3.30/1.60  tff(c_816, plain, (![B_185]: (r2_hidden(B_185, '#skF_2') | ~m1_subset_1(B_185, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_632, c_810])).
% 3.30/1.60  tff(c_824, plain, (![B_185]: (~v1_xboole_0('#skF_2') | ~m1_subset_1(B_185, '#skF_3'))), inference(resolution, [status(thm)], [c_816, c_8])).
% 3.30/1.60  tff(c_830, plain, (![B_185]: (~m1_subset_1(B_185, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_824])).
% 3.30/1.60  tff(c_634, plain, (![A_147, B_148]: (r2_hidden('#skF_1'(A_147, B_148), A_147) | k1_xboole_0=A_147 | k1_tarski(B_148)=A_147)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.60  tff(c_650, plain, (![A_149, B_150]: (~v1_xboole_0(A_149) | k1_xboole_0=A_149 | k1_tarski(B_150)=A_149)), inference(resolution, [status(thm)], [c_634, c_8])).
% 3.30/1.60  tff(c_653, plain, (![B_150]: (k1_xboole_0='#skF_2' | k1_tarski(B_150)='#skF_2')), inference(resolution, [status(thm)], [c_625, c_650])).
% 3.30/1.60  tff(c_670, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_653])).
% 3.30/1.60  tff(c_674, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_670, c_40])).
% 3.30/1.60  tff(c_645, plain, (![A_147, B_148]: (m1_subset_1('#skF_1'(A_147, B_148), A_147) | v1_xboole_0(A_147) | k1_xboole_0=A_147 | k1_tarski(B_148)=A_147)), inference(resolution, [status(thm)], [c_634, c_28])).
% 3.30/1.60  tff(c_783, plain, (![A_147, B_148]: (m1_subset_1('#skF_1'(A_147, B_148), A_147) | v1_xboole_0(A_147) | A_147='#skF_2' | k1_tarski(B_148)=A_147)), inference(demodulation, [status(thm), theory('equality')], [c_670, c_645])).
% 3.30/1.60  tff(c_831, plain, (![B_186]: (~m1_subset_1(B_186, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_824])).
% 3.30/1.60  tff(c_835, plain, (![B_148]: (v1_xboole_0('#skF_3') | '#skF_2'='#skF_3' | k1_tarski(B_148)='#skF_3')), inference(resolution, [status(thm)], [c_783, c_831])).
% 3.30/1.60  tff(c_842, plain, (![B_148]: (k1_tarski(B_148)='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_674, c_632, c_835])).
% 3.30/1.60  tff(c_863, plain, (![A_5]: (m1_subset_1(A_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_842, c_142])).
% 3.30/1.60  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_830, c_863])).
% 3.30/1.60  tff(c_869, plain, (![B_150]: (k1_tarski(B_150)='#skF_2')), inference(splitRight, [status(thm)], [c_653])).
% 3.30/1.60  tff(c_877, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_869, c_102])).
% 3.30/1.60  tff(c_881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_625, c_877])).
% 3.30/1.60  tff(c_882, plain, (![B_24]: (~v1_xboole_0(B_24))), inference(splitRight, [status(thm)], [c_631])).
% 3.30/1.60  tff(c_888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_882, c_625])).
% 3.30/1.60  tff(c_889, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_188])).
% 3.30/1.60  tff(c_891, plain, (![A_195, B_196]: (r2_hidden('#skF_1'(A_195, B_196), A_195) | k1_xboole_0=A_195 | k1_tarski(B_196)=A_195)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.60  tff(c_907, plain, (![A_197, B_198]: (~v1_xboole_0(A_197) | k1_xboole_0=A_197 | k1_tarski(B_198)=A_197)), inference(resolution, [status(thm)], [c_891, c_8])).
% 3.30/1.60  tff(c_909, plain, (![B_198]: (k1_xboole_0='#skF_3' | k1_tarski(B_198)='#skF_3')), inference(resolution, [status(thm)], [c_889, c_907])).
% 3.30/1.60  tff(c_912, plain, (![B_198]: (k1_tarski(B_198)='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_909])).
% 3.30/1.60  tff(c_919, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_912, c_102])).
% 3.30/1.60  tff(c_923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_889, c_919])).
% 3.30/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.60  
% 3.30/1.60  Inference rules
% 3.30/1.60  ----------------------
% 3.30/1.60  #Ref     : 0
% 3.30/1.60  #Sup     : 156
% 3.30/1.60  #Fact    : 0
% 3.30/1.60  #Define  : 0
% 3.30/1.60  #Split   : 8
% 3.30/1.60  #Chain   : 0
% 3.30/1.60  #Close   : 0
% 3.30/1.60  
% 3.30/1.60  Ordering : KBO
% 3.30/1.60  
% 3.30/1.60  Simplification rules
% 3.30/1.60  ----------------------
% 3.30/1.60  #Subsume      : 54
% 3.30/1.60  #Demod        : 117
% 3.30/1.60  #Tautology    : 49
% 3.30/1.60  #SimpNegUnit  : 29
% 3.30/1.60  #BackRed      : 91
% 3.30/1.60  
% 3.30/1.60  #Partial instantiations: 0
% 3.30/1.60  #Strategies tried      : 1
% 3.30/1.60  
% 3.30/1.60  Timing (in seconds)
% 3.30/1.60  ----------------------
% 3.30/1.60  Preprocessing        : 0.32
% 3.30/1.60  Parsing              : 0.16
% 3.30/1.60  CNF conversion       : 0.02
% 3.30/1.60  Main loop            : 0.44
% 3.30/1.60  Inferencing          : 0.17
% 3.30/1.60  Reduction            : 0.13
% 3.30/1.60  Demodulation         : 0.09
% 3.30/1.60  BG Simplification    : 0.03
% 3.30/1.60  Subsumption          : 0.08
% 3.30/1.60  Abstraction          : 0.02
% 3.30/1.60  MUC search           : 0.00
% 3.30/1.60  Cooper               : 0.00
% 3.30/1.61  Total                : 0.81
% 3.30/1.61  Index Insertion      : 0.00
% 3.30/1.61  Index Deletion       : 0.00
% 3.30/1.61  Index Matching       : 0.00
% 3.30/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
