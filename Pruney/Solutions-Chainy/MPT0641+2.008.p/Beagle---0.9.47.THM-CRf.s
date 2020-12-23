%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:39 EST 2020

% Result     : Theorem 29.15s
% Output     : CNFRefutation 29.68s
% Verified   : 
% Statistics : Number of formulae       :  261 (24349 expanded)
%              Number of leaves         :   31 (8280 expanded)
%              Depth                    :   41
%              Number of atoms          :  777 (93699 expanded)
%              Number of equality atoms :  163 (17969 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(k5_relat_1(B,A))
                & k2_relat_1(B) = k1_relat_1(A) )
             => ( v2_funct_1(B)
                & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    v2_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,
    ( ~ v2_funct_1('#skF_7')
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_63,plain,(
    ~ v2_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_56,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    k2_relat_1('#skF_8') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_467,plain,(
    ! [B_107,A_108] :
      ( v2_funct_1(B_107)
      | ~ r1_tarski(k2_relat_1(B_107),k1_relat_1(A_108))
      | ~ v2_funct_1(k5_relat_1(B_107,A_108))
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_473,plain,(
    ! [A_108] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_108))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_108))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_467])).

tff(c_477,plain,(
    ! [A_108] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_108))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_108))
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_473])).

tff(c_479,plain,(
    ! [A_109] :
      ( ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_109))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_477])).

tff(c_486,plain,
    ( ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_479])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_486])).

tff(c_493,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_32,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_5'(A_27),k1_relat_1(A_27))
      | v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_27] :
      ( k1_funct_1(A_27,'#skF_5'(A_27)) = k1_funct_1(A_27,'#skF_6'(A_27))
      | v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_518,plain,(
    ! [A_122,C_123] :
      ( r2_hidden(k4_tarski('#skF_4'(A_122,k2_relat_1(A_122),C_123),C_123),A_122)
      | ~ r2_hidden(C_123,k2_relat_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_524,plain,(
    ! [C_123] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123),C_123),'#skF_8')
      | ~ r2_hidden(C_123,k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_518])).

tff(c_526,plain,(
    ! [C_123] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123),C_123),'#skF_8')
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_524])).

tff(c_534,plain,(
    ! [A_127,C_128,B_129] :
      ( r2_hidden(A_127,k1_relat_1(C_128))
      | ~ r2_hidden(k4_tarski(A_127,B_129),C_128)
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_537,plain,(
    ! [C_123] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_526,c_534])).

tff(c_543,plain,(
    ! [C_123] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_537])).

tff(c_546,plain,(
    ! [C_131,A_132,B_133] :
      ( k1_funct_1(C_131,A_132) = B_133
      | ~ r2_hidden(k4_tarski(A_132,B_133),C_131)
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_549,plain,(
    ! [C_123] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123)) = C_123
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_526,c_546])).

tff(c_555,plain,(
    ! [C_123] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123)) = C_123
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_549])).

tff(c_1073,plain,(
    ! [B_182,C_183,A_184] :
      ( k1_funct_1(k5_relat_1(B_182,C_183),A_184) = k1_funct_1(C_183,k1_funct_1(B_182,A_184))
      | ~ r2_hidden(A_184,k1_relat_1(B_182))
      | ~ v1_funct_1(C_183)
      | ~ v1_relat_1(C_183)
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1106,plain,(
    ! [C_183,C_123] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_183),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123)) = k1_funct_1(C_183,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123)))
      | ~ v1_funct_1(C_183)
      | ~ v1_relat_1(C_183)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_1073])).

tff(c_1136,plain,(
    ! [C_183,C_123] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_183),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123)) = k1_funct_1(C_183,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123)))
      | ~ v1_funct_1(C_183)
      | ~ v1_relat_1(C_183)
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1106])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k5_relat_1(A_22,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_576,plain,(
    ! [A_139,B_140] :
      ( k1_relat_1(k5_relat_1(A_139,B_140)) = k1_relat_1(A_139)
      | ~ r1_tarski(k2_relat_1(A_139),k1_relat_1(B_140))
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_579,plain,(
    ! [B_140] :
      ( k1_relat_1(k5_relat_1('#skF_8',B_140)) = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(B_140))
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_576])).

tff(c_582,plain,(
    ! [B_141] :
      ( k1_relat_1(k5_relat_1('#skF_8',B_141)) = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(B_141))
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_579])).

tff(c_586,plain,
    ( k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_582])).

tff(c_589,plain,(
    k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_586])).

tff(c_581,plain,(
    ! [B_140] :
      ( k1_relat_1(k5_relat_1('#skF_8',B_140)) = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(B_140))
      | ~ v1_relat_1(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_579])).

tff(c_593,plain,
    ( k1_relat_1(k5_relat_1('#skF_8',k5_relat_1('#skF_8','#skF_7'))) = k1_relat_1('#skF_8')
    | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_581])).

tff(c_710,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_713,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20,c_710])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_713])).

tff(c_719,plain,(
    v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( v1_funct_1(k5_relat_1(A_34,B_35))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_737,plain,(
    ! [B_161,A_162] :
      ( v2_funct_1(B_161)
      | ~ r1_tarski(k2_relat_1(B_161),k1_relat_1(A_162))
      | ~ v2_funct_1(k5_relat_1(B_161,A_162))
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_740,plain,(
    ! [B_161] :
      ( v2_funct_1(B_161)
      | ~ r1_tarski(k2_relat_1(B_161),k1_relat_1('#skF_8'))
      | ~ v2_funct_1(k5_relat_1(B_161,k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_737])).

tff(c_745,plain,(
    ! [B_161] :
      ( v2_funct_1(B_161)
      | ~ r1_tarski(k2_relat_1(B_161),k1_relat_1('#skF_8'))
      | ~ v2_funct_1(k5_relat_1(B_161,k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_740])).

tff(c_1049,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_1052,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_1049])).

tff(c_1056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_60,c_58,c_1052])).

tff(c_1058,plain,(
    v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_608,plain,(
    ! [A_142,C_143] :
      ( r2_hidden(k4_tarski(A_142,k1_funct_1(C_143,A_142)),C_143)
      | ~ r2_hidden(A_142,k1_relat_1(C_143))
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10,plain,(
    ! [C_18,A_3,D_21] :
      ( r2_hidden(C_18,k2_relat_1(A_3))
      | ~ r2_hidden(k4_tarski(D_21,C_18),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_627,plain,(
    ! [C_143,A_142] :
      ( r2_hidden(k1_funct_1(C_143,A_142),k2_relat_1(C_143))
      | ~ r2_hidden(A_142,k1_relat_1(C_143))
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(resolution,[status(thm)],[c_608,c_10])).

tff(c_8,plain,(
    ! [A_3,C_18] :
      ( r2_hidden(k4_tarski('#skF_4'(A_3,k2_relat_1(A_3),C_18),C_18),A_3)
      | ~ r2_hidden(C_18,k2_relat_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_680,plain,(
    ! [A_149,C_150] :
      ( r2_hidden('#skF_4'(A_149,k2_relat_1(A_149),C_150),k1_relat_1(A_149))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149)
      | ~ r2_hidden(C_150,k2_relat_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_8,c_534])).

tff(c_683,plain,(
    ! [C_150] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_150),k1_relat_1('#skF_8'))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_150,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_680])).

tff(c_1060,plain,(
    ! [C_150] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_150),k1_relat_1('#skF_8'))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_150,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_683])).

tff(c_1061,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1061])).

tff(c_1064,plain,(
    ! [C_150] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_150),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_150,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_630,plain,(
    ! [C_144,A_145] :
      ( r2_hidden(k1_funct_1(C_144,A_145),k2_relat_1(C_144))
      | ~ r2_hidden(A_145,k1_relat_1(C_144))
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_608,c_10])).

tff(c_639,plain,(
    ! [A_145] :
      ( r2_hidden(k1_funct_1('#skF_8',A_145),k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_145,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_630])).

tff(c_643,plain,(
    ! [A_145] :
      ( r2_hidden(k1_funct_1('#skF_8',A_145),k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_145,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_639])).

tff(c_1141,plain,(
    ! [C_185] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_185),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_185,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_38,plain,(
    ! [B_37,C_39,A_36] :
      ( k1_funct_1(k5_relat_1(B_37,C_39),A_36) = k1_funct_1(C_39,k1_funct_1(B_37,A_36))
      | ~ r2_hidden(A_36,k1_relat_1(B_37))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1143,plain,(
    ! [C_39,C_185] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_39),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_185)) = k1_funct_1(C_39,k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_185)))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_185,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_1141,c_38])).

tff(c_3869,plain,(
    ! [C_305,C_306] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_305),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_306)) = k1_funct_1(C_305,k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_306)))
      | ~ v1_funct_1(C_305)
      | ~ v1_relat_1(C_305)
      | ~ r2_hidden(C_306,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1143])).

tff(c_556,plain,(
    ! [A_3,C_18] :
      ( k1_funct_1(A_3,'#skF_4'(A_3,k2_relat_1(A_3),C_18)) = C_18
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3)
      | ~ r2_hidden(C_18,k2_relat_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_8,c_546])).

tff(c_3890,plain,(
    ! [C_306] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_306))) = C_306
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_306,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_306,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3869,c_556])).

tff(c_3914,plain,(
    ! [C_307] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_307))) = C_307
      | ~ r2_hidden(C_307,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_719,c_1058,c_3890])).

tff(c_3929,plain,(
    ! [C_307] :
      ( r2_hidden(C_307,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_307)),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_307,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3914,c_627])).

tff(c_3949,plain,(
    ! [C_308] :
      ( r2_hidden(C_308,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_308)),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_308,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3929])).

tff(c_3954,plain,(
    ! [C_309] :
      ( r2_hidden(C_309,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_309,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_309),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_643,c_3949])).

tff(c_3959,plain,(
    ! [C_310] :
      ( r2_hidden(C_310,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_310,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_1064,c_3954])).

tff(c_4059,plain,(
    ! [A_142] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_142),k2_relat_1('#skF_7'))
      | ~ r2_hidden(A_142,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_627,c_3959])).

tff(c_4115,plain,(
    ! [A_311] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_311),k2_relat_1('#skF_7'))
      | ~ r2_hidden(A_311,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_4059])).

tff(c_4169,plain,(
    ! [C_123] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_4115])).

tff(c_32930,plain,(
    ! [C_643] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_643))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_643),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_643,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4169])).

tff(c_32943,plain,(
    ! [C_644] :
      ( r2_hidden(k1_funct_1('#skF_7',C_644),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_644),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_644,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_644,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_32930])).

tff(c_32951,plain,(
    ! [C_645] :
      ( r2_hidden(k1_funct_1('#skF_7',C_645),k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_645,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_32943])).

tff(c_32972,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_32951])).

tff(c_32980,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_32972])).

tff(c_32981,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_32980])).

tff(c_32982,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_32981])).

tff(c_32985,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_32982])).

tff(c_32988,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_32985])).

tff(c_32990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_32988])).

tff(c_32992,plain,(
    r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32981])).

tff(c_30,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_6'(A_27),k1_relat_1(A_27))
      | v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_508,plain,(
    ! [A_117] :
      ( '#skF_5'(A_117) != '#skF_6'(A_117)
      | v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_511,plain,
    ( '#skF_5'('#skF_7') != '#skF_6'('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_508,c_493])).

tff(c_514,plain,(
    '#skF_5'('#skF_7') != '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_511])).

tff(c_689,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(k4_tarski('#skF_2'(A_151,B_152),'#skF_1'(A_151,B_152)),A_151)
      | r2_hidden('#skF_3'(A_151,B_152),B_152)
      | k2_relat_1(A_151) = B_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_43,C_45,B_44] :
      ( r2_hidden(A_43,k1_relat_1(C_45))
      | ~ r2_hidden(k4_tarski(A_43,B_44),C_45)
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_700,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_2'(A_151,B_152),k1_relat_1(A_151))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151)
      | r2_hidden('#skF_3'(A_151,B_152),B_152)
      | k2_relat_1(A_151) = B_152 ) ),
    inference(resolution,[status(thm)],[c_689,c_46])).

tff(c_494,plain,(
    v2_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,(
    ! [C_45,A_43,B_44] :
      ( k1_funct_1(C_45,A_43) = B_44
      | ~ r2_hidden(k4_tarski(A_43,B_44),C_45)
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_699,plain,(
    ! [A_151,B_152] :
      ( k1_funct_1(A_151,'#skF_2'(A_151,B_152)) = '#skF_1'(A_151,B_152)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151)
      | r2_hidden('#skF_3'(A_151,B_152),B_152)
      | k2_relat_1(A_151) = B_152 ) ),
    inference(resolution,[status(thm)],[c_689,c_44])).

tff(c_991,plain,(
    ! [C_176,B_177,A_178] :
      ( C_176 = B_177
      | k1_funct_1(A_178,C_176) != k1_funct_1(A_178,B_177)
      | ~ r2_hidden(C_176,k1_relat_1(A_178))
      | ~ r2_hidden(B_177,k1_relat_1(A_178))
      | ~ v2_funct_1(A_178)
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4226,plain,(
    ! [B_312,A_313,B_314] :
      ( B_312 = '#skF_2'(A_313,B_314)
      | k1_funct_1(A_313,B_312) != '#skF_1'(A_313,B_314)
      | ~ r2_hidden('#skF_2'(A_313,B_314),k1_relat_1(A_313))
      | ~ r2_hidden(B_312,k1_relat_1(A_313))
      | ~ v2_funct_1(A_313)
      | ~ v1_funct_1(A_313)
      | ~ v1_relat_1(A_313)
      | ~ v1_funct_1(A_313)
      | ~ v1_relat_1(A_313)
      | r2_hidden('#skF_3'(A_313,B_314),B_314)
      | k2_relat_1(A_313) = B_314 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_991])).

tff(c_4300,plain,(
    ! [C_123,B_314] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123) = '#skF_2'('#skF_8',B_314)
      | C_123 != '#skF_1'('#skF_8',B_314)
      | ~ r2_hidden('#skF_2'('#skF_8',B_314),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123),k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_3'('#skF_8',B_314),B_314)
      | k2_relat_1('#skF_8') = B_314
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_4226])).

tff(c_35617,plain,(
    ! [C_709,B_710] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_709) = '#skF_2'('#skF_8',B_710)
      | C_709 != '#skF_1'('#skF_8',B_710)
      | ~ r2_hidden('#skF_2'('#skF_8',B_710),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_709),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_710),B_710)
      | k1_relat_1('#skF_7') = B_710
      | ~ r2_hidden(C_709,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_56,c_54,c_494,c_4300])).

tff(c_35629,plain,(
    ! [C_709,B_152] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_709) = '#skF_2'('#skF_8',B_152)
      | C_709 != '#skF_1'('#skF_8',B_152)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_709),k1_relat_1('#skF_8'))
      | k1_relat_1('#skF_7') = B_152
      | ~ r2_hidden(C_709,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_3'('#skF_8',B_152),B_152)
      | k2_relat_1('#skF_8') = B_152 ) ),
    inference(resolution,[status(thm)],[c_700,c_35617])).

tff(c_35645,plain,(
    ! [C_711,B_712] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_711) = '#skF_2'('#skF_8',B_712)
      | C_711 != '#skF_1'('#skF_8',B_712)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_711),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_711,k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_712),B_712)
      | k1_relat_1('#skF_7') = B_712 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_35629])).

tff(c_35652,plain,(
    ! [C_713,B_714] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_713) = '#skF_2'('#skF_8',B_714)
      | C_713 != '#skF_1'('#skF_8',B_714)
      | r2_hidden('#skF_3'('#skF_8',B_714),B_714)
      | k1_relat_1('#skF_7') = B_714
      | ~ r2_hidden(C_713,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_35645])).

tff(c_35745,plain,(
    ! [B_714] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_714)
      | '#skF_1'('#skF_8',B_714) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_714),B_714)
      | k1_relat_1('#skF_7') = B_714
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_35652])).

tff(c_35807,plain,(
    ! [B_714] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_714)
      | '#skF_1'('#skF_8',B_714) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_714),B_714)
      | k1_relat_1('#skF_7') = B_714
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_35745])).

tff(c_36155,plain,(
    ! [B_722] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_722)
      | '#skF_1'('#skF_8',B_722) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_722),B_722)
      | k1_relat_1('#skF_7') = B_722 ) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_35807])).

tff(c_36214,plain,(
    ! [B_722] :
      ( k1_funct_1('#skF_8','#skF_2'('#skF_8',B_722)) = '#skF_6'('#skF_7')
      | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7'))
      | '#skF_1'('#skF_8',B_722) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_722),B_722)
      | k1_relat_1('#skF_7') = B_722 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36155,c_555])).

tff(c_36837,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_36214])).

tff(c_36840,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_36837])).

tff(c_36843,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36840])).

tff(c_36845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_36843])).

tff(c_36847,plain,(
    r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36214])).

tff(c_36208,plain,(
    ! [B_722] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_3'('#skF_8',B_722),B_722)
      | k2_relat_1('#skF_8') = B_722
      | '#skF_1'('#skF_8',B_722) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_722),B_722)
      | k1_relat_1('#skF_7') = B_722 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36155,c_700])).

tff(c_36269,plain,(
    ! [B_722] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_1'('#skF_8',B_722) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_722),B_722)
      | k1_relat_1('#skF_7') = B_722 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_36208])).

tff(c_36304,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_36269])).

tff(c_35742,plain,(
    ! [B_714] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_714)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_714)
      | r2_hidden('#skF_3'('#skF_8',B_714),B_714)
      | k1_relat_1('#skF_7') = B_714
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_35652])).

tff(c_35803,plain,(
    ! [B_714] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_714)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_714)
      | r2_hidden('#skF_3'('#skF_8',B_714),B_714)
      | k1_relat_1('#skF_7') = B_714
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_35742])).

tff(c_35810,plain,(
    ! [B_715] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_715)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_715)
      | r2_hidden('#skF_3'('#skF_8',B_715),B_715)
      | k1_relat_1('#skF_7') = B_715 ) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_35803])).

tff(c_35854,plain,(
    ! [B_715] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_3'('#skF_8',B_715),B_715)
      | k2_relat_1('#skF_8') = B_715
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_715)
      | r2_hidden('#skF_3'('#skF_8',B_715),B_715)
      | k1_relat_1('#skF_7') = B_715 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35810,c_700])).

tff(c_35924,plain,(
    ! [B_715] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_715)
      | r2_hidden('#skF_3'('#skF_8',B_715),B_715)
      | k1_relat_1('#skF_7') = B_715 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_35854])).

tff(c_36294,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_35924])).

tff(c_36298,plain,(
    ! [C_39] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_39),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1(C_39,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36294,c_38])).

tff(c_36502,plain,(
    ! [C_726] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_726),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1(C_726,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))
      | ~ v1_funct_1(C_726)
      | ~ v1_relat_1(C_726) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36298])).

tff(c_4111,plain,(
    ! [A_142] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_142),k2_relat_1('#skF_7'))
      | ~ r2_hidden(A_142,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_4059])).

tff(c_36526,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36502,c_4111])).

tff(c_36570,plain,(
    r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36294,c_36526])).

tff(c_36303,plain,(
    ! [C_39] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_39),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1(C_39,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36298])).

tff(c_701,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_1'(A_151,B_152),k2_relat_1(A_151))
      | r2_hidden('#skF_3'(A_151,B_152),B_152)
      | k2_relat_1(A_151) = B_152 ) ),
    inference(resolution,[status(thm)],[c_689,c_10])).

tff(c_4450,plain,(
    ! [A_317] :
      ( r2_hidden('#skF_3'(A_317,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | r2_hidden('#skF_1'(A_317,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(A_317))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_317) ) ),
    inference(resolution,[status(thm)],[c_701,c_3959])).

tff(c_727,plain,(
    ! [A_158,B_159,D_160] :
      ( r2_hidden(k4_tarski('#skF_2'(A_158,B_159),'#skF_1'(A_158,B_159)),A_158)
      | ~ r2_hidden(k4_tarski(D_160,'#skF_3'(A_158,B_159)),A_158)
      | k2_relat_1(A_158) = B_159 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_748,plain,(
    ! [A_163,B_164] :
      ( r2_hidden(k4_tarski('#skF_2'(A_163,B_164),'#skF_1'(A_163,B_164)),A_163)
      | k2_relat_1(A_163) = B_164
      | ~ r2_hidden('#skF_3'(A_163,B_164),k2_relat_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_8,c_727])).

tff(c_760,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_1'(A_163,B_164),k2_relat_1(A_163))
      | k2_relat_1(A_163) = B_164
      | ~ r2_hidden('#skF_3'(A_163,B_164),k2_relat_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_748,c_10])).

tff(c_4481,plain,
    ( r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4450,c_760])).

tff(c_32484,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4481])).

tff(c_544,plain,(
    ! [A_3,C_18] :
      ( r2_hidden('#skF_4'(A_3,k2_relat_1(A_3),C_18),k1_relat_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3)
      | ~ r2_hidden(C_18,k2_relat_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_8,c_534])).

tff(c_999,plain,(
    ! [C_176,A_3,C_18] :
      ( C_176 = '#skF_4'(A_3,k2_relat_1(A_3),C_18)
      | k1_funct_1(A_3,C_176) != C_18
      | ~ r2_hidden(C_176,k1_relat_1(A_3))
      | ~ r2_hidden('#skF_4'(A_3,k2_relat_1(A_3),C_18),k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3)
      | ~ r2_hidden(C_18,k2_relat_1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_991])).

tff(c_41322,plain,(
    ! [A_824,C_825] :
      ( '#skF_4'(A_824,k2_relat_1(A_824),k1_funct_1(A_824,C_825)) = C_825
      | ~ r2_hidden(C_825,k1_relat_1(A_824))
      | ~ r2_hidden('#skF_4'(A_824,k2_relat_1(A_824),k1_funct_1(A_824,C_825)),k1_relat_1(A_824))
      | ~ v2_funct_1(A_824)
      | ~ v1_funct_1(A_824)
      | ~ v1_relat_1(A_824)
      | ~ v1_funct_1(A_824)
      | ~ v1_relat_1(A_824)
      | ~ r2_hidden(k1_funct_1(A_824,C_825),k2_relat_1(A_824)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_999])).

tff(c_41515,plain,(
    ! [A_826,C_827] :
      ( '#skF_4'(A_826,k2_relat_1(A_826),k1_funct_1(A_826,C_827)) = C_827
      | ~ r2_hidden(C_827,k1_relat_1(A_826))
      | ~ v2_funct_1(A_826)
      | ~ v1_funct_1(A_826)
      | ~ v1_relat_1(A_826)
      | ~ r2_hidden(k1_funct_1(A_826,C_827),k2_relat_1(A_826)) ) ),
    inference(resolution,[status(thm)],[c_544,c_41322])).

tff(c_41733,plain,(
    ! [C_828,A_829] :
      ( '#skF_4'(C_828,k2_relat_1(C_828),k1_funct_1(C_828,A_829)) = A_829
      | ~ v2_funct_1(C_828)
      | ~ r2_hidden(A_829,k1_relat_1(C_828))
      | ~ v1_funct_1(C_828)
      | ~ v1_relat_1(C_828) ) ),
    inference(resolution,[status(thm)],[c_627,c_41515])).

tff(c_41884,plain,(
    ! [A_829] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_829)) = A_829
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(A_829,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32484,c_41733])).

tff(c_42011,plain,(
    ! [A_830] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_830)) = A_830
      | ~ r2_hidden(A_830,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_52,c_41884])).

tff(c_3910,plain,(
    ! [C_306] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_306))) = C_306
      | ~ r2_hidden(C_306,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_719,c_1058,c_3890])).

tff(c_32490,plain,(
    ! [C_306] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),C_306))) = C_306
      | ~ r2_hidden(C_306,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32484,c_32484,c_3910])).

tff(c_42955,plain,(
    ! [A_834] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_834) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_834))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_834),k2_relat_1('#skF_7'))
      | ~ r2_hidden(A_834,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42011,c_32490])).

tff(c_42978,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))
    | ~ r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36303,c_42955])).

tff(c_43104,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36294,c_36570,c_42978])).

tff(c_42,plain,(
    ! [A_43,C_45] :
      ( r2_hidden(k4_tarski(A_43,k1_funct_1(C_45,A_43)),C_45)
      | ~ r2_hidden(A_43,k1_relat_1(C_45))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_43732,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))),k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43104,c_42])).

tff(c_43775,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))),k5_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_36294,c_589,c_43732])).

tff(c_44197,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_5'('#skF_7'))),k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_43775])).

tff(c_44207,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_5'('#skF_7'))),k5_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32992,c_44197])).

tff(c_44210,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7','#skF_5'('#skF_7'))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_44207,c_44])).

tff(c_44223,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))) = k1_funct_1('#skF_7','#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_43104,c_44210])).

tff(c_44233,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7','#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44223,c_43104])).

tff(c_44220,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44207])).

tff(c_44230,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44220])).

tff(c_44231,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_44230])).

tff(c_44401,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7','#skF_6'('#skF_7'))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_44231,c_44])).

tff(c_44411,plain,(
    k1_funct_1('#skF_7','#skF_5'('#skF_7')) = k1_funct_1('#skF_7','#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_44233,c_44401])).

tff(c_41728,plain,(
    ! [C_143,A_142] :
      ( '#skF_4'(C_143,k2_relat_1(C_143),k1_funct_1(C_143,A_142)) = A_142
      | ~ v2_funct_1(C_143)
      | ~ r2_hidden(A_142,k1_relat_1(C_143))
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(resolution,[status(thm)],[c_627,c_41515])).

tff(c_44321,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44233,c_41728])).

tff(c_44367,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_36294,c_589,c_52,c_32484,c_44321])).

tff(c_44859,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44411,c_44367])).

tff(c_36308,plain,(
    ! [C_39] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_39),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1(C_39,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36304,c_38])).

tff(c_36628,plain,(
    ! [C_730] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_730),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1(C_730,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))
      | ~ v1_funct_1(C_730)
      | ~ v1_relat_1(C_730) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36308])).

tff(c_36652,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36628,c_4111])).

tff(c_36696,plain,(
    r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36304,c_36652])).

tff(c_36313,plain,(
    ! [C_39] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_39),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1(C_39,k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36308])).

tff(c_42974,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))
    | ~ r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36313,c_42955])).

tff(c_43102,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36304,c_36696,c_42974])).

tff(c_43822,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))),k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43102,c_42])).

tff(c_43865,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))),k5_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_36304,c_589,c_43822])).

tff(c_45640,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_43865])).

tff(c_45650,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36847,c_45640])).

tff(c_45873,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7','#skF_6'('#skF_7'))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_45650,c_44])).

tff(c_45883,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))) = k1_funct_1('#skF_7','#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_43102,c_45873])).

tff(c_45891,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7','#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45883,c_43102])).

tff(c_42005,plain,(
    ! [A_829] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_829)) = A_829
      | ~ r2_hidden(A_829,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_52,c_41884])).

tff(c_45976,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45891,c_42005])).

tff(c_46023,plain,(
    '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36304,c_44859,c_45976])).

tff(c_46098,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46023,c_555])).

tff(c_46124,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32992,c_46098])).

tff(c_46215,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46124,c_555])).

tff(c_46280,plain,(
    '#skF_5'('#skF_7') = '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36847,c_46215])).

tff(c_46282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_46280])).

tff(c_46284,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_36269])).

tff(c_46402,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_543,c_46284])).

tff(c_46405,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_46402])).

tff(c_46408,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_46405])).

tff(c_46410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_46408])).

tff(c_46412,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_35924])).

tff(c_46416,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_543,c_46412])).

tff(c_46420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32992,c_46416])).

tff(c_46422,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) != k2_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_4481])).

tff(c_48516,plain,(
    ! [A_932] :
      ( r2_hidden('#skF_3'(A_932,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | r2_hidden('#skF_2'(A_932,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1(A_932))
      | ~ v1_funct_1(A_932)
      | ~ v1_relat_1(A_932)
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_932) ) ),
    inference(resolution,[status(thm)],[c_700,c_3959])).

tff(c_759,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_2'(A_163,B_164),k1_relat_1(A_163))
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163)
      | k2_relat_1(A_163) = B_164
      | ~ r2_hidden('#skF_3'(A_163,B_164),k2_relat_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_748,c_46])).

tff(c_48524,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48516,c_759])).

tff(c_48548,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48524])).

tff(c_48549,plain,(
    r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_46422,c_48548])).

tff(c_50704,plain,(
    ! [A_996] :
      ( r2_hidden('#skF_3'(A_996,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | k1_funct_1(A_996,'#skF_2'(A_996,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'(A_996,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(A_996)
      | ~ v1_relat_1(A_996)
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_996) ) ),
    inference(resolution,[status(thm)],[c_699,c_3959])).

tff(c_758,plain,(
    ! [A_163,B_164] :
      ( k1_funct_1(A_163,'#skF_2'(A_163,B_164)) = '#skF_1'(A_163,B_164)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163)
      | k2_relat_1(A_163) = B_164
      | ~ r2_hidden('#skF_3'(A_163,B_164),k2_relat_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_748,c_44])).

tff(c_50708,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50704,c_758])).

tff(c_50831,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50708])).

tff(c_50832,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46422,c_50831])).

tff(c_52364,plain,(
    ! [A_1031,C_1032] :
      ( '#skF_4'(A_1031,k2_relat_1(A_1031),k1_funct_1(A_1031,C_1032)) = C_1032
      | ~ r2_hidden(C_1032,k1_relat_1(A_1031))
      | ~ r2_hidden('#skF_4'(A_1031,k2_relat_1(A_1031),k1_funct_1(A_1031,C_1032)),k1_relat_1(A_1031))
      | ~ v2_funct_1(A_1031)
      | ~ v1_funct_1(A_1031)
      | ~ v1_relat_1(A_1031)
      | ~ v1_funct_1(A_1031)
      | ~ v1_relat_1(A_1031)
      | ~ r2_hidden(k1_funct_1(A_1031,C_1032),k2_relat_1(A_1031)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_999])).

tff(c_52564,plain,(
    ! [A_1033,C_1034] :
      ( '#skF_4'(A_1033,k2_relat_1(A_1033),k1_funct_1(A_1033,C_1034)) = C_1034
      | ~ r2_hidden(C_1034,k1_relat_1(A_1033))
      | ~ v2_funct_1(A_1033)
      | ~ v1_funct_1(A_1033)
      | ~ v1_relat_1(A_1033)
      | ~ r2_hidden(k1_funct_1(A_1033,C_1034),k2_relat_1(A_1033)) ) ),
    inference(resolution,[status(thm)],[c_544,c_52364])).

tff(c_52746,plain,(
    ! [C_1035,A_1036] :
      ( '#skF_4'(C_1035,k2_relat_1(C_1035),k1_funct_1(C_1035,A_1036)) = A_1036
      | ~ v2_funct_1(C_1035)
      | ~ r2_hidden(A_1036,k1_relat_1(C_1035))
      | ~ v1_funct_1(C_1035)
      | ~ v1_relat_1(C_1035) ) ),
    inference(resolution,[status(thm)],[c_627,c_52564])).

tff(c_52804,plain,(
    ! [A_1036] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_1036) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_1036))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_1036),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(A_1036,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52746,c_3910])).

tff(c_53051,plain,(
    ! [A_1037] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_1037) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_1037))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_1037),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(A_1037,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_52,c_52804])).

tff(c_53169,plain,(
    ! [A_142] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_142) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_142))
      | ~ r2_hidden(A_142,k1_relat_1('#skF_8'))
      | ~ r2_hidden(A_142,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_627,c_53051])).

tff(c_53231,plain,(
    ! [A_1038] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_1038) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_1038))
      | ~ r2_hidden(A_1038,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_53169])).

tff(c_53342,plain,(
    ! [C_18] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_18)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_18)))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_18,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_544,c_53231])).

tff(c_53709,plain,(
    ! [C_1042] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1042)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1042)))
      | ~ r2_hidden(C_1042,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_50,c_50,c_53342])).

tff(c_53742,plain,(
    ! [C_1042] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1042))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1042),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_1042,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53709,c_627])).

tff(c_54003,plain,(
    ! [C_1047] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1047))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1047),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1047,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_53742])).

tff(c_54023,plain,(
    ! [C_1048] :
      ( r2_hidden(k1_funct_1('#skF_7',C_1048),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1048),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1048,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_1048,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_54003])).

tff(c_54031,plain,(
    ! [C_1049] :
      ( r2_hidden(k1_funct_1('#skF_7',C_1049),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_1049,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_54023])).

tff(c_54046,plain,
    ( r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50832,c_54031])).

tff(c_54083,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48549,c_54046])).

tff(c_16,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r2_hidden('#skF_3'(A_3,B_4),B_4)
      | k2_relat_1(A_3) = B_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4113,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_3'(A_3,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_3,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_16,c_3959])).

tff(c_54194,plain,
    ( r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54083,c_4113])).

tff(c_54202,plain,(
    r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_46422,c_54194])).

tff(c_12,plain,(
    ! [A_3,B_4,D_17] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_hidden(k4_tarski(D_17,'#skF_3'(A_3,B_4)),A_3)
      | k2_relat_1(A_3) = B_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54199,plain,(
    ! [D_17] :
      ( ~ r2_hidden(k4_tarski(D_17,'#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))),'#skF_7')
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54083,c_12])).

tff(c_54229,plain,(
    ! [D_1052] : ~ r2_hidden(k4_tarski(D_1052,'#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46422,c_54199])).

tff(c_54237,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_8,c_54229])).

tff(c_54242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54202,c_54237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:48:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.15/17.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.34/17.28  
% 29.34/17.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.43/17.28  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6
% 29.43/17.28  
% 29.43/17.28  %Foreground sorts:
% 29.43/17.28  
% 29.43/17.28  
% 29.43/17.28  %Background operators:
% 29.43/17.28  
% 29.43/17.28  
% 29.43/17.28  %Foreground operators:
% 29.43/17.28  tff('#skF_5', type, '#skF_5': $i > $i).
% 29.43/17.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 29.43/17.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 29.43/17.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.43/17.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.43/17.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 29.43/17.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 29.43/17.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 29.43/17.28  tff('#skF_7', type, '#skF_7': $i).
% 29.43/17.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 29.43/17.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.43/17.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.43/17.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 29.43/17.28  tff('#skF_8', type, '#skF_8': $i).
% 29.43/17.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.43/17.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.43/17.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.43/17.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.43/17.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.43/17.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.43/17.28  tff('#skF_6', type, '#skF_6': $i > $i).
% 29.43/17.28  
% 29.60/17.33  tff(f_137, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 29.60/17.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.60/17.33  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 29.60/17.33  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 29.60/17.33  tff(f_39, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 29.60/17.33  tff(f_119, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 29.60/17.33  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 29.60/17.33  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 29.60/17.33  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 29.60/17.33  tff(f_81, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 29.60/17.33  tff(c_60, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.60/17.33  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.60/17.33  tff(c_52, plain, (v2_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.60/17.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.60/17.33  tff(c_48, plain, (~v2_funct_1('#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.60/17.33  tff(c_63, plain, (~v2_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 29.60/17.33  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.60/17.33  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.60/17.33  tff(c_50, plain, (k2_relat_1('#skF_8')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.60/17.33  tff(c_467, plain, (![B_107, A_108]: (v2_funct_1(B_107) | ~r1_tarski(k2_relat_1(B_107), k1_relat_1(A_108)) | ~v2_funct_1(k5_relat_1(B_107, A_108)) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_109])).
% 29.60/17.33  tff(c_473, plain, (![A_108]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_108)) | ~v2_funct_1(k5_relat_1('#skF_8', A_108)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_50, c_467])).
% 29.60/17.33  tff(c_477, plain, (![A_108]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_108)) | ~v2_funct_1(k5_relat_1('#skF_8', A_108)) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_473])).
% 29.60/17.33  tff(c_479, plain, (![A_109]: (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_109)) | ~v2_funct_1(k5_relat_1('#skF_8', A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(negUnitSimplification, [status(thm)], [c_63, c_477])).
% 29.60/17.33  tff(c_486, plain, (~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_479])).
% 29.60/17.33  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_486])).
% 29.60/17.33  tff(c_493, plain, (~v2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 29.60/17.33  tff(c_32, plain, (![A_27]: (r2_hidden('#skF_5'(A_27), k1_relat_1(A_27)) | v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 29.60/17.33  tff(c_28, plain, (![A_27]: (k1_funct_1(A_27, '#skF_5'(A_27))=k1_funct_1(A_27, '#skF_6'(A_27)) | v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 29.60/17.33  tff(c_518, plain, (![A_122, C_123]: (r2_hidden(k4_tarski('#skF_4'(A_122, k2_relat_1(A_122), C_123), C_123), A_122) | ~r2_hidden(C_123, k2_relat_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.60/17.33  tff(c_524, plain, (![C_123]: (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), C_123), '#skF_8') | ~r2_hidden(C_123, k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_518])).
% 29.60/17.33  tff(c_526, plain, (![C_123]: (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), C_123), '#skF_8') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_524])).
% 29.60/17.33  tff(c_534, plain, (![A_127, C_128, B_129]: (r2_hidden(A_127, k1_relat_1(C_128)) | ~r2_hidden(k4_tarski(A_127, B_129), C_128) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_119])).
% 29.60/17.33  tff(c_537, plain, (![C_123]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_526, c_534])).
% 29.60/17.33  tff(c_543, plain, (![C_123]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), k1_relat_1('#skF_8')) | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_537])).
% 29.60/17.33  tff(c_546, plain, (![C_131, A_132, B_133]: (k1_funct_1(C_131, A_132)=B_133 | ~r2_hidden(k4_tarski(A_132, B_133), C_131) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_119])).
% 29.60/17.33  tff(c_549, plain, (![C_123]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))=C_123 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_526, c_546])).
% 29.60/17.33  tff(c_555, plain, (![C_123]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))=C_123 | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_549])).
% 29.60/17.33  tff(c_1073, plain, (![B_182, C_183, A_184]: (k1_funct_1(k5_relat_1(B_182, C_183), A_184)=k1_funct_1(C_183, k1_funct_1(B_182, A_184)) | ~r2_hidden(A_184, k1_relat_1(B_182)) | ~v1_funct_1(C_183) | ~v1_relat_1(C_183) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_94])).
% 29.60/17.33  tff(c_1106, plain, (![C_183, C_123]: (k1_funct_1(k5_relat_1('#skF_8', C_183), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))=k1_funct_1(C_183, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))) | ~v1_funct_1(C_183) | ~v1_relat_1(C_183) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_1073])).
% 29.60/17.33  tff(c_1136, plain, (![C_183, C_123]: (k1_funct_1(k5_relat_1('#skF_8', C_183), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))=k1_funct_1(C_183, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))) | ~v1_funct_1(C_183) | ~v1_relat_1(C_183) | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1106])).
% 29.68/17.33  tff(c_20, plain, (![A_22, B_23]: (v1_relat_1(k5_relat_1(A_22, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.68/17.33  tff(c_576, plain, (![A_139, B_140]: (k1_relat_1(k5_relat_1(A_139, B_140))=k1_relat_1(A_139) | ~r1_tarski(k2_relat_1(A_139), k1_relat_1(B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.68/17.33  tff(c_579, plain, (![B_140]: (k1_relat_1(k5_relat_1('#skF_8', B_140))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_576])).
% 29.68/17.33  tff(c_582, plain, (![B_141]: (k1_relat_1(k5_relat_1('#skF_8', B_141))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_141)) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_579])).
% 29.68/17.33  tff(c_586, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_582])).
% 29.68/17.33  tff(c_589, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_586])).
% 29.68/17.33  tff(c_581, plain, (![B_140]: (k1_relat_1(k5_relat_1('#skF_8', B_140))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_140)) | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_579])).
% 29.68/17.33  tff(c_593, plain, (k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_589, c_581])).
% 29.68/17.33  tff(c_710, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_593])).
% 29.68/17.33  tff(c_713, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20, c_710])).
% 29.68/17.33  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_713])).
% 29.68/17.33  tff(c_719, plain, (v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_593])).
% 29.68/17.33  tff(c_34, plain, (![A_34, B_35]: (v1_funct_1(k5_relat_1(A_34, B_35)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 29.68/17.33  tff(c_737, plain, (![B_161, A_162]: (v2_funct_1(B_161) | ~r1_tarski(k2_relat_1(B_161), k1_relat_1(A_162)) | ~v2_funct_1(k5_relat_1(B_161, A_162)) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_109])).
% 29.68/17.33  tff(c_740, plain, (![B_161]: (v2_funct_1(B_161) | ~r1_tarski(k2_relat_1(B_161), k1_relat_1('#skF_8')) | ~v2_funct_1(k5_relat_1(B_161, k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_589, c_737])).
% 29.68/17.33  tff(c_745, plain, (![B_161]: (v2_funct_1(B_161) | ~r1_tarski(k2_relat_1(B_161), k1_relat_1('#skF_8')) | ~v2_funct_1(k5_relat_1(B_161, k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_740])).
% 29.68/17.33  tff(c_1049, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_745])).
% 29.68/17.33  tff(c_1052, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_1049])).
% 29.68/17.33  tff(c_1056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_60, c_58, c_1052])).
% 29.68/17.33  tff(c_1058, plain, (v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_745])).
% 29.68/17.33  tff(c_608, plain, (![A_142, C_143]: (r2_hidden(k4_tarski(A_142, k1_funct_1(C_143, A_142)), C_143) | ~r2_hidden(A_142, k1_relat_1(C_143)) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_119])).
% 29.68/17.33  tff(c_10, plain, (![C_18, A_3, D_21]: (r2_hidden(C_18, k2_relat_1(A_3)) | ~r2_hidden(k4_tarski(D_21, C_18), A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.68/17.33  tff(c_627, plain, (![C_143, A_142]: (r2_hidden(k1_funct_1(C_143, A_142), k2_relat_1(C_143)) | ~r2_hidden(A_142, k1_relat_1(C_143)) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143))), inference(resolution, [status(thm)], [c_608, c_10])).
% 29.68/17.33  tff(c_8, plain, (![A_3, C_18]: (r2_hidden(k4_tarski('#skF_4'(A_3, k2_relat_1(A_3), C_18), C_18), A_3) | ~r2_hidden(C_18, k2_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.68/17.33  tff(c_680, plain, (![A_149, C_150]: (r2_hidden('#skF_4'(A_149, k2_relat_1(A_149), C_150), k1_relat_1(A_149)) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149) | ~r2_hidden(C_150, k2_relat_1(A_149)))), inference(resolution, [status(thm)], [c_8, c_534])).
% 29.68/17.33  tff(c_683, plain, (![C_150]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_150), k1_relat_1('#skF_8')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_150, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_589, c_680])).
% 29.68/17.33  tff(c_1060, plain, (![C_150]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_150), k1_relat_1('#skF_8')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_150, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_683])).
% 29.68/17.33  tff(c_1061, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1060])).
% 29.68/17.33  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1061])).
% 29.68/17.33  tff(c_1064, plain, (![C_150]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_150), k1_relat_1('#skF_8')) | ~r2_hidden(C_150, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(splitRight, [status(thm)], [c_1060])).
% 29.68/17.33  tff(c_630, plain, (![C_144, A_145]: (r2_hidden(k1_funct_1(C_144, A_145), k2_relat_1(C_144)) | ~r2_hidden(A_145, k1_relat_1(C_144)) | ~v1_funct_1(C_144) | ~v1_relat_1(C_144))), inference(resolution, [status(thm)], [c_608, c_10])).
% 29.68/17.33  tff(c_639, plain, (![A_145]: (r2_hidden(k1_funct_1('#skF_8', A_145), k1_relat_1('#skF_7')) | ~r2_hidden(A_145, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_630])).
% 29.68/17.33  tff(c_643, plain, (![A_145]: (r2_hidden(k1_funct_1('#skF_8', A_145), k1_relat_1('#skF_7')) | ~r2_hidden(A_145, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_639])).
% 29.68/17.33  tff(c_1141, plain, (![C_185]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_185), k1_relat_1('#skF_8')) | ~r2_hidden(C_185, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(splitRight, [status(thm)], [c_1060])).
% 29.68/17.33  tff(c_38, plain, (![B_37, C_39, A_36]: (k1_funct_1(k5_relat_1(B_37, C_39), A_36)=k1_funct_1(C_39, k1_funct_1(B_37, A_36)) | ~r2_hidden(A_36, k1_relat_1(B_37)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 29.68/17.33  tff(c_1143, plain, (![C_39, C_185]: (k1_funct_1(k5_relat_1('#skF_8', C_39), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_185))=k1_funct_1(C_39, k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_185))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_185, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_1141, c_38])).
% 29.68/17.33  tff(c_3869, plain, (![C_305, C_306]: (k1_funct_1(k5_relat_1('#skF_8', C_305), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_306))=k1_funct_1(C_305, k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_306))) | ~v1_funct_1(C_305) | ~v1_relat_1(C_305) | ~r2_hidden(C_306, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1143])).
% 29.68/17.33  tff(c_556, plain, (![A_3, C_18]: (k1_funct_1(A_3, '#skF_4'(A_3, k2_relat_1(A_3), C_18))=C_18 | ~v1_funct_1(A_3) | ~v1_relat_1(A_3) | ~r2_hidden(C_18, k2_relat_1(A_3)))), inference(resolution, [status(thm)], [c_8, c_546])).
% 29.68/17.33  tff(c_3890, plain, (![C_306]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_306)))=C_306 | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_306, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_306, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3869, c_556])).
% 29.68/17.33  tff(c_3914, plain, (![C_307]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_307)))=C_307 | ~r2_hidden(C_307, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_719, c_1058, c_3890])).
% 29.68/17.33  tff(c_3929, plain, (![C_307]: (r2_hidden(C_307, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_307)), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_307, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3914, c_627])).
% 29.68/17.33  tff(c_3949, plain, (![C_308]: (r2_hidden(C_308, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_308)), k1_relat_1('#skF_7')) | ~r2_hidden(C_308, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3929])).
% 29.68/17.33  tff(c_3954, plain, (![C_309]: (r2_hidden(C_309, k2_relat_1('#skF_7')) | ~r2_hidden(C_309, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_309), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_643, c_3949])).
% 29.68/17.33  tff(c_3959, plain, (![C_310]: (r2_hidden(C_310, k2_relat_1('#skF_7')) | ~r2_hidden(C_310, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_1064, c_3954])).
% 29.68/17.33  tff(c_4059, plain, (![A_142]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_142), k2_relat_1('#skF_7')) | ~r2_hidden(A_142, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_627, c_3959])).
% 29.68/17.33  tff(c_4115, plain, (![A_311]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_311), k2_relat_1('#skF_7')) | ~r2_hidden(A_311, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_4059])).
% 29.68/17.33  tff(c_4169, plain, (![C_123]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1136, c_4115])).
% 29.68/17.33  tff(c_32930, plain, (![C_643]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_643))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_643), k1_relat_1('#skF_8')) | ~r2_hidden(C_643, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4169])).
% 29.68/17.33  tff(c_32943, plain, (![C_644]: (r2_hidden(k1_funct_1('#skF_7', C_644), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_644), k1_relat_1('#skF_8')) | ~r2_hidden(C_644, k1_relat_1('#skF_7')) | ~r2_hidden(C_644, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_555, c_32930])).
% 29.68/17.33  tff(c_32951, plain, (![C_645]: (r2_hidden(k1_funct_1('#skF_7', C_645), k2_relat_1('#skF_7')) | ~r2_hidden(C_645, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_32943])).
% 29.68/17.33  tff(c_32972, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_28, c_32951])).
% 29.68/17.33  tff(c_32980, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_32972])).
% 29.68/17.33  tff(c_32981, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_493, c_32980])).
% 29.68/17.33  tff(c_32982, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_32981])).
% 29.68/17.33  tff(c_32985, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_32982])).
% 29.68/17.33  tff(c_32988, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_32985])).
% 29.68/17.33  tff(c_32990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_32988])).
% 29.68/17.33  tff(c_32992, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_32981])).
% 29.68/17.33  tff(c_30, plain, (![A_27]: (r2_hidden('#skF_6'(A_27), k1_relat_1(A_27)) | v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 29.68/17.33  tff(c_508, plain, (![A_117]: ('#skF_5'(A_117)!='#skF_6'(A_117) | v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_69])).
% 29.68/17.33  tff(c_511, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_508, c_493])).
% 29.68/17.33  tff(c_514, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_511])).
% 29.68/17.33  tff(c_689, plain, (![A_151, B_152]: (r2_hidden(k4_tarski('#skF_2'(A_151, B_152), '#skF_1'(A_151, B_152)), A_151) | r2_hidden('#skF_3'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.68/17.33  tff(c_46, plain, (![A_43, C_45, B_44]: (r2_hidden(A_43, k1_relat_1(C_45)) | ~r2_hidden(k4_tarski(A_43, B_44), C_45) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 29.68/17.33  tff(c_700, plain, (![A_151, B_152]: (r2_hidden('#skF_2'(A_151, B_152), k1_relat_1(A_151)) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151) | r2_hidden('#skF_3'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(resolution, [status(thm)], [c_689, c_46])).
% 29.68/17.33  tff(c_494, plain, (v2_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 29.68/17.33  tff(c_44, plain, (![C_45, A_43, B_44]: (k1_funct_1(C_45, A_43)=B_44 | ~r2_hidden(k4_tarski(A_43, B_44), C_45) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 29.68/17.33  tff(c_699, plain, (![A_151, B_152]: (k1_funct_1(A_151, '#skF_2'(A_151, B_152))='#skF_1'(A_151, B_152) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151) | r2_hidden('#skF_3'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(resolution, [status(thm)], [c_689, c_44])).
% 29.68/17.34  tff(c_991, plain, (![C_176, B_177, A_178]: (C_176=B_177 | k1_funct_1(A_178, C_176)!=k1_funct_1(A_178, B_177) | ~r2_hidden(C_176, k1_relat_1(A_178)) | ~r2_hidden(B_177, k1_relat_1(A_178)) | ~v2_funct_1(A_178) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_69])).
% 29.68/17.34  tff(c_4226, plain, (![B_312, A_313, B_314]: (B_312='#skF_2'(A_313, B_314) | k1_funct_1(A_313, B_312)!='#skF_1'(A_313, B_314) | ~r2_hidden('#skF_2'(A_313, B_314), k1_relat_1(A_313)) | ~r2_hidden(B_312, k1_relat_1(A_313)) | ~v2_funct_1(A_313) | ~v1_funct_1(A_313) | ~v1_relat_1(A_313) | ~v1_funct_1(A_313) | ~v1_relat_1(A_313) | r2_hidden('#skF_3'(A_313, B_314), B_314) | k2_relat_1(A_313)=B_314)), inference(superposition, [status(thm), theory('equality')], [c_699, c_991])).
% 29.68/17.34  tff(c_4300, plain, (![C_123, B_314]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123)='#skF_2'('#skF_8', B_314) | C_123!='#skF_1'('#skF_8', B_314) | ~r2_hidden('#skF_2'('#skF_8', B_314), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_3'('#skF_8', B_314), B_314) | k2_relat_1('#skF_8')=B_314 | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_555, c_4226])).
% 29.68/17.34  tff(c_35617, plain, (![C_709, B_710]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_709)='#skF_2'('#skF_8', B_710) | C_709!='#skF_1'('#skF_8', B_710) | ~r2_hidden('#skF_2'('#skF_8', B_710), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_709), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_710), B_710) | k1_relat_1('#skF_7')=B_710 | ~r2_hidden(C_709, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_56, c_54, c_494, c_4300])).
% 29.68/17.34  tff(c_35629, plain, (![C_709, B_152]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_709)='#skF_2'('#skF_8', B_152) | C_709!='#skF_1'('#skF_8', B_152) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_709), k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=B_152 | ~r2_hidden(C_709, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_3'('#skF_8', B_152), B_152) | k2_relat_1('#skF_8')=B_152)), inference(resolution, [status(thm)], [c_700, c_35617])).
% 29.68/17.34  tff(c_35645, plain, (![C_711, B_712]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_711)='#skF_2'('#skF_8', B_712) | C_711!='#skF_1'('#skF_8', B_712) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_711), k1_relat_1('#skF_8')) | ~r2_hidden(C_711, k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_712), B_712) | k1_relat_1('#skF_7')=B_712)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_35629])).
% 29.68/17.34  tff(c_35652, plain, (![C_713, B_714]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_713)='#skF_2'('#skF_8', B_714) | C_713!='#skF_1'('#skF_8', B_714) | r2_hidden('#skF_3'('#skF_8', B_714), B_714) | k1_relat_1('#skF_7')=B_714 | ~r2_hidden(C_713, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_35645])).
% 29.68/17.34  tff(c_35745, plain, (![B_714]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_714) | '#skF_1'('#skF_8', B_714)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_714), B_714) | k1_relat_1('#skF_7')=B_714 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_35652])).
% 29.68/17.34  tff(c_35807, plain, (![B_714]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_714) | '#skF_1'('#skF_8', B_714)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_714), B_714) | k1_relat_1('#skF_7')=B_714 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_35745])).
% 29.68/17.34  tff(c_36155, plain, (![B_722]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_722) | '#skF_1'('#skF_8', B_722)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_722), B_722) | k1_relat_1('#skF_7')=B_722)), inference(negUnitSimplification, [status(thm)], [c_493, c_35807])).
% 29.68/17.34  tff(c_36214, plain, (![B_722]: (k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_722))='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7')) | '#skF_1'('#skF_8', B_722)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_722), B_722) | k1_relat_1('#skF_7')=B_722)), inference(superposition, [status(thm), theory('equality')], [c_36155, c_555])).
% 29.68/17.34  tff(c_36837, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_36214])).
% 29.68/17.34  tff(c_36840, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_36837])).
% 29.68/17.34  tff(c_36843, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36840])).
% 29.68/17.34  tff(c_36845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_36843])).
% 29.68/17.34  tff(c_36847, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_36214])).
% 29.68/17.34  tff(c_36208, plain, (![B_722]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_3'('#skF_8', B_722), B_722) | k2_relat_1('#skF_8')=B_722 | '#skF_1'('#skF_8', B_722)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_722), B_722) | k1_relat_1('#skF_7')=B_722)), inference(superposition, [status(thm), theory('equality')], [c_36155, c_700])).
% 29.68/17.34  tff(c_36269, plain, (![B_722]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', B_722)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_722), B_722) | k1_relat_1('#skF_7')=B_722)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_36208])).
% 29.68/17.34  tff(c_36304, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_36269])).
% 29.68/17.34  tff(c_35742, plain, (![B_714]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_714) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_714) | r2_hidden('#skF_3'('#skF_8', B_714), B_714) | k1_relat_1('#skF_7')=B_714 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_32, c_35652])).
% 29.68/17.34  tff(c_35803, plain, (![B_714]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_714) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_714) | r2_hidden('#skF_3'('#skF_8', B_714), B_714) | k1_relat_1('#skF_7')=B_714 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_35742])).
% 29.68/17.34  tff(c_35810, plain, (![B_715]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_715) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_715) | r2_hidden('#skF_3'('#skF_8', B_715), B_715) | k1_relat_1('#skF_7')=B_715)), inference(negUnitSimplification, [status(thm)], [c_493, c_35803])).
% 29.68/17.34  tff(c_35854, plain, (![B_715]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_3'('#skF_8', B_715), B_715) | k2_relat_1('#skF_8')=B_715 | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_715) | r2_hidden('#skF_3'('#skF_8', B_715), B_715) | k1_relat_1('#skF_7')=B_715)), inference(superposition, [status(thm), theory('equality')], [c_35810, c_700])).
% 29.68/17.34  tff(c_35924, plain, (![B_715]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_715) | r2_hidden('#skF_3'('#skF_8', B_715), B_715) | k1_relat_1('#skF_7')=B_715)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_35854])).
% 29.68/17.34  tff(c_36294, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_35924])).
% 29.68/17.34  tff(c_36298, plain, (![C_39]: (k1_funct_1(k5_relat_1('#skF_8', C_39), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1(C_39, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_36294, c_38])).
% 29.68/17.34  tff(c_36502, plain, (![C_726]: (k1_funct_1(k5_relat_1('#skF_8', C_726), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1(C_726, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))) | ~v1_funct_1(C_726) | ~v1_relat_1(C_726))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36298])).
% 29.68/17.34  tff(c_4111, plain, (![A_142]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_142), k2_relat_1('#skF_7')) | ~r2_hidden(A_142, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_4059])).
% 29.68/17.34  tff(c_36526, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36502, c_4111])).
% 29.68/17.34  tff(c_36570, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36294, c_36526])).
% 29.68/17.34  tff(c_36303, plain, (![C_39]: (k1_funct_1(k5_relat_1('#skF_8', C_39), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1(C_39, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36298])).
% 29.68/17.34  tff(c_701, plain, (![A_151, B_152]: (r2_hidden('#skF_1'(A_151, B_152), k2_relat_1(A_151)) | r2_hidden('#skF_3'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(resolution, [status(thm)], [c_689, c_10])).
% 29.68/17.34  tff(c_4450, plain, (![A_317]: (r2_hidden('#skF_3'(A_317, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | r2_hidden('#skF_1'(A_317, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(A_317)) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_317))), inference(resolution, [status(thm)], [c_701, c_3959])).
% 29.68/17.34  tff(c_727, plain, (![A_158, B_159, D_160]: (r2_hidden(k4_tarski('#skF_2'(A_158, B_159), '#skF_1'(A_158, B_159)), A_158) | ~r2_hidden(k4_tarski(D_160, '#skF_3'(A_158, B_159)), A_158) | k2_relat_1(A_158)=B_159)), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.68/17.34  tff(c_748, plain, (![A_163, B_164]: (r2_hidden(k4_tarski('#skF_2'(A_163, B_164), '#skF_1'(A_163, B_164)), A_163) | k2_relat_1(A_163)=B_164 | ~r2_hidden('#skF_3'(A_163, B_164), k2_relat_1(A_163)))), inference(resolution, [status(thm)], [c_8, c_727])).
% 29.68/17.34  tff(c_760, plain, (![A_163, B_164]: (r2_hidden('#skF_1'(A_163, B_164), k2_relat_1(A_163)) | k2_relat_1(A_163)=B_164 | ~r2_hidden('#skF_3'(A_163, B_164), k2_relat_1(A_163)))), inference(resolution, [status(thm)], [c_748, c_10])).
% 29.68/17.34  tff(c_4481, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4450, c_760])).
% 29.68/17.34  tff(c_32484, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_4481])).
% 29.68/17.34  tff(c_544, plain, (![A_3, C_18]: (r2_hidden('#skF_4'(A_3, k2_relat_1(A_3), C_18), k1_relat_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3) | ~r2_hidden(C_18, k2_relat_1(A_3)))), inference(resolution, [status(thm)], [c_8, c_534])).
% 29.68/17.34  tff(c_999, plain, (![C_176, A_3, C_18]: (C_176='#skF_4'(A_3, k2_relat_1(A_3), C_18) | k1_funct_1(A_3, C_176)!=C_18 | ~r2_hidden(C_176, k1_relat_1(A_3)) | ~r2_hidden('#skF_4'(A_3, k2_relat_1(A_3), C_18), k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3) | ~r2_hidden(C_18, k2_relat_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_556, c_991])).
% 29.68/17.34  tff(c_41322, plain, (![A_824, C_825]: ('#skF_4'(A_824, k2_relat_1(A_824), k1_funct_1(A_824, C_825))=C_825 | ~r2_hidden(C_825, k1_relat_1(A_824)) | ~r2_hidden('#skF_4'(A_824, k2_relat_1(A_824), k1_funct_1(A_824, C_825)), k1_relat_1(A_824)) | ~v2_funct_1(A_824) | ~v1_funct_1(A_824) | ~v1_relat_1(A_824) | ~v1_funct_1(A_824) | ~v1_relat_1(A_824) | ~r2_hidden(k1_funct_1(A_824, C_825), k2_relat_1(A_824)))), inference(reflexivity, [status(thm), theory('equality')], [c_999])).
% 29.68/17.34  tff(c_41515, plain, (![A_826, C_827]: ('#skF_4'(A_826, k2_relat_1(A_826), k1_funct_1(A_826, C_827))=C_827 | ~r2_hidden(C_827, k1_relat_1(A_826)) | ~v2_funct_1(A_826) | ~v1_funct_1(A_826) | ~v1_relat_1(A_826) | ~r2_hidden(k1_funct_1(A_826, C_827), k2_relat_1(A_826)))), inference(resolution, [status(thm)], [c_544, c_41322])).
% 29.68/17.34  tff(c_41733, plain, (![C_828, A_829]: ('#skF_4'(C_828, k2_relat_1(C_828), k1_funct_1(C_828, A_829))=A_829 | ~v2_funct_1(C_828) | ~r2_hidden(A_829, k1_relat_1(C_828)) | ~v1_funct_1(C_828) | ~v1_relat_1(C_828))), inference(resolution, [status(thm)], [c_627, c_41515])).
% 29.68/17.34  tff(c_41884, plain, (![A_829]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_829))=A_829 | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(A_829, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_32484, c_41733])).
% 29.68/17.34  tff(c_42011, plain, (![A_830]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_830))=A_830 | ~r2_hidden(A_830, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_52, c_41884])).
% 29.68/17.34  tff(c_3910, plain, (![C_306]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_306)))=C_306 | ~r2_hidden(C_306, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_719, c_1058, c_3890])).
% 29.68/17.34  tff(c_32490, plain, (![C_306]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), C_306)))=C_306 | ~r2_hidden(C_306, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_32484, c_32484, c_3910])).
% 29.68/17.34  tff(c_42955, plain, (![A_834]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_834)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_834)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_834), k2_relat_1('#skF_7')) | ~r2_hidden(A_834, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_42011, c_32490])).
% 29.68/17.34  tff(c_42978, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))) | ~r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36303, c_42955])).
% 29.68/17.34  tff(c_43104, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36294, c_36570, c_42978])).
% 29.68/17.34  tff(c_42, plain, (![A_43, C_45]: (r2_hidden(k4_tarski(A_43, k1_funct_1(C_45, A_43)), C_45) | ~r2_hidden(A_43, k1_relat_1(C_45)) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 29.68/17.34  tff(c_43732, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_43104, c_42])).
% 29.68/17.34  tff(c_43775, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))), k5_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_36294, c_589, c_43732])).
% 29.68/17.34  tff(c_44197, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_5'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_555, c_43775])).
% 29.68/17.34  tff(c_44207, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_5'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_32992, c_44197])).
% 29.68/17.34  tff(c_44210, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', '#skF_5'('#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_44207, c_44])).
% 29.68/17.34  tff(c_44223, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))=k1_funct_1('#skF_7', '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_43104, c_44210])).
% 29.68/17.34  tff(c_44233, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_44223, c_43104])).
% 29.68/17.34  tff(c_44220, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_28, c_44207])).
% 29.68/17.34  tff(c_44230, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44220])).
% 29.68/17.34  tff(c_44231, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_493, c_44230])).
% 29.68/17.34  tff(c_44401, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', '#skF_6'('#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_44231, c_44])).
% 29.68/17.34  tff(c_44411, plain, (k1_funct_1('#skF_7', '#skF_5'('#skF_7'))=k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_44233, c_44401])).
% 29.68/17.34  tff(c_41728, plain, (![C_143, A_142]: ('#skF_4'(C_143, k2_relat_1(C_143), k1_funct_1(C_143, A_142))=A_142 | ~v2_funct_1(C_143) | ~r2_hidden(A_142, k1_relat_1(C_143)) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143))), inference(resolution, [status(thm)], [c_627, c_41515])).
% 29.68/17.34  tff(c_44321, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_44233, c_41728])).
% 29.68/17.34  tff(c_44367, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_36294, c_589, c_52, c_32484, c_44321])).
% 29.68/17.34  tff(c_44859, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_44411, c_44367])).
% 29.68/17.34  tff(c_36308, plain, (![C_39]: (k1_funct_1(k5_relat_1('#skF_8', C_39), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1(C_39, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_36304, c_38])).
% 29.68/17.34  tff(c_36628, plain, (![C_730]: (k1_funct_1(k5_relat_1('#skF_8', C_730), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1(C_730, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))) | ~v1_funct_1(C_730) | ~v1_relat_1(C_730))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36308])).
% 29.68/17.34  tff(c_36652, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36628, c_4111])).
% 29.68/17.34  tff(c_36696, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36304, c_36652])).
% 29.68/17.34  tff(c_36313, plain, (![C_39]: (k1_funct_1(k5_relat_1('#skF_8', C_39), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1(C_39, k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_36308])).
% 29.68/17.34  tff(c_42974, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))) | ~r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36313, c_42955])).
% 29.68/17.34  tff(c_43102, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36304, c_36696, c_42974])).
% 29.68/17.34  tff(c_43822, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_43102, c_42])).
% 29.68/17.34  tff(c_43865, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))))), k5_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_36304, c_589, c_43822])).
% 29.68/17.34  tff(c_45640, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_555, c_43865])).
% 29.68/17.34  tff(c_45650, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36847, c_45640])).
% 29.68/17.34  tff(c_45873, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', '#skF_6'('#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_45650, c_44])).
% 29.68/17.34  tff(c_45883, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))))=k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_43102, c_45873])).
% 29.68/17.34  tff(c_45891, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_45883, c_43102])).
% 29.68/17.34  tff(c_42005, plain, (![A_829]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_829))=A_829 | ~r2_hidden(A_829, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_52, c_41884])).
% 29.68/17.34  tff(c_45976, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_45891, c_42005])).
% 29.68/17.34  tff(c_46023, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36304, c_44859, c_45976])).
% 29.68/17.34  tff(c_46098, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_46023, c_555])).
% 29.68/17.34  tff(c_46124, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32992, c_46098])).
% 29.68/17.34  tff(c_46215, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_46124, c_555])).
% 29.68/17.34  tff(c_46280, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36847, c_46215])).
% 29.68/17.34  tff(c_46282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_46280])).
% 29.68/17.34  tff(c_46284, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_36269])).
% 29.68/17.34  tff(c_46402, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_543, c_46284])).
% 29.68/17.34  tff(c_46405, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_46402])).
% 29.68/17.34  tff(c_46408, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_46405])).
% 29.68/17.34  tff(c_46410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_46408])).
% 29.68/17.34  tff(c_46412, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_35924])).
% 29.68/17.34  tff(c_46416, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_543, c_46412])).
% 29.68/17.34  tff(c_46420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32992, c_46416])).
% 29.68/17.34  tff(c_46422, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))!=k2_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_4481])).
% 29.68/17.34  tff(c_48516, plain, (![A_932]: (r2_hidden('#skF_3'(A_932, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | r2_hidden('#skF_2'(A_932, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1(A_932)) | ~v1_funct_1(A_932) | ~v1_relat_1(A_932) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_932))), inference(resolution, [status(thm)], [c_700, c_3959])).
% 29.68/17.34  tff(c_759, plain, (![A_163, B_164]: (r2_hidden('#skF_2'(A_163, B_164), k1_relat_1(A_163)) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163) | k2_relat_1(A_163)=B_164 | ~r2_hidden('#skF_3'(A_163, B_164), k2_relat_1(A_163)))), inference(resolution, [status(thm)], [c_748, c_46])).
% 29.68/17.34  tff(c_48524, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_48516, c_759])).
% 29.68/17.34  tff(c_48548, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48524])).
% 29.68/17.34  tff(c_48549, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46422, c_48548])).
% 29.68/17.34  tff(c_50704, plain, (![A_996]: (r2_hidden('#skF_3'(A_996, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k1_funct_1(A_996, '#skF_2'(A_996, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'(A_996, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(A_996) | ~v1_relat_1(A_996) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_996))), inference(resolution, [status(thm)], [c_699, c_3959])).
% 29.68/17.34  tff(c_758, plain, (![A_163, B_164]: (k1_funct_1(A_163, '#skF_2'(A_163, B_164))='#skF_1'(A_163, B_164) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163) | k2_relat_1(A_163)=B_164 | ~r2_hidden('#skF_3'(A_163, B_164), k2_relat_1(A_163)))), inference(resolution, [status(thm)], [c_748, c_44])).
% 29.68/17.34  tff(c_50708, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50704, c_758])).
% 29.68/17.34  tff(c_50831, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50708])).
% 29.68/17.34  tff(c_50832, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_46422, c_50831])).
% 29.68/17.34  tff(c_52364, plain, (![A_1031, C_1032]: ('#skF_4'(A_1031, k2_relat_1(A_1031), k1_funct_1(A_1031, C_1032))=C_1032 | ~r2_hidden(C_1032, k1_relat_1(A_1031)) | ~r2_hidden('#skF_4'(A_1031, k2_relat_1(A_1031), k1_funct_1(A_1031, C_1032)), k1_relat_1(A_1031)) | ~v2_funct_1(A_1031) | ~v1_funct_1(A_1031) | ~v1_relat_1(A_1031) | ~v1_funct_1(A_1031) | ~v1_relat_1(A_1031) | ~r2_hidden(k1_funct_1(A_1031, C_1032), k2_relat_1(A_1031)))), inference(reflexivity, [status(thm), theory('equality')], [c_999])).
% 29.68/17.34  tff(c_52564, plain, (![A_1033, C_1034]: ('#skF_4'(A_1033, k2_relat_1(A_1033), k1_funct_1(A_1033, C_1034))=C_1034 | ~r2_hidden(C_1034, k1_relat_1(A_1033)) | ~v2_funct_1(A_1033) | ~v1_funct_1(A_1033) | ~v1_relat_1(A_1033) | ~r2_hidden(k1_funct_1(A_1033, C_1034), k2_relat_1(A_1033)))), inference(resolution, [status(thm)], [c_544, c_52364])).
% 29.68/17.34  tff(c_52746, plain, (![C_1035, A_1036]: ('#skF_4'(C_1035, k2_relat_1(C_1035), k1_funct_1(C_1035, A_1036))=A_1036 | ~v2_funct_1(C_1035) | ~r2_hidden(A_1036, k1_relat_1(C_1035)) | ~v1_funct_1(C_1035) | ~v1_relat_1(C_1035))), inference(resolution, [status(thm)], [c_627, c_52564])).
% 29.68/17.34  tff(c_52804, plain, (![A_1036]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_1036)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_1036)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_1036), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(A_1036, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_52746, c_3910])).
% 29.68/17.34  tff(c_53051, plain, (![A_1037]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_1037)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_1037)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_1037), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(A_1037, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_52, c_52804])).
% 29.68/17.34  tff(c_53169, plain, (![A_142]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_142)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_142)) | ~r2_hidden(A_142, k1_relat_1('#skF_8')) | ~r2_hidden(A_142, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_627, c_53051])).
% 29.68/17.34  tff(c_53231, plain, (![A_1038]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_1038)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_1038)) | ~r2_hidden(A_1038, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_53169])).
% 29.68/17.34  tff(c_53342, plain, (![C_18]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_18))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_18))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_18, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_544, c_53231])).
% 29.68/17.34  tff(c_53709, plain, (![C_1042]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1042))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1042))) | ~r2_hidden(C_1042, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_50, c_50, c_53342])).
% 29.68/17.34  tff(c_53742, plain, (![C_1042]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1042))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1042), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_1042, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_53709, c_627])).
% 29.68/17.34  tff(c_54003, plain, (![C_1047]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1047))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1047), k1_relat_1('#skF_8')) | ~r2_hidden(C_1047, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_53742])).
% 29.68/17.34  tff(c_54023, plain, (![C_1048]: (r2_hidden(k1_funct_1('#skF_7', C_1048), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1048), k1_relat_1('#skF_8')) | ~r2_hidden(C_1048, k1_relat_1('#skF_7')) | ~r2_hidden(C_1048, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_555, c_54003])).
% 29.68/17.34  tff(c_54031, plain, (![C_1049]: (r2_hidden(k1_funct_1('#skF_7', C_1049), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_1049, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_54023])).
% 29.68/17.34  tff(c_54046, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_50832, c_54031])).
% 29.68/17.34  tff(c_54083, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_48549, c_54046])).
% 29.68/17.34  tff(c_16, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r2_hidden('#skF_3'(A_3, B_4), B_4) | k2_relat_1(A_3)=B_4)), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.68/17.34  tff(c_4113, plain, (![A_3]: (r2_hidden('#skF_3'(A_3, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_3, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_3))), inference(resolution, [status(thm)], [c_16, c_3959])).
% 29.68/17.34  tff(c_54194, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54083, c_4113])).
% 29.68/17.34  tff(c_54202, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46422, c_54194])).
% 29.68/17.34  tff(c_12, plain, (![A_3, B_4, D_17]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_hidden(k4_tarski(D_17, '#skF_3'(A_3, B_4)), A_3) | k2_relat_1(A_3)=B_4)), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.68/17.34  tff(c_54199, plain, (![D_17]: (~r2_hidden(k4_tarski(D_17, '#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), '#skF_7') | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_54083, c_12])).
% 29.68/17.34  tff(c_54229, plain, (![D_1052]: (~r2_hidden(k4_tarski(D_1052, '#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46422, c_54199])).
% 29.68/17.34  tff(c_54237, plain, (~r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_8, c_54229])).
% 29.68/17.34  tff(c_54242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54202, c_54237])).
% 29.68/17.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.68/17.34  
% 29.68/17.34  Inference rules
% 29.68/17.34  ----------------------
% 29.68/17.34  #Ref     : 5
% 29.68/17.34  #Sup     : 12010
% 29.68/17.34  #Fact    : 4
% 29.68/17.34  #Define  : 0
% 29.68/17.34  #Split   : 134
% 29.68/17.34  #Chain   : 0
% 29.68/17.34  #Close   : 0
% 29.68/17.34  
% 29.68/17.34  Ordering : KBO
% 29.68/17.34  
% 29.68/17.34  Simplification rules
% 29.68/17.34  ----------------------
% 29.68/17.34  #Subsume      : 2626
% 29.68/17.34  #Demod        : 30312
% 29.68/17.34  #Tautology    : 2639
% 29.68/17.34  #SimpNegUnit  : 807
% 29.68/17.34  #BackRed      : 231
% 29.68/17.34  
% 29.68/17.34  #Partial instantiations: 0
% 29.68/17.34  #Strategies tried      : 1
% 29.68/17.34  
% 29.68/17.34  Timing (in seconds)
% 29.68/17.34  ----------------------
% 29.68/17.34  Preprocessing        : 0.35
% 29.68/17.34  Parsing              : 0.18
% 29.68/17.34  CNF conversion       : 0.03
% 29.68/17.34  Main loop            : 16.12
% 29.68/17.34  Inferencing          : 3.43
% 29.68/17.34  Reduction            : 6.40
% 29.68/17.34  Demodulation         : 5.14
% 29.68/17.34  BG Simplification    : 0.44
% 29.68/17.34  Subsumption          : 5.18
% 29.68/17.34  Abstraction          : 0.82
% 29.68/17.35  MUC search           : 0.00
% 29.68/17.35  Cooper               : 0.00
% 29.68/17.35  Total                : 16.60
% 29.68/17.35  Index Insertion      : 0.00
% 29.68/17.35  Index Deletion       : 0.00
% 29.68/17.35  Index Matching       : 0.00
% 29.68/17.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
