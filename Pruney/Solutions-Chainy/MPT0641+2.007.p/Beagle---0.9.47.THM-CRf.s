%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:39 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :  165 (6675 expanded)
%              Number of leaves         :   31 (2289 expanded)
%              Depth                    :   40
%              Number of atoms          :  425 (24918 expanded)
%              Number of equality atoms :   90 (5008 expanded)
%              Maximal formula depth    :   11 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_508,plain,(
    ! [A_117] :
      ( '#skF_5'(A_117) != '#skF_6'(A_117)
      | v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

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

tff(c_511,plain,
    ( '#skF_5'('#skF_7') != '#skF_6'('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_508,c_493])).

tff(c_514,plain,(
    '#skF_5'('#skF_7') != '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_511])).

tff(c_30,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_6'(A_27),k1_relat_1(A_27))
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

tff(c_494,plain,(
    v2_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_689,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(k4_tarski('#skF_2'(A_151,B_152),'#skF_1'(A_151,B_152)),A_151)
      | r2_hidden('#skF_3'(A_151,B_152),B_152)
      | k2_relat_1(A_151) = B_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [C_18,A_3,D_21] :
      ( r2_hidden(C_18,k2_relat_1(A_3))
      | ~ r2_hidden(k4_tarski(D_21,C_18),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_702,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_1'(A_153,B_154),k2_relat_1(A_153))
      | r2_hidden('#skF_3'(A_153,B_154),B_154)
      | k2_relat_1(A_153) = B_154 ) ),
    inference(resolution,[status(thm)],[c_689,c_10])).

tff(c_706,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_1'('#skF_8',B_154),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_154),B_154)
      | k2_relat_1('#skF_8') = B_154 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_702])).

tff(c_707,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_1'('#skF_8',B_154),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_154),B_154)
      | k1_relat_1('#skF_7') = B_154 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_706])).

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

tff(c_1073,plain,(
    ! [C_182,B_183,A_184] :
      ( k1_funct_1(k5_relat_1(C_182,B_183),A_184) = k1_funct_1(B_183,k1_funct_1(C_182,A_184))
      | ~ r2_hidden(A_184,k1_relat_1(k5_relat_1(C_182,B_183)))
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1112,plain,(
    ! [A_184] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_184) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_184))
      | ~ r2_hidden(A_184,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_1073])).

tff(c_1144,plain,(
    ! [A_185] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_185) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_185))
      | ~ r2_hidden(A_185,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_1112])).

tff(c_1206,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8'))))
    | r2_hidden('#skF_1'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_7'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_707,c_1144])).

tff(c_1233,plain,(
    k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k5_relat_1(A_22,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

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

tff(c_718,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8'))
    | k1_relat_1(k5_relat_1('#skF_8',k5_relat_1('#skF_8','#skF_7'))) = k1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_720,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_718])).

tff(c_1238,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_720])).

tff(c_1248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1238])).

tff(c_1250,plain,(
    k1_relat_1('#skF_7') != k1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1206])).

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

tff(c_1249,plain,
    ( r2_hidden('#skF_1'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_7'))
    | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))) ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_1378,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))) ),
    inference(splitLeft,[status(thm)],[c_1249])).

tff(c_608,plain,(
    ! [A_142,C_143] :
      ( r2_hidden(k4_tarski(A_142,k1_funct_1(C_143,A_142)),C_143)
      | ~ r2_hidden(A_142,k1_relat_1(C_143))
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_627,plain,(
    ! [C_143,A_142] :
      ( r2_hidden(k1_funct_1(C_143,A_142),k2_relat_1(C_143))
      | ~ r2_hidden(A_142,k1_relat_1(C_143))
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(resolution,[status(thm)],[c_608,c_10])).

tff(c_1386,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1378,c_627])).

tff(c_1397,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_1386])).

tff(c_1401,plain,(
    ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1397])).

tff(c_1436,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | k2_relat_1('#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_700,c_1401])).

tff(c_1455,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_1436])).

tff(c_1456,plain,(
    r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1250,c_1455])).

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

tff(c_1433,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | k2_relat_1('#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_699,c_1401])).

tff(c_1451,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_1433])).

tff(c_1452,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1250,c_1451])).

tff(c_24,plain,(
    ! [C_33,B_32,A_27] :
      ( C_33 = B_32
      | k1_funct_1(A_27,C_33) != k1_funct_1(A_27,B_32)
      | ~ r2_hidden(C_33,k1_relat_1(A_27))
      | ~ r2_hidden(B_32,k1_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1498,plain,(
    ! [B_32] :
      ( B_32 = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',B_32) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
      | ~ r2_hidden(B_32,k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1452,c_24])).

tff(c_1591,plain,(
    ! [B_197] :
      ( B_197 = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',B_197) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(B_197,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_494,c_1456,c_1498])).

tff(c_1832,plain,(
    ! [C_204] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_204) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_204)) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_204,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_1591])).

tff(c_1837,plain,(
    ! [C_205] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_205) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | C_205 != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_205,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_205,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_1832])).

tff(c_1893,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_1837])).

tff(c_1925,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1893])).

tff(c_1926,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_1925])).

tff(c_1984,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1926])).

tff(c_1987,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_1984])).

tff(c_1990,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1987])).

tff(c_1992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_1990])).

tff(c_1994,plain,(
    r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1926])).

tff(c_32,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_5'(A_27),k1_relat_1(A_27))
      | v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1890,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1837])).

tff(c_1921,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1890])).

tff(c_1922,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_1921])).

tff(c_1956,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1922])).

tff(c_1970,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1956])).

tff(c_1973,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1970])).

tff(c_1975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_1973])).

tff(c_1977,plain,(
    r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1922])).

tff(c_1251,plain,(
    ! [C_188] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_188)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_188)))
      | ~ r2_hidden(C_188,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_1144])).

tff(c_42,plain,(
    ! [A_43,C_45] :
      ( r2_hidden(k4_tarski(A_43,k1_funct_1(C_45,A_43)),C_45)
      | ~ r2_hidden(A_43,k1_relat_1(C_45))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1264,plain,(
    ! [C_188] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_188),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_188)))),k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_188),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_188,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1251,c_42])).

tff(c_5066,plain,(
    ! [C_323] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_323),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_323)))),k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_323),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_323,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_589,c_1264])).

tff(c_5120,plain,(
    ! [C_324] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_324),k1_funct_1('#skF_7',C_324)),k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_324),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_324,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_324,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_5066])).

tff(c_5123,plain,(
    ! [C_324] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_324)) = k1_funct_1('#skF_7',C_324)
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_324),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_324,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_5120,c_44])).

tff(c_5182,plain,(
    ! [C_327] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_327)) = k1_funct_1('#skF_7',C_327)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_327),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_327,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_5123])).

tff(c_5204,plain,(
    ! [C_123] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_123)) = k1_funct_1('#skF_7',C_123)
      | ~ r2_hidden(C_123,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_5182])).

tff(c_28,plain,(
    ! [A_27] :
      ( k1_funct_1(A_27,'#skF_5'(A_27)) = k1_funct_1(A_27,'#skF_6'(A_27))
      | v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5160,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5120])).

tff(c_5174,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1977,c_1977,c_5160])).

tff(c_5175,plain,
    ( r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_5174])).

tff(c_5346,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_5175])).

tff(c_5349,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_543,c_5346])).

tff(c_5353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_5349])).

tff(c_5355,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5175])).

tff(c_5354,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))),k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5175])).

tff(c_5372,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7','#skF_6'('#skF_7'))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_5354,c_44])).

tff(c_5381,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7','#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_5372])).

tff(c_5408,plain,(
    ! [C_33] :
      ( C_33 = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
      | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),C_33) != k1_funct_1('#skF_7','#skF_6'('#skF_7'))
      | ~ r2_hidden(C_33,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5381,c_24])).

tff(c_5769,plain,(
    ! [C_333] :
      ( C_333 = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
      | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),C_333) != k1_funct_1('#skF_7','#skF_6'('#skF_7'))
      | ~ r2_hidden(C_333,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1058,c_52,c_5355,c_589,c_589,c_5408])).

tff(c_6738,plain,(
    ! [C_352] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_352) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
      | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_352)) != k1_funct_1('#skF_7','#skF_6'('#skF_7'))
      | ~ r2_hidden(C_352,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_543,c_5769])).

tff(c_6768,plain,(
    ! [C_353] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_353) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
      | k1_funct_1('#skF_7',C_353) != k1_funct_1('#skF_7','#skF_6'('#skF_7'))
      | ~ r2_hidden(C_353,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_353,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_6738])).

tff(c_6808,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1994,c_6768])).

tff(c_6887,plain,(
    '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_6808])).

tff(c_6977,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6887,c_555])).

tff(c_7014,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_6977])).

tff(c_7124,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7014,c_555])).

tff(c_7176,plain,(
    '#skF_5'('#skF_7') = '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_7124])).

tff(c_7178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_7176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/2.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.87  
% 8.87/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.87  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6
% 8.87/2.87  
% 8.87/2.87  %Foreground sorts:
% 8.87/2.87  
% 8.87/2.87  
% 8.87/2.87  %Background operators:
% 8.87/2.87  
% 8.87/2.87  
% 8.87/2.87  %Foreground operators:
% 8.87/2.87  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.87/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.87/2.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.87/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.87/2.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.87/2.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.87/2.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.87/2.87  tff('#skF_7', type, '#skF_7': $i).
% 8.87/2.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.87/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.87/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.87/2.87  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.87/2.87  tff('#skF_8', type, '#skF_8': $i).
% 8.87/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.87/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/2.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.87/2.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.87/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.87/2.87  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.87/2.87  
% 8.87/2.90  tff(f_137, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 8.87/2.90  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 8.87/2.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.87/2.90  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 8.87/2.90  tff(f_39, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.87/2.90  tff(f_119, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 8.87/2.90  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 8.87/2.90  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 8.87/2.90  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 8.87/2.90  tff(f_81, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 8.87/2.90  tff(c_60, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.87/2.90  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.87/2.90  tff(c_508, plain, (![A_117]: ('#skF_5'(A_117)!='#skF_6'(A_117) | v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.87/2.90  tff(c_52, plain, (v2_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.87/2.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.87/2.90  tff(c_48, plain, (~v2_funct_1('#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.87/2.90  tff(c_63, plain, (~v2_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 8.87/2.90  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.87/2.90  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.87/2.90  tff(c_50, plain, (k2_relat_1('#skF_8')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.87/2.90  tff(c_467, plain, (![B_107, A_108]: (v2_funct_1(B_107) | ~r1_tarski(k2_relat_1(B_107), k1_relat_1(A_108)) | ~v2_funct_1(k5_relat_1(B_107, A_108)) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.87/2.90  tff(c_473, plain, (![A_108]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_108)) | ~v2_funct_1(k5_relat_1('#skF_8', A_108)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_50, c_467])).
% 8.87/2.90  tff(c_477, plain, (![A_108]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_108)) | ~v2_funct_1(k5_relat_1('#skF_8', A_108)) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_473])).
% 8.87/2.90  tff(c_479, plain, (![A_109]: (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_109)) | ~v2_funct_1(k5_relat_1('#skF_8', A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(negUnitSimplification, [status(thm)], [c_63, c_477])).
% 8.87/2.90  tff(c_486, plain, (~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_479])).
% 8.87/2.90  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_486])).
% 8.87/2.90  tff(c_493, plain, (~v2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 8.87/2.90  tff(c_511, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_508, c_493])).
% 8.87/2.90  tff(c_514, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_511])).
% 8.87/2.90  tff(c_30, plain, (![A_27]: (r2_hidden('#skF_6'(A_27), k1_relat_1(A_27)) | v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.87/2.90  tff(c_518, plain, (![A_122, C_123]: (r2_hidden(k4_tarski('#skF_4'(A_122, k2_relat_1(A_122), C_123), C_123), A_122) | ~r2_hidden(C_123, k2_relat_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.87/2.90  tff(c_524, plain, (![C_123]: (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), C_123), '#skF_8') | ~r2_hidden(C_123, k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_518])).
% 8.87/2.90  tff(c_526, plain, (![C_123]: (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), C_123), '#skF_8') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_524])).
% 8.87/2.90  tff(c_546, plain, (![C_131, A_132, B_133]: (k1_funct_1(C_131, A_132)=B_133 | ~r2_hidden(k4_tarski(A_132, B_133), C_131) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.87/2.90  tff(c_549, plain, (![C_123]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))=C_123 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_526, c_546])).
% 8.87/2.90  tff(c_555, plain, (![C_123]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))=C_123 | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_549])).
% 8.87/2.90  tff(c_534, plain, (![A_127, C_128, B_129]: (r2_hidden(A_127, k1_relat_1(C_128)) | ~r2_hidden(k4_tarski(A_127, B_129), C_128) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.87/2.90  tff(c_537, plain, (![C_123]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_526, c_534])).
% 8.87/2.90  tff(c_543, plain, (![C_123]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123), k1_relat_1('#skF_8')) | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_537])).
% 8.87/2.90  tff(c_494, plain, (v2_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 8.87/2.90  tff(c_689, plain, (![A_151, B_152]: (r2_hidden(k4_tarski('#skF_2'(A_151, B_152), '#skF_1'(A_151, B_152)), A_151) | r2_hidden('#skF_3'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.87/2.90  tff(c_10, plain, (![C_18, A_3, D_21]: (r2_hidden(C_18, k2_relat_1(A_3)) | ~r2_hidden(k4_tarski(D_21, C_18), A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.87/2.90  tff(c_702, plain, (![A_153, B_154]: (r2_hidden('#skF_1'(A_153, B_154), k2_relat_1(A_153)) | r2_hidden('#skF_3'(A_153, B_154), B_154) | k2_relat_1(A_153)=B_154)), inference(resolution, [status(thm)], [c_689, c_10])).
% 8.87/2.90  tff(c_706, plain, (![B_154]: (r2_hidden('#skF_1'('#skF_8', B_154), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_154), B_154) | k2_relat_1('#skF_8')=B_154)), inference(superposition, [status(thm), theory('equality')], [c_50, c_702])).
% 8.87/2.90  tff(c_707, plain, (![B_154]: (r2_hidden('#skF_1'('#skF_8', B_154), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_154), B_154) | k1_relat_1('#skF_7')=B_154)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_706])).
% 8.87/2.90  tff(c_576, plain, (![A_139, B_140]: (k1_relat_1(k5_relat_1(A_139, B_140))=k1_relat_1(A_139) | ~r1_tarski(k2_relat_1(A_139), k1_relat_1(B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.87/2.90  tff(c_579, plain, (![B_140]: (k1_relat_1(k5_relat_1('#skF_8', B_140))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_576])).
% 8.87/2.90  tff(c_582, plain, (![B_141]: (k1_relat_1(k5_relat_1('#skF_8', B_141))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_141)) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_579])).
% 8.87/2.90  tff(c_586, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_582])).
% 8.87/2.90  tff(c_589, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_586])).
% 8.87/2.90  tff(c_1073, plain, (![C_182, B_183, A_184]: (k1_funct_1(k5_relat_1(C_182, B_183), A_184)=k1_funct_1(B_183, k1_funct_1(C_182, A_184)) | ~r2_hidden(A_184, k1_relat_1(k5_relat_1(C_182, B_183))) | ~v1_funct_1(C_182) | ~v1_relat_1(C_182) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.87/2.90  tff(c_1112, plain, (![A_184]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_184)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_184)) | ~r2_hidden(A_184, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_589, c_1073])).
% 8.87/2.90  tff(c_1144, plain, (![A_185]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_185)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_185)) | ~r2_hidden(A_185, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_1112])).
% 8.87/2.90  tff(c_1206, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))) | r2_hidden('#skF_1'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_707, c_1144])).
% 8.87/2.90  tff(c_1233, plain, (k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1206])).
% 8.87/2.90  tff(c_20, plain, (![A_22, B_23]: (v1_relat_1(k5_relat_1(A_22, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.87/2.90  tff(c_581, plain, (![B_140]: (k1_relat_1(k5_relat_1('#skF_8', B_140))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(B_140)) | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_579])).
% 8.87/2.90  tff(c_593, plain, (k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_589, c_581])).
% 8.87/2.90  tff(c_710, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_593])).
% 8.87/2.90  tff(c_713, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20, c_710])).
% 8.87/2.90  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_713])).
% 8.87/2.90  tff(c_718, plain, (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))=k1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_593])).
% 8.87/2.90  tff(c_720, plain, (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_718])).
% 8.87/2.90  tff(c_1238, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_720])).
% 8.87/2.90  tff(c_1248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1238])).
% 8.87/2.90  tff(c_1250, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_1206])).
% 8.87/2.90  tff(c_46, plain, (![A_43, C_45, B_44]: (r2_hidden(A_43, k1_relat_1(C_45)) | ~r2_hidden(k4_tarski(A_43, B_44), C_45) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.87/2.90  tff(c_700, plain, (![A_151, B_152]: (r2_hidden('#skF_2'(A_151, B_152), k1_relat_1(A_151)) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151) | r2_hidden('#skF_3'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(resolution, [status(thm)], [c_689, c_46])).
% 8.87/2.90  tff(c_719, plain, (v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_593])).
% 8.87/2.90  tff(c_34, plain, (![A_34, B_35]: (v1_funct_1(k5_relat_1(A_34, B_35)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.87/2.90  tff(c_737, plain, (![B_161, A_162]: (v2_funct_1(B_161) | ~r1_tarski(k2_relat_1(B_161), k1_relat_1(A_162)) | ~v2_funct_1(k5_relat_1(B_161, A_162)) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.87/2.90  tff(c_740, plain, (![B_161]: (v2_funct_1(B_161) | ~r1_tarski(k2_relat_1(B_161), k1_relat_1('#skF_8')) | ~v2_funct_1(k5_relat_1(B_161, k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_589, c_737])).
% 8.87/2.90  tff(c_745, plain, (![B_161]: (v2_funct_1(B_161) | ~r1_tarski(k2_relat_1(B_161), k1_relat_1('#skF_8')) | ~v2_funct_1(k5_relat_1(B_161, k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_740])).
% 8.87/2.90  tff(c_1049, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_745])).
% 8.87/2.90  tff(c_1052, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_1049])).
% 8.87/2.90  tff(c_1056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_60, c_58, c_1052])).
% 8.87/2.90  tff(c_1058, plain, (v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_745])).
% 8.87/2.90  tff(c_1249, plain, (r2_hidden('#skF_1'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_7')) | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8'))))), inference(splitRight, [status(thm)], [c_1206])).
% 8.87/2.90  tff(c_1378, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8'))))), inference(splitLeft, [status(thm)], [c_1249])).
% 8.87/2.90  tff(c_608, plain, (![A_142, C_143]: (r2_hidden(k4_tarski(A_142, k1_funct_1(C_143, A_142)), C_143) | ~r2_hidden(A_142, k1_relat_1(C_143)) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.87/2.90  tff(c_627, plain, (![C_143, A_142]: (r2_hidden(k1_funct_1(C_143, A_142), k2_relat_1(C_143)) | ~r2_hidden(A_142, k1_relat_1(C_143)) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143))), inference(resolution, [status(thm)], [c_608, c_10])).
% 8.87/2.90  tff(c_1386, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1378, c_627])).
% 8.87/2.90  tff(c_1397, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_1386])).
% 8.87/2.90  tff(c_1401, plain, (~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1397])).
% 8.87/2.90  tff(c_1436, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | k2_relat_1('#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_700, c_1401])).
% 8.87/2.90  tff(c_1455, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_1436])).
% 8.87/2.90  tff(c_1456, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1250, c_1455])).
% 8.87/2.90  tff(c_44, plain, (![C_45, A_43, B_44]: (k1_funct_1(C_45, A_43)=B_44 | ~r2_hidden(k4_tarski(A_43, B_44), C_45) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.87/2.90  tff(c_699, plain, (![A_151, B_152]: (k1_funct_1(A_151, '#skF_2'(A_151, B_152))='#skF_1'(A_151, B_152) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151) | r2_hidden('#skF_3'(A_151, B_152), B_152) | k2_relat_1(A_151)=B_152)), inference(resolution, [status(thm)], [c_689, c_44])).
% 8.87/2.90  tff(c_1433, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | k2_relat_1('#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_699, c_1401])).
% 8.87/2.90  tff(c_1451, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_1433])).
% 8.87/2.90  tff(c_1452, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1250, c_1451])).
% 8.87/2.90  tff(c_24, plain, (![C_33, B_32, A_27]: (C_33=B_32 | k1_funct_1(A_27, C_33)!=k1_funct_1(A_27, B_32) | ~r2_hidden(C_33, k1_relat_1(A_27)) | ~r2_hidden(B_32, k1_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.87/2.90  tff(c_1498, plain, (![B_32]: (B_32='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', B_32)!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | ~r2_hidden(B_32, k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1452, c_24])).
% 8.87/2.90  tff(c_1591, plain, (![B_197]: (B_197='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', B_197)!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(B_197, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_494, c_1456, c_1498])).
% 8.87/2.90  tff(c_1832, plain, (![C_204]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_204)='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_204))!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_204, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_1591])).
% 8.87/2.90  tff(c_1837, plain, (![C_205]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_205)='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | C_205!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_205, k1_relat_1('#skF_7')) | ~r2_hidden(C_205, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_555, c_1832])).
% 8.87/2.90  tff(c_1893, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_1837])).
% 8.87/2.90  tff(c_1925, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1893])).
% 8.87/2.90  tff(c_1926, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_493, c_1925])).
% 8.87/2.90  tff(c_1984, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1926])).
% 8.87/2.90  tff(c_1987, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_1984])).
% 8.87/2.90  tff(c_1990, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1987])).
% 8.87/2.90  tff(c_1992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_1990])).
% 8.87/2.90  tff(c_1994, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1926])).
% 8.87/2.90  tff(c_32, plain, (![A_27]: (r2_hidden('#skF_5'(A_27), k1_relat_1(A_27)) | v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.87/2.90  tff(c_1890, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1837])).
% 8.87/2.90  tff(c_1921, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1890])).
% 8.87/2.90  tff(c_1922, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_493, c_1921])).
% 8.87/2.90  tff(c_1956, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1922])).
% 8.87/2.90  tff(c_1970, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1956])).
% 8.87/2.90  tff(c_1973, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1970])).
% 8.87/2.90  tff(c_1975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_1973])).
% 8.87/2.90  tff(c_1977, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1922])).
% 8.87/2.90  tff(c_1251, plain, (![C_188]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_188))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_188))) | ~r2_hidden(C_188, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_1144])).
% 8.87/2.90  tff(c_42, plain, (![A_43, C_45]: (r2_hidden(k4_tarski(A_43, k1_funct_1(C_45, A_43)), C_45) | ~r2_hidden(A_43, k1_relat_1(C_45)) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.87/2.90  tff(c_1264, plain, (![C_188]: (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_188), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_188)))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_188), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_188, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1251, c_42])).
% 8.87/2.90  tff(c_5066, plain, (![C_323]: (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_323), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_323)))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_323), k1_relat_1('#skF_8')) | ~r2_hidden(C_323, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_589, c_1264])).
% 8.87/2.90  tff(c_5120, plain, (![C_324]: (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_324), k1_funct_1('#skF_7', C_324)), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_324), k1_relat_1('#skF_8')) | ~r2_hidden(C_324, k1_relat_1('#skF_7')) | ~r2_hidden(C_324, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_555, c_5066])).
% 8.87/2.90  tff(c_5123, plain, (![C_324]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_324))=k1_funct_1('#skF_7', C_324) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_324), k1_relat_1('#skF_8')) | ~r2_hidden(C_324, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_5120, c_44])).
% 8.87/2.90  tff(c_5182, plain, (![C_327]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_327))=k1_funct_1('#skF_7', C_327) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_327), k1_relat_1('#skF_8')) | ~r2_hidden(C_327, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_5123])).
% 8.87/2.90  tff(c_5204, plain, (![C_123]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_123))=k1_funct_1('#skF_7', C_123) | ~r2_hidden(C_123, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_5182])).
% 8.87/2.90  tff(c_28, plain, (![A_27]: (k1_funct_1(A_27, '#skF_5'(A_27))=k1_funct_1(A_27, '#skF_6'(A_27)) | v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.87/2.90  tff(c_5160, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_28, c_5120])).
% 8.87/2.90  tff(c_5174, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1977, c_1977, c_5160])).
% 8.87/2.90  tff(c_5175, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_493, c_5174])).
% 8.87/2.90  tff(c_5346, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_5175])).
% 8.87/2.90  tff(c_5349, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_543, c_5346])).
% 8.87/2.90  tff(c_5353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1977, c_5349])).
% 8.87/2.90  tff(c_5355, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_5175])).
% 8.87/2.90  tff(c_5354, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_5175])).
% 8.87/2.90  tff(c_5372, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', '#skF_6'('#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_5354, c_44])).
% 8.87/2.90  tff(c_5381, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_5372])).
% 8.87/2.90  tff(c_5408, plain, (![C_33]: (C_33='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), C_33)!=k1_funct_1('#skF_7', '#skF_6'('#skF_7')) | ~r2_hidden(C_33, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_5381, c_24])).
% 8.87/2.90  tff(c_5769, plain, (![C_333]: (C_333='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), C_333)!=k1_funct_1('#skF_7', '#skF_6'('#skF_7')) | ~r2_hidden(C_333, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_1058, c_52, c_5355, c_589, c_589, c_5408])).
% 8.87/2.90  tff(c_6738, plain, (![C_352]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_352)='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_352))!=k1_funct_1('#skF_7', '#skF_6'('#skF_7')) | ~r2_hidden(C_352, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_543, c_5769])).
% 8.87/2.90  tff(c_6768, plain, (![C_353]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_353)='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | k1_funct_1('#skF_7', C_353)!=k1_funct_1('#skF_7', '#skF_6'('#skF_7')) | ~r2_hidden(C_353, k1_relat_1('#skF_7')) | ~r2_hidden(C_353, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_6738])).
% 8.87/2.90  tff(c_6808, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1994, c_6768])).
% 8.87/2.90  tff(c_6887, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_6808])).
% 8.87/2.90  tff(c_6977, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6887, c_555])).
% 8.87/2.90  tff(c_7014, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1977, c_6977])).
% 8.87/2.90  tff(c_7124, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_7014, c_555])).
% 8.87/2.90  tff(c_7176, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_7124])).
% 8.87/2.90  tff(c_7178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_7176])).
% 8.87/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/2.90  
% 8.87/2.90  Inference rules
% 8.87/2.90  ----------------------
% 8.87/2.90  #Ref     : 3
% 8.87/2.90  #Sup     : 1437
% 8.87/2.90  #Fact    : 0
% 8.87/2.90  #Define  : 0
% 8.87/2.90  #Split   : 23
% 8.87/2.90  #Chain   : 0
% 8.87/2.90  #Close   : 0
% 8.87/2.90  
% 8.87/2.90  Ordering : KBO
% 8.87/2.90  
% 8.87/2.90  Simplification rules
% 8.87/2.90  ----------------------
% 8.87/2.90  #Subsume      : 266
% 8.87/2.90  #Demod        : 2704
% 8.87/2.90  #Tautology    : 543
% 8.87/2.90  #SimpNegUnit  : 79
% 8.87/2.90  #BackRed      : 35
% 8.87/2.90  
% 8.87/2.90  #Partial instantiations: 0
% 8.87/2.90  #Strategies tried      : 1
% 9.20/2.90  
% 9.20/2.90  Timing (in seconds)
% 9.20/2.90  ----------------------
% 9.20/2.90  Preprocessing        : 0.33
% 9.20/2.90  Parsing              : 0.17
% 9.20/2.90  CNF conversion       : 0.02
% 9.20/2.90  Main loop            : 1.78
% 9.20/2.90  Inferencing          : 0.62
% 9.20/2.90  Reduction            : 0.60
% 9.20/2.90  Demodulation         : 0.43
% 9.20/2.90  BG Simplification    : 0.09
% 9.20/2.90  Subsumption          : 0.37
% 9.20/2.90  Abstraction          : 0.10
% 9.20/2.90  MUC search           : 0.00
% 9.20/2.90  Cooper               : 0.00
% 9.20/2.90  Total                : 2.16
% 9.20/2.90  Index Insertion      : 0.00
% 9.20/2.90  Index Deletion       : 0.00
% 9.20/2.90  Index Matching       : 0.00
% 9.20/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
