%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:49 EST 2020

% Result     : Theorem 14.48s
% Output     : CNFRefutation 14.48s
% Verified   : 
% Statistics : Number of formulae       :  140 (1687 expanded)
%              Number of leaves         :   36 ( 562 expanded)
%              Depth                    :   21
%              Number of atoms          :  372 (5568 expanded)
%              Number of equality atoms :   27 ( 699 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ~ ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C))
            & A != B
            & r4_wellord1(k2_wellord1(C,k1_wellord1(C,A)),k2_wellord1(C,k1_wellord1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_wellord1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k1_wellord1(C,B)) )
       => k1_wellord1(k2_wellord1(C,k1_wellord1(C,B)),A) = k1_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => v2_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(c_70,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    v2_wellord1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [A_13] :
      ( v6_relat_2(A_13)
      | ~ v2_wellord1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    r2_hidden('#skF_6',k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_508,plain,(
    ! [C_135,B_136,A_137] :
      ( r2_hidden(k4_tarski(C_135,B_136),A_137)
      | r2_hidden(k4_tarski(B_136,C_135),A_137)
      | C_135 = B_136
      | ~ r2_hidden(C_135,k3_relat_1(A_137))
      | ~ r2_hidden(B_136,k3_relat_1(A_137))
      | ~ v6_relat_2(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [D_12,A_1,B_8] :
      ( r2_hidden(D_12,k1_wellord1(A_1,B_8))
      | ~ r2_hidden(k4_tarski(D_12,B_8),A_1)
      | D_12 = B_8
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_770,plain,(
    ! [B_174,A_175,C_176] :
      ( r2_hidden(B_174,k1_wellord1(A_175,C_176))
      | r2_hidden(k4_tarski(C_176,B_174),A_175)
      | C_176 = B_174
      | ~ r2_hidden(C_176,k3_relat_1(A_175))
      | ~ r2_hidden(B_174,k3_relat_1(A_175))
      | ~ v6_relat_2(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(resolution,[status(thm)],[c_508,c_2])).

tff(c_796,plain,(
    ! [C_176,A_175,B_174] :
      ( r2_hidden(C_176,k1_wellord1(A_175,B_174))
      | r2_hidden(B_174,k1_wellord1(A_175,C_176))
      | C_176 = B_174
      | ~ r2_hidden(C_176,k3_relat_1(A_175))
      | ~ r2_hidden(B_174,k3_relat_1(A_175))
      | ~ v6_relat_2(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(resolution,[status(thm)],[c_770,c_2])).

tff(c_48,plain,(
    ! [C_27,B_26,A_25] :
      ( k2_wellord1(k2_wellord1(C_27,B_26),A_25) = k2_wellord1(C_27,A_25)
      | ~ r1_tarski(A_25,B_26)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k2_wellord1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_103,plain,(
    ! [B_57,A_58] :
      ( r4_wellord1(B_57,A_58)
      | ~ r4_wellord1(A_58,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_106,plain,
    ( r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
    | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_147,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_150,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_150])).

tff(c_155,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_216,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_219,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_216])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_219])).

tff(c_225,plain,(
    v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_54,plain,(
    ! [B_34,A_33] :
      ( k3_relat_1(k2_wellord1(B_34,k1_wellord1(B_34,A_33))) = k1_wellord1(B_34,A_33)
      | ~ v2_wellord1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_232,plain,(
    ! [C_93,B_94,A_95] :
      ( k1_wellord1(k2_wellord1(C_93,k1_wellord1(C_93,B_94)),A_95) = k1_wellord1(C_93,A_95)
      | ~ r2_hidden(A_95,k1_wellord1(C_93,B_94))
      | ~ v2_wellord1(C_93)
      | ~ v1_relat_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_wellord1(B_24,A_23),k3_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1266,plain,(
    ! [C_232,A_233,B_234] :
      ( r1_tarski(k1_wellord1(C_232,A_233),k3_relat_1(k2_wellord1(C_232,k1_wellord1(C_232,B_234))))
      | ~ v1_relat_1(k2_wellord1(C_232,k1_wellord1(C_232,B_234)))
      | ~ r2_hidden(A_233,k1_wellord1(C_232,B_234))
      | ~ v2_wellord1(C_232)
      | ~ v1_relat_1(C_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_46])).

tff(c_1888,plain,(
    ! [B_292,A_293,A_294] :
      ( r1_tarski(k1_wellord1(B_292,A_293),k1_wellord1(B_292,A_294))
      | ~ v1_relat_1(k2_wellord1(B_292,k1_wellord1(B_292,A_294)))
      | ~ r2_hidden(A_293,k1_wellord1(B_292,A_294))
      | ~ v2_wellord1(B_292)
      | ~ v1_relat_1(B_292)
      | ~ v2_wellord1(B_292)
      | ~ v1_relat_1(B_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1266])).

tff(c_157,plain,(
    ! [C_72,B_73,A_74] :
      ( k2_wellord1(k2_wellord1(C_72,B_73),A_74) = k2_wellord1(C_72,A_74)
      | ~ r1_tarski(A_74,B_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_294,plain,(
    ! [C_102,B_103,A_104,A_105] :
      ( k2_wellord1(k2_wellord1(C_102,B_103),A_104) = k2_wellord1(k2_wellord1(C_102,A_105),A_104)
      | ~ r1_tarski(A_104,A_105)
      | ~ v1_relat_1(k2_wellord1(C_102,B_103))
      | ~ r1_tarski(A_105,B_103)
      | ~ v1_relat_1(C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_157])).

tff(c_296,plain,(
    ! [A_104,A_105] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_104) = k2_wellord1(k2_wellord1('#skF_7',A_105),A_104)
      | ~ r1_tarski(A_104,A_105)
      | ~ r1_tarski(A_105,k1_wellord1('#skF_7','#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_225,c_294])).

tff(c_305,plain,(
    ! [A_104,A_105] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_104) = k2_wellord1(k2_wellord1('#skF_7',A_105),A_104)
      | ~ r1_tarski(A_104,A_105)
      | ~ r1_tarski(A_105,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_296])).

tff(c_1974,plain,(
    ! [A_293,A_104] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_293)),A_104) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_104)
      | ~ r1_tarski(A_104,k1_wellord1('#skF_7',A_293))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r2_hidden(A_293,k1_wellord1('#skF_7','#skF_6'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1888,c_305])).

tff(c_2062,plain,(
    ! [A_295,A_296] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_295)),A_296) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_296)
      | ~ r1_tarski(A_296,k1_wellord1('#skF_7',A_295))
      | ~ r2_hidden(A_295,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_225,c_1974])).

tff(c_2230,plain,(
    ! [A_295,A_296] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_295)),A_296))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r1_tarski(A_296,k1_wellord1('#skF_7',A_295))
      | ~ r2_hidden(A_295,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2062,c_32])).

tff(c_2643,plain,(
    ! [A_299,A_300] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_299)),A_300))
      | ~ r1_tarski(A_300,k1_wellord1('#skF_7',A_299))
      | ~ r2_hidden(A_299,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_2230])).

tff(c_2663,plain,(
    ! [A_25,A_299] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_25))
      | ~ r1_tarski(A_25,k1_wellord1('#skF_7',A_299))
      | ~ r2_hidden(A_299,k1_wellord1('#skF_7','#skF_6'))
      | ~ r1_tarski(A_25,k1_wellord1('#skF_7',A_299))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2643])).

tff(c_2668,plain,(
    ! [A_301,A_302] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_301))
      | ~ r2_hidden(A_302,k1_wellord1('#skF_7','#skF_6'))
      | ~ r1_tarski(A_301,k1_wellord1('#skF_7',A_302)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2663])).

tff(c_2674,plain,(
    ! [A_301,C_176] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_301))
      | ~ r1_tarski(A_301,k1_wellord1('#skF_7',C_176))
      | r2_hidden('#skF_6',k1_wellord1('#skF_7',C_176))
      | C_176 = '#skF_6'
      | ~ r2_hidden(C_176,k3_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
      | ~ v6_relat_2('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_796,c_2668])).

tff(c_2712,plain,(
    ! [A_301,C_176] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_301))
      | ~ r1_tarski(A_301,k1_wellord1('#skF_7',C_176))
      | r2_hidden('#skF_6',k1_wellord1('#skF_7',C_176))
      | C_176 = '#skF_6'
      | ~ r2_hidden(C_176,k3_relat_1('#skF_7'))
      | ~ v6_relat_2('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_2674])).

tff(c_3289,plain,(
    ~ v6_relat_2('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2712])).

tff(c_3324,plain,
    ( ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_3289])).

tff(c_3331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3324])).

tff(c_3333,plain,(
    v6_relat_2('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2712])).

tff(c_66,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_156,plain,(
    v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_3559,plain,(
    ! [A_345,A_346] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_345))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_346)))
      | ~ r1_tarski(A_345,k1_wellord1('#skF_7',A_346))
      | ~ r2_hidden(A_346,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2062,c_32])).

tff(c_3574,plain,(
    ! [A_345] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_345))
      | ~ r1_tarski(A_345,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_156,c_3559])).

tff(c_3578,plain,(
    ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3574])).

tff(c_3581,plain,
    ( r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
    | ~ v6_relat_2('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_796,c_3578])).

tff(c_3587,plain,
    ( r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3333,c_64,c_66,c_3581])).

tff(c_3588,plain,(
    r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3587])).

tff(c_1293,plain,(
    ! [B_34,A_233,A_33] :
      ( r1_tarski(k1_wellord1(B_34,A_233),k1_wellord1(B_34,A_33))
      | ~ v1_relat_1(k2_wellord1(B_34,k1_wellord1(B_34,A_33)))
      | ~ r2_hidden(A_233,k1_wellord1(B_34,A_33))
      | ~ v2_wellord1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v2_wellord1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1266])).

tff(c_310,plain,(
    ! [A_106,B_107,A_108,A_109] :
      ( k2_wellord1(k2_wellord1(A_106,B_107),A_108) = k2_wellord1(k2_wellord1(A_106,A_109),A_108)
      | ~ r1_tarski(A_108,A_109)
      | ~ r1_tarski(A_109,B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_32,c_294])).

tff(c_331,plain,(
    ! [A_114,B_115,A_116,A_117] :
      ( k2_wellord1(k2_wellord1(A_114,k1_wellord1(B_115,A_116)),A_117) = k2_wellord1(k2_wellord1(A_114,k3_relat_1(B_115)),A_117)
      | ~ r1_tarski(A_117,k1_wellord1(B_115,A_116))
      | ~ v1_relat_1(A_114)
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_46,c_310])).

tff(c_395,plain,(
    ! [A_118,B_119,A_120,A_121] :
      ( v1_relat_1(k2_wellord1(k2_wellord1(A_118,k3_relat_1(B_119)),A_120))
      | ~ v1_relat_1(k2_wellord1(A_118,k1_wellord1(B_119,A_121)))
      | ~ r1_tarski(A_120,k1_wellord1(B_119,A_121))
      | ~ v1_relat_1(A_118)
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_32])).

tff(c_407,plain,(
    ! [A_120] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')),A_120))
      | ~ r1_tarski(A_120,k1_wellord1('#skF_7','#skF_5'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_156,c_395])).

tff(c_435,plain,(
    ! [A_126] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')),A_126))
      | ~ r1_tarski(A_126,k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_407])).

tff(c_374,plain,(
    ! [A_114,B_115,A_117,A_116] :
      ( v1_relat_1(k2_wellord1(k2_wellord1(A_114,k3_relat_1(B_115)),A_117))
      | ~ v1_relat_1(k2_wellord1(A_114,k1_wellord1(B_115,A_116)))
      | ~ r1_tarski(A_117,k1_wellord1(B_115,A_116))
      | ~ v1_relat_1(A_114)
      | ~ v1_relat_1(B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_32])).

tff(c_443,plain,(
    ! [B_115,A_117,A_116] :
      ( v1_relat_1(k2_wellord1(k2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')),k3_relat_1(B_115)),A_117))
      | ~ r1_tarski(A_117,k1_wellord1(B_115,A_116))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')))
      | ~ v1_relat_1(B_115)
      | ~ r1_tarski(k1_wellord1(B_115,A_116),k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_435,c_374])).

tff(c_462,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_7',k3_relat_1('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_465,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_462])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_465])).

tff(c_471,plain,(
    v1_relat_1(k2_wellord1('#skF_7',k3_relat_1('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_50,plain,(
    ! [B_29,A_28] :
      ( v2_wellord1(k2_wellord1(B_29,A_28))
      | ~ v2_wellord1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_402,plain,(
    ! [A_120] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')),A_120))
      | ~ r1_tarski(A_120,k1_wellord1('#skF_7','#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_225,c_395])).

tff(c_413,plain,(
    ! [A_120] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')),A_120))
      | ~ r1_tarski(A_120,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_402])).

tff(c_91,plain,(
    ! [B_52,A_53] :
      ( v2_wellord1(k2_wellord1(B_52,A_53))
      | ~ v2_wellord1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [A_13] :
      ( v1_relat_2(A_13)
      | ~ v2_wellord1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_98,plain,(
    ! [B_52,A_53] :
      ( v1_relat_2(k2_wellord1(B_52,A_53))
      | ~ v1_relat_1(k2_wellord1(B_52,A_53))
      | ~ v2_wellord1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_91,c_30])).

tff(c_599,plain,(
    ! [C_147,A_148,B_149] :
      ( v1_relat_2(k2_wellord1(C_147,A_148))
      | ~ v1_relat_1(k2_wellord1(k2_wellord1(C_147,B_149),A_148))
      | ~ v2_wellord1(k2_wellord1(C_147,B_149))
      | ~ v1_relat_1(k2_wellord1(C_147,B_149))
      | ~ r1_tarski(A_148,B_149)
      | ~ v1_relat_1(C_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_98])).

tff(c_605,plain,(
    ! [A_120] :
      ( v1_relat_2(k2_wellord1('#skF_7',A_120))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')))
      | ~ r1_tarski(A_120,k3_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(A_120,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_413,c_599])).

tff(c_627,plain,(
    ! [A_120] :
      ( v1_relat_2(k2_wellord1('#skF_7',A_120))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')))
      | ~ r1_tarski(A_120,k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_120,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_471,c_605])).

tff(c_657,plain,(
    ~ v2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_661,plain,
    ( ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_657])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_661])).

tff(c_667,plain,(
    v2_wellord1(k2_wellord1('#skF_7',k3_relat_1('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_176,plain,(
    ! [C_72,A_74,B_73] :
      ( v2_wellord1(k2_wellord1(C_72,A_74))
      | ~ v2_wellord1(k2_wellord1(C_72,B_73))
      | ~ v1_relat_1(k2_wellord1(C_72,B_73))
      | ~ r1_tarski(A_74,B_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_50])).

tff(c_671,plain,(
    ! [A_74] :
      ( v2_wellord1(k2_wellord1('#skF_7',A_74))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k3_relat_1('#skF_7')))
      | ~ r1_tarski(A_74,k3_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_667,c_176])).

tff(c_704,plain,(
    ! [A_167] :
      ( v2_wellord1(k2_wellord1('#skF_7',A_167))
      | ~ r1_tarski(A_167,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_471,c_671])).

tff(c_708,plain,(
    ! [A_23] :
      ( v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_23)))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_704])).

tff(c_711,plain,(
    ! [A_23] : v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_708])).

tff(c_58,plain,(
    ! [A_38,B_40] :
      ( ~ r4_wellord1(A_38,k2_wellord1(A_38,k1_wellord1(A_38,B_40)))
      | ~ r2_hidden(B_40,k3_relat_1(A_38))
      | ~ v2_wellord1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4780,plain,(
    ! [C_396,B_397,A_398] :
      ( ~ r4_wellord1(k2_wellord1(C_396,k1_wellord1(C_396,B_397)),k2_wellord1(k2_wellord1(C_396,k1_wellord1(C_396,B_397)),k1_wellord1(C_396,A_398)))
      | ~ r2_hidden(A_398,k3_relat_1(k2_wellord1(C_396,k1_wellord1(C_396,B_397))))
      | ~ v2_wellord1(k2_wellord1(C_396,k1_wellord1(C_396,B_397)))
      | ~ v1_relat_1(k2_wellord1(C_396,k1_wellord1(C_396,B_397)))
      | ~ r2_hidden(A_398,k1_wellord1(C_396,B_397))
      | ~ v2_wellord1(C_396)
      | ~ v1_relat_1(C_396) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_58])).

tff(c_14055,plain,(
    ! [C_706,B_707,A_708] :
      ( ~ r4_wellord1(k2_wellord1(C_706,k1_wellord1(C_706,B_707)),k2_wellord1(C_706,k1_wellord1(C_706,A_708)))
      | ~ r2_hidden(A_708,k3_relat_1(k2_wellord1(C_706,k1_wellord1(C_706,B_707))))
      | ~ v2_wellord1(k2_wellord1(C_706,k1_wellord1(C_706,B_707)))
      | ~ v1_relat_1(k2_wellord1(C_706,k1_wellord1(C_706,B_707)))
      | ~ r2_hidden(A_708,k1_wellord1(C_706,B_707))
      | ~ v2_wellord1(C_706)
      | ~ v1_relat_1(C_706)
      | ~ r1_tarski(k1_wellord1(C_706,A_708),k1_wellord1(C_706,B_707))
      | ~ v1_relat_1(C_706) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4780])).

tff(c_14207,plain,
    ( ~ r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
    | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
    | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
    | ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | ~ v2_wellord1('#skF_7')
    | ~ r1_tarski(k1_wellord1('#skF_7','#skF_6'),k1_wellord1('#skF_7','#skF_5'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_14055])).

tff(c_14265,plain,
    ( ~ r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
    | ~ r1_tarski(k1_wellord1('#skF_7','#skF_6'),k1_wellord1('#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3588,c_156,c_711,c_14207])).

tff(c_14266,plain,(
    ~ r1_tarski(k1_wellord1('#skF_7','#skF_6'),k1_wellord1('#skF_7','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_14265])).

tff(c_14269,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
    | ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1293,c_14266])).

tff(c_14273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3588,c_156,c_14269])).

tff(c_14274,plain,(
    ~ r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_14265])).

tff(c_14484,plain,
    ( ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_14274])).

tff(c_14487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3588,c_14484])).

tff(c_14489,plain,(
    r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3574])).

tff(c_224,plain,(
    r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_15837,plain,(
    ! [C_761,B_762,A_763] :
      ( ~ r4_wellord1(k2_wellord1(C_761,k1_wellord1(C_761,B_762)),k2_wellord1(k2_wellord1(C_761,k1_wellord1(C_761,B_762)),k1_wellord1(C_761,A_763)))
      | ~ r2_hidden(A_763,k3_relat_1(k2_wellord1(C_761,k1_wellord1(C_761,B_762))))
      | ~ v2_wellord1(k2_wellord1(C_761,k1_wellord1(C_761,B_762)))
      | ~ v1_relat_1(k2_wellord1(C_761,k1_wellord1(C_761,B_762)))
      | ~ r2_hidden(A_763,k1_wellord1(C_761,B_762))
      | ~ v2_wellord1(C_761)
      | ~ v1_relat_1(C_761) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_58])).

tff(c_24412,plain,(
    ! [C_1066,B_1067,A_1068] :
      ( ~ r4_wellord1(k2_wellord1(C_1066,k1_wellord1(C_1066,B_1067)),k2_wellord1(C_1066,k1_wellord1(C_1066,A_1068)))
      | ~ r2_hidden(A_1068,k3_relat_1(k2_wellord1(C_1066,k1_wellord1(C_1066,B_1067))))
      | ~ v2_wellord1(k2_wellord1(C_1066,k1_wellord1(C_1066,B_1067)))
      | ~ v1_relat_1(k2_wellord1(C_1066,k1_wellord1(C_1066,B_1067)))
      | ~ r2_hidden(A_1068,k1_wellord1(C_1066,B_1067))
      | ~ v2_wellord1(C_1066)
      | ~ v1_relat_1(C_1066)
      | ~ r1_tarski(k1_wellord1(C_1066,A_1068),k1_wellord1(C_1066,B_1067))
      | ~ v1_relat_1(C_1066) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_15837])).

tff(c_24545,plain,
    ( ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
    | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ v2_wellord1('#skF_7')
    | ~ r1_tarski(k1_wellord1('#skF_7','#skF_5'),k1_wellord1('#skF_7','#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_224,c_24412])).

tff(c_24607,plain,
    ( ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
    | ~ r1_tarski(k1_wellord1('#skF_7','#skF_5'),k1_wellord1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_14489,c_225,c_711,c_24545])).

tff(c_24611,plain,(
    ~ r1_tarski(k1_wellord1('#skF_7','#skF_5'),k1_wellord1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_24607])).

tff(c_24614,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1293,c_24611])).

tff(c_24618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_14489,c_225,c_24614])).

tff(c_24619,plain,(
    ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_24607])).

tff(c_24863,plain,
    ( ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_24619])).

tff(c_24866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_14489,c_24863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.48/6.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.48/6.04  
% 14.48/6.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.48/6.04  %$ r4_wellord1 > r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 14.48/6.04  
% 14.48/6.04  %Foreground sorts:
% 14.48/6.04  
% 14.48/6.04  
% 14.48/6.04  %Background operators:
% 14.48/6.04  
% 14.48/6.04  
% 14.48/6.04  %Foreground operators:
% 14.48/6.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.48/6.04  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 14.48/6.04  tff('#skF_4', type, '#skF_4': $i > $i).
% 14.48/6.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.48/6.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.48/6.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.48/6.04  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 14.48/6.04  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 14.48/6.04  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 14.48/6.04  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 14.48/6.04  tff('#skF_7', type, '#skF_7': $i).
% 14.48/6.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.48/6.04  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 14.48/6.04  tff('#skF_5', type, '#skF_5': $i).
% 14.48/6.04  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 14.48/6.04  tff('#skF_6', type, '#skF_6': $i).
% 14.48/6.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.48/6.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.48/6.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.48/6.04  tff('#skF_3', type, '#skF_3': $i > $i).
% 14.48/6.04  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 14.48/6.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.48/6.04  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 14.48/6.04  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 14.48/6.04  
% 14.48/6.07  tff(f_139, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ~((((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) & ~(A = B)) & r4_wellord1(k2_wellord1(C, k1_wellord1(C, A)), k2_wellord1(C, k1_wellord1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_wellord1)).
% 14.48/6.07  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 14.48/6.07  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 14.48/6.07  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 14.48/6.07  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 14.48/6.07  tff(f_56, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 14.48/6.07  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 14.48/6.07  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => (k3_relat_1(k2_wellord1(B, k1_wellord1(B, A))) = k1_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_wellord1)).
% 14.48/6.07  tff(f_99, axiom, (![A, B, C]: (v1_relat_1(C) => ((v2_wellord1(C) & r2_hidden(A, k1_wellord1(C, B))) => (k1_wellord1(k2_wellord1(C, k1_wellord1(C, B)), A) = k1_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_wellord1)).
% 14.48/6.07  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_wellord1)).
% 14.48/6.07  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => v2_wellord1(k2_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_wellord1)).
% 14.48/6.07  tff(f_124, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 14.48/6.07  tff(c_70, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.48/6.07  tff(c_68, plain, (v2_wellord1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.48/6.07  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.48/6.07  tff(c_24, plain, (![A_13]: (v6_relat_2(A_13) | ~v2_wellord1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.48/6.07  tff(c_64, plain, (r2_hidden('#skF_6', k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.48/6.07  tff(c_508, plain, (![C_135, B_136, A_137]: (r2_hidden(k4_tarski(C_135, B_136), A_137) | r2_hidden(k4_tarski(B_136, C_135), A_137) | C_135=B_136 | ~r2_hidden(C_135, k3_relat_1(A_137)) | ~r2_hidden(B_136, k3_relat_1(A_137)) | ~v6_relat_2(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.48/6.07  tff(c_2, plain, (![D_12, A_1, B_8]: (r2_hidden(D_12, k1_wellord1(A_1, B_8)) | ~r2_hidden(k4_tarski(D_12, B_8), A_1) | D_12=B_8 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.48/6.07  tff(c_770, plain, (![B_174, A_175, C_176]: (r2_hidden(B_174, k1_wellord1(A_175, C_176)) | r2_hidden(k4_tarski(C_176, B_174), A_175) | C_176=B_174 | ~r2_hidden(C_176, k3_relat_1(A_175)) | ~r2_hidden(B_174, k3_relat_1(A_175)) | ~v6_relat_2(A_175) | ~v1_relat_1(A_175))), inference(resolution, [status(thm)], [c_508, c_2])).
% 14.48/6.07  tff(c_796, plain, (![C_176, A_175, B_174]: (r2_hidden(C_176, k1_wellord1(A_175, B_174)) | r2_hidden(B_174, k1_wellord1(A_175, C_176)) | C_176=B_174 | ~r2_hidden(C_176, k3_relat_1(A_175)) | ~r2_hidden(B_174, k3_relat_1(A_175)) | ~v6_relat_2(A_175) | ~v1_relat_1(A_175))), inference(resolution, [status(thm)], [c_770, c_2])).
% 14.48/6.07  tff(c_48, plain, (![C_27, B_26, A_25]: (k2_wellord1(k2_wellord1(C_27, B_26), A_25)=k2_wellord1(C_27, A_25) | ~r1_tarski(A_25, B_26) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.48/6.07  tff(c_32, plain, (![A_14, B_15]: (v1_relat_1(k2_wellord1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.48/6.07  tff(c_60, plain, (r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.48/6.07  tff(c_103, plain, (![B_57, A_58]: (r4_wellord1(B_57, A_58) | ~r4_wellord1(A_58, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.48/6.07  tff(c_106, plain, (r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_103])).
% 14.48/6.07  tff(c_147, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitLeft, [status(thm)], [c_106])).
% 14.48/6.07  tff(c_150, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_147])).
% 14.48/6.07  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_150])).
% 14.48/6.07  tff(c_155, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitRight, [status(thm)], [c_106])).
% 14.48/6.07  tff(c_216, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_155])).
% 14.48/6.07  tff(c_219, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_216])).
% 14.48/6.07  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_219])).
% 14.48/6.07  tff(c_225, plain, (v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_155])).
% 14.48/6.07  tff(c_54, plain, (![B_34, A_33]: (k3_relat_1(k2_wellord1(B_34, k1_wellord1(B_34, A_33)))=k1_wellord1(B_34, A_33) | ~v2_wellord1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.48/6.07  tff(c_232, plain, (![C_93, B_94, A_95]: (k1_wellord1(k2_wellord1(C_93, k1_wellord1(C_93, B_94)), A_95)=k1_wellord1(C_93, A_95) | ~r2_hidden(A_95, k1_wellord1(C_93, B_94)) | ~v2_wellord1(C_93) | ~v1_relat_1(C_93))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.48/6.07  tff(c_46, plain, (![B_24, A_23]: (r1_tarski(k1_wellord1(B_24, A_23), k3_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.48/6.07  tff(c_1266, plain, (![C_232, A_233, B_234]: (r1_tarski(k1_wellord1(C_232, A_233), k3_relat_1(k2_wellord1(C_232, k1_wellord1(C_232, B_234)))) | ~v1_relat_1(k2_wellord1(C_232, k1_wellord1(C_232, B_234))) | ~r2_hidden(A_233, k1_wellord1(C_232, B_234)) | ~v2_wellord1(C_232) | ~v1_relat_1(C_232))), inference(superposition, [status(thm), theory('equality')], [c_232, c_46])).
% 14.48/6.07  tff(c_1888, plain, (![B_292, A_293, A_294]: (r1_tarski(k1_wellord1(B_292, A_293), k1_wellord1(B_292, A_294)) | ~v1_relat_1(k2_wellord1(B_292, k1_wellord1(B_292, A_294))) | ~r2_hidden(A_293, k1_wellord1(B_292, A_294)) | ~v2_wellord1(B_292) | ~v1_relat_1(B_292) | ~v2_wellord1(B_292) | ~v1_relat_1(B_292))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1266])).
% 14.48/6.07  tff(c_157, plain, (![C_72, B_73, A_74]: (k2_wellord1(k2_wellord1(C_72, B_73), A_74)=k2_wellord1(C_72, A_74) | ~r1_tarski(A_74, B_73) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.48/6.07  tff(c_294, plain, (![C_102, B_103, A_104, A_105]: (k2_wellord1(k2_wellord1(C_102, B_103), A_104)=k2_wellord1(k2_wellord1(C_102, A_105), A_104) | ~r1_tarski(A_104, A_105) | ~v1_relat_1(k2_wellord1(C_102, B_103)) | ~r1_tarski(A_105, B_103) | ~v1_relat_1(C_102))), inference(superposition, [status(thm), theory('equality')], [c_48, c_157])).
% 14.48/6.07  tff(c_296, plain, (![A_104, A_105]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_104)=k2_wellord1(k2_wellord1('#skF_7', A_105), A_104) | ~r1_tarski(A_104, A_105) | ~r1_tarski(A_105, k1_wellord1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_225, c_294])).
% 14.48/6.07  tff(c_305, plain, (![A_104, A_105]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_104)=k2_wellord1(k2_wellord1('#skF_7', A_105), A_104) | ~r1_tarski(A_104, A_105) | ~r1_tarski(A_105, k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_296])).
% 14.48/6.07  tff(c_1974, plain, (![A_293, A_104]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_293)), A_104)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_104) | ~r1_tarski(A_104, k1_wellord1('#skF_7', A_293)) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden(A_293, k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1888, c_305])).
% 14.48/6.07  tff(c_2062, plain, (![A_295, A_296]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_295)), A_296)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_296) | ~r1_tarski(A_296, k1_wellord1('#skF_7', A_295)) | ~r2_hidden(A_295, k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_225, c_1974])).
% 14.48/6.07  tff(c_2230, plain, (![A_295, A_296]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_295)), A_296)) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r1_tarski(A_296, k1_wellord1('#skF_7', A_295)) | ~r2_hidden(A_295, k1_wellord1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2062, c_32])).
% 14.48/6.07  tff(c_2643, plain, (![A_299, A_300]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_299)), A_300)) | ~r1_tarski(A_300, k1_wellord1('#skF_7', A_299)) | ~r2_hidden(A_299, k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_2230])).
% 14.48/6.07  tff(c_2663, plain, (![A_25, A_299]: (v1_relat_1(k2_wellord1('#skF_7', A_25)) | ~r1_tarski(A_25, k1_wellord1('#skF_7', A_299)) | ~r2_hidden(A_299, k1_wellord1('#skF_7', '#skF_6')) | ~r1_tarski(A_25, k1_wellord1('#skF_7', A_299)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2643])).
% 14.48/6.07  tff(c_2668, plain, (![A_301, A_302]: (v1_relat_1(k2_wellord1('#skF_7', A_301)) | ~r2_hidden(A_302, k1_wellord1('#skF_7', '#skF_6')) | ~r1_tarski(A_301, k1_wellord1('#skF_7', A_302)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2663])).
% 14.48/6.07  tff(c_2674, plain, (![A_301, C_176]: (v1_relat_1(k2_wellord1('#skF_7', A_301)) | ~r1_tarski(A_301, k1_wellord1('#skF_7', C_176)) | r2_hidden('#skF_6', k1_wellord1('#skF_7', C_176)) | C_176='#skF_6' | ~r2_hidden(C_176, k3_relat_1('#skF_7')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~v6_relat_2('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_796, c_2668])).
% 14.48/6.07  tff(c_2712, plain, (![A_301, C_176]: (v1_relat_1(k2_wellord1('#skF_7', A_301)) | ~r1_tarski(A_301, k1_wellord1('#skF_7', C_176)) | r2_hidden('#skF_6', k1_wellord1('#skF_7', C_176)) | C_176='#skF_6' | ~r2_hidden(C_176, k3_relat_1('#skF_7')) | ~v6_relat_2('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_2674])).
% 14.48/6.07  tff(c_3289, plain, (~v6_relat_2('#skF_7')), inference(splitLeft, [status(thm)], [c_2712])).
% 14.48/6.07  tff(c_3324, plain, (~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_3289])).
% 14.48/6.07  tff(c_3331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3324])).
% 14.48/6.07  tff(c_3333, plain, (v6_relat_2('#skF_7')), inference(splitRight, [status(thm)], [c_2712])).
% 14.48/6.07  tff(c_66, plain, (r2_hidden('#skF_5', k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.48/6.07  tff(c_156, plain, (v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitRight, [status(thm)], [c_106])).
% 14.48/6.07  tff(c_3559, plain, (![A_345, A_346]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_345)) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_346))) | ~r1_tarski(A_345, k1_wellord1('#skF_7', A_346)) | ~r2_hidden(A_346, k1_wellord1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2062, c_32])).
% 14.48/6.07  tff(c_3574, plain, (![A_345]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_345)) | ~r1_tarski(A_345, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_156, c_3559])).
% 14.48/6.07  tff(c_3578, plain, (~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_3574])).
% 14.48/6.07  tff(c_3581, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | '#skF_5'='#skF_6' | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~v6_relat_2('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_796, c_3578])).
% 14.48/6.07  tff(c_3587, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3333, c_64, c_66, c_3581])).
% 14.48/6.07  tff(c_3588, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_3587])).
% 14.48/6.07  tff(c_1293, plain, (![B_34, A_233, A_33]: (r1_tarski(k1_wellord1(B_34, A_233), k1_wellord1(B_34, A_33)) | ~v1_relat_1(k2_wellord1(B_34, k1_wellord1(B_34, A_33))) | ~r2_hidden(A_233, k1_wellord1(B_34, A_33)) | ~v2_wellord1(B_34) | ~v1_relat_1(B_34) | ~v2_wellord1(B_34) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1266])).
% 14.48/6.07  tff(c_310, plain, (![A_106, B_107, A_108, A_109]: (k2_wellord1(k2_wellord1(A_106, B_107), A_108)=k2_wellord1(k2_wellord1(A_106, A_109), A_108) | ~r1_tarski(A_108, A_109) | ~r1_tarski(A_109, B_107) | ~v1_relat_1(A_106))), inference(resolution, [status(thm)], [c_32, c_294])).
% 14.48/6.07  tff(c_331, plain, (![A_114, B_115, A_116, A_117]: (k2_wellord1(k2_wellord1(A_114, k1_wellord1(B_115, A_116)), A_117)=k2_wellord1(k2_wellord1(A_114, k3_relat_1(B_115)), A_117) | ~r1_tarski(A_117, k1_wellord1(B_115, A_116)) | ~v1_relat_1(A_114) | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_46, c_310])).
% 14.48/6.07  tff(c_395, plain, (![A_118, B_119, A_120, A_121]: (v1_relat_1(k2_wellord1(k2_wellord1(A_118, k3_relat_1(B_119)), A_120)) | ~v1_relat_1(k2_wellord1(A_118, k1_wellord1(B_119, A_121))) | ~r1_tarski(A_120, k1_wellord1(B_119, A_121)) | ~v1_relat_1(A_118) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_331, c_32])).
% 14.48/6.07  tff(c_407, plain, (![A_120]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')), A_120)) | ~r1_tarski(A_120, k1_wellord1('#skF_7', '#skF_5')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_156, c_395])).
% 14.48/6.07  tff(c_435, plain, (![A_126]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')), A_126)) | ~r1_tarski(A_126, k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_407])).
% 14.48/6.07  tff(c_374, plain, (![A_114, B_115, A_117, A_116]: (v1_relat_1(k2_wellord1(k2_wellord1(A_114, k3_relat_1(B_115)), A_117)) | ~v1_relat_1(k2_wellord1(A_114, k1_wellord1(B_115, A_116))) | ~r1_tarski(A_117, k1_wellord1(B_115, A_116)) | ~v1_relat_1(A_114) | ~v1_relat_1(B_115))), inference(superposition, [status(thm), theory('equality')], [c_331, c_32])).
% 14.48/6.07  tff(c_443, plain, (![B_115, A_117, A_116]: (v1_relat_1(k2_wellord1(k2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')), k3_relat_1(B_115)), A_117)) | ~r1_tarski(A_117, k1_wellord1(B_115, A_116)) | ~v1_relat_1(k2_wellord1('#skF_7', k3_relat_1('#skF_7'))) | ~v1_relat_1(B_115) | ~r1_tarski(k1_wellord1(B_115, A_116), k1_wellord1('#skF_7', '#skF_5')))), inference(resolution, [status(thm)], [c_435, c_374])).
% 14.48/6.07  tff(c_462, plain, (~v1_relat_1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')))), inference(splitLeft, [status(thm)], [c_443])).
% 14.48/6.07  tff(c_465, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_462])).
% 14.48/6.07  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_465])).
% 14.48/6.07  tff(c_471, plain, (v1_relat_1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')))), inference(splitRight, [status(thm)], [c_443])).
% 14.48/6.07  tff(c_50, plain, (![B_29, A_28]: (v2_wellord1(k2_wellord1(B_29, A_28)) | ~v2_wellord1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.48/6.07  tff(c_402, plain, (![A_120]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')), A_120)) | ~r1_tarski(A_120, k1_wellord1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_225, c_395])).
% 14.48/6.07  tff(c_413, plain, (![A_120]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')), A_120)) | ~r1_tarski(A_120, k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_402])).
% 14.48/6.07  tff(c_91, plain, (![B_52, A_53]: (v2_wellord1(k2_wellord1(B_52, A_53)) | ~v2_wellord1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.48/6.07  tff(c_30, plain, (![A_13]: (v1_relat_2(A_13) | ~v2_wellord1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.48/6.07  tff(c_98, plain, (![B_52, A_53]: (v1_relat_2(k2_wellord1(B_52, A_53)) | ~v1_relat_1(k2_wellord1(B_52, A_53)) | ~v2_wellord1(B_52) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_91, c_30])).
% 14.48/6.07  tff(c_599, plain, (![C_147, A_148, B_149]: (v1_relat_2(k2_wellord1(C_147, A_148)) | ~v1_relat_1(k2_wellord1(k2_wellord1(C_147, B_149), A_148)) | ~v2_wellord1(k2_wellord1(C_147, B_149)) | ~v1_relat_1(k2_wellord1(C_147, B_149)) | ~r1_tarski(A_148, B_149) | ~v1_relat_1(C_147))), inference(superposition, [status(thm), theory('equality')], [c_157, c_98])).
% 14.48/6.07  tff(c_605, plain, (![A_120]: (v1_relat_2(k2_wellord1('#skF_7', A_120)) | ~v2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7'))) | ~v1_relat_1(k2_wellord1('#skF_7', k3_relat_1('#skF_7'))) | ~r1_tarski(A_120, k3_relat_1('#skF_7')) | ~v1_relat_1('#skF_7') | ~r1_tarski(A_120, k1_wellord1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_413, c_599])).
% 14.48/6.07  tff(c_627, plain, (![A_120]: (v1_relat_2(k2_wellord1('#skF_7', A_120)) | ~v2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7'))) | ~r1_tarski(A_120, k3_relat_1('#skF_7')) | ~r1_tarski(A_120, k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_471, c_605])).
% 14.48/6.07  tff(c_657, plain, (~v2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')))), inference(splitLeft, [status(thm)], [c_627])).
% 14.48/6.07  tff(c_661, plain, (~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_657])).
% 14.48/6.07  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_661])).
% 14.48/6.07  tff(c_667, plain, (v2_wellord1(k2_wellord1('#skF_7', k3_relat_1('#skF_7')))), inference(splitRight, [status(thm)], [c_627])).
% 14.48/6.07  tff(c_176, plain, (![C_72, A_74, B_73]: (v2_wellord1(k2_wellord1(C_72, A_74)) | ~v2_wellord1(k2_wellord1(C_72, B_73)) | ~v1_relat_1(k2_wellord1(C_72, B_73)) | ~r1_tarski(A_74, B_73) | ~v1_relat_1(C_72))), inference(superposition, [status(thm), theory('equality')], [c_157, c_50])).
% 14.48/6.07  tff(c_671, plain, (![A_74]: (v2_wellord1(k2_wellord1('#skF_7', A_74)) | ~v1_relat_1(k2_wellord1('#skF_7', k3_relat_1('#skF_7'))) | ~r1_tarski(A_74, k3_relat_1('#skF_7')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_667, c_176])).
% 14.48/6.07  tff(c_704, plain, (![A_167]: (v2_wellord1(k2_wellord1('#skF_7', A_167)) | ~r1_tarski(A_167, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_471, c_671])).
% 14.48/6.07  tff(c_708, plain, (![A_23]: (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_23))) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_46, c_704])).
% 14.48/6.07  tff(c_711, plain, (![A_23]: (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_708])).
% 14.48/6.07  tff(c_58, plain, (![A_38, B_40]: (~r4_wellord1(A_38, k2_wellord1(A_38, k1_wellord1(A_38, B_40))) | ~r2_hidden(B_40, k3_relat_1(A_38)) | ~v2_wellord1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.48/6.07  tff(c_4780, plain, (![C_396, B_397, A_398]: (~r4_wellord1(k2_wellord1(C_396, k1_wellord1(C_396, B_397)), k2_wellord1(k2_wellord1(C_396, k1_wellord1(C_396, B_397)), k1_wellord1(C_396, A_398))) | ~r2_hidden(A_398, k3_relat_1(k2_wellord1(C_396, k1_wellord1(C_396, B_397)))) | ~v2_wellord1(k2_wellord1(C_396, k1_wellord1(C_396, B_397))) | ~v1_relat_1(k2_wellord1(C_396, k1_wellord1(C_396, B_397))) | ~r2_hidden(A_398, k1_wellord1(C_396, B_397)) | ~v2_wellord1(C_396) | ~v1_relat_1(C_396))), inference(superposition, [status(thm), theory('equality')], [c_232, c_58])).
% 14.48/6.07  tff(c_14055, plain, (![C_706, B_707, A_708]: (~r4_wellord1(k2_wellord1(C_706, k1_wellord1(C_706, B_707)), k2_wellord1(C_706, k1_wellord1(C_706, A_708))) | ~r2_hidden(A_708, k3_relat_1(k2_wellord1(C_706, k1_wellord1(C_706, B_707)))) | ~v2_wellord1(k2_wellord1(C_706, k1_wellord1(C_706, B_707))) | ~v1_relat_1(k2_wellord1(C_706, k1_wellord1(C_706, B_707))) | ~r2_hidden(A_708, k1_wellord1(C_706, B_707)) | ~v2_wellord1(C_706) | ~v1_relat_1(C_706) | ~r1_tarski(k1_wellord1(C_706, A_708), k1_wellord1(C_706, B_707)) | ~v1_relat_1(C_706))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4780])).
% 14.48/6.07  tff(c_14207, plain, (~r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | ~v2_wellord1('#skF_7') | ~r1_tarski(k1_wellord1('#skF_7', '#skF_6'), k1_wellord1('#skF_7', '#skF_5')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_14055])).
% 14.48/6.07  tff(c_14265, plain, (~r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~r1_tarski(k1_wellord1('#skF_7', '#skF_6'), k1_wellord1('#skF_7', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3588, c_156, c_711, c_14207])).
% 14.48/6.07  tff(c_14266, plain, (~r1_tarski(k1_wellord1('#skF_7', '#skF_6'), k1_wellord1('#skF_7', '#skF_5'))), inference(splitLeft, [status(thm)], [c_14265])).
% 14.48/6.07  tff(c_14269, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1293, c_14266])).
% 14.48/6.07  tff(c_14273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3588, c_156, c_14269])).
% 14.48/6.07  tff(c_14274, plain, (~r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))))), inference(splitRight, [status(thm)], [c_14265])).
% 14.48/6.07  tff(c_14484, plain, (~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_54, c_14274])).
% 14.48/6.07  tff(c_14487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3588, c_14484])).
% 14.48/6.07  tff(c_14489, plain, (r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_3574])).
% 14.48/6.07  tff(c_224, plain, (r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitRight, [status(thm)], [c_155])).
% 14.48/6.07  tff(c_15837, plain, (![C_761, B_762, A_763]: (~r4_wellord1(k2_wellord1(C_761, k1_wellord1(C_761, B_762)), k2_wellord1(k2_wellord1(C_761, k1_wellord1(C_761, B_762)), k1_wellord1(C_761, A_763))) | ~r2_hidden(A_763, k3_relat_1(k2_wellord1(C_761, k1_wellord1(C_761, B_762)))) | ~v2_wellord1(k2_wellord1(C_761, k1_wellord1(C_761, B_762))) | ~v1_relat_1(k2_wellord1(C_761, k1_wellord1(C_761, B_762))) | ~r2_hidden(A_763, k1_wellord1(C_761, B_762)) | ~v2_wellord1(C_761) | ~v1_relat_1(C_761))), inference(superposition, [status(thm), theory('equality')], [c_232, c_58])).
% 14.48/6.07  tff(c_24412, plain, (![C_1066, B_1067, A_1068]: (~r4_wellord1(k2_wellord1(C_1066, k1_wellord1(C_1066, B_1067)), k2_wellord1(C_1066, k1_wellord1(C_1066, A_1068))) | ~r2_hidden(A_1068, k3_relat_1(k2_wellord1(C_1066, k1_wellord1(C_1066, B_1067)))) | ~v2_wellord1(k2_wellord1(C_1066, k1_wellord1(C_1066, B_1067))) | ~v1_relat_1(k2_wellord1(C_1066, k1_wellord1(C_1066, B_1067))) | ~r2_hidden(A_1068, k1_wellord1(C_1066, B_1067)) | ~v2_wellord1(C_1066) | ~v1_relat_1(C_1066) | ~r1_tarski(k1_wellord1(C_1066, A_1068), k1_wellord1(C_1066, B_1067)) | ~v1_relat_1(C_1066))), inference(superposition, [status(thm), theory('equality')], [c_48, c_15837])).
% 14.48/6.07  tff(c_24545, plain, (~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~r1_tarski(k1_wellord1('#skF_7', '#skF_5'), k1_wellord1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_224, c_24412])).
% 14.48/6.07  tff(c_24607, plain, (~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r1_tarski(k1_wellord1('#skF_7', '#skF_5'), k1_wellord1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_14489, c_225, c_711, c_24545])).
% 14.48/6.07  tff(c_24611, plain, (~r1_tarski(k1_wellord1('#skF_7', '#skF_5'), k1_wellord1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_24607])).
% 14.48/6.07  tff(c_24614, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1293, c_24611])).
% 14.48/6.07  tff(c_24618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_14489, c_225, c_24614])).
% 14.48/6.07  tff(c_24619, plain, (~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))))), inference(splitRight, [status(thm)], [c_24607])).
% 14.48/6.07  tff(c_24863, plain, (~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_54, c_24619])).
% 14.48/6.07  tff(c_24866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_14489, c_24863])).
% 14.48/6.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.48/6.07  
% 14.48/6.07  Inference rules
% 14.48/6.07  ----------------------
% 14.48/6.07  #Ref     : 0
% 14.48/6.07  #Sup     : 5519
% 14.48/6.07  #Fact    : 4
% 14.48/6.07  #Define  : 0
% 14.48/6.07  #Split   : 30
% 14.48/6.07  #Chain   : 0
% 14.48/6.07  #Close   : 0
% 14.48/6.07  
% 14.48/6.07  Ordering : KBO
% 14.48/6.07  
% 14.48/6.07  Simplification rules
% 14.48/6.07  ----------------------
% 14.48/6.07  #Subsume      : 1620
% 14.48/6.07  #Demod        : 4102
% 14.48/6.07  #Tautology    : 291
% 14.48/6.07  #SimpNegUnit  : 22
% 14.48/6.07  #BackRed      : 12
% 14.48/6.07  
% 14.48/6.07  #Partial instantiations: 0
% 14.48/6.07  #Strategies tried      : 1
% 14.48/6.07  
% 14.48/6.07  Timing (in seconds)
% 14.48/6.07  ----------------------
% 14.48/6.07  Preprocessing        : 0.43
% 14.48/6.07  Parsing              : 0.21
% 14.48/6.07  CNF conversion       : 0.03
% 14.48/6.07  Main loop            : 4.82
% 14.48/6.07  Inferencing          : 1.29
% 14.48/6.07  Reduction            : 1.57
% 14.48/6.07  Demodulation         : 1.14
% 14.48/6.07  BG Simplification    : 0.17
% 14.48/6.07  Subsumption          : 1.52
% 14.48/6.07  Abstraction          : 0.25
% 14.48/6.07  MUC search           : 0.00
% 14.48/6.07  Cooper               : 0.00
% 14.48/6.07  Total                : 5.29
% 14.48/6.07  Index Insertion      : 0.00
% 14.48/6.07  Index Deletion       : 0.00
% 14.48/6.07  Index Matching       : 0.00
% 14.48/6.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
