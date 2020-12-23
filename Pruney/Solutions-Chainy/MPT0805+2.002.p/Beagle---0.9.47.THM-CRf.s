%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:49 EST 2020

% Result     : Theorem 12.43s
% Output     : CNFRefutation 12.50s
% Verified   : 
% Statistics : Number of formulae       :  195 (10973 expanded)
%              Number of leaves         :   36 (3649 expanded)
%              Depth                    :   44
%              Number of atoms          :  622 (40417 expanded)
%              Number of equality atoms :   70 (5697 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

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

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ~ ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C))
            & A != B
            & r4_wellord1(k2_wellord1(C,k1_wellord1(C,A)),k2_wellord1(C,k1_wellord1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_wellord1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B))
        <=> ( A = B
            | r2_hidden(A,k1_wellord1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => v2_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k1_wellord1(C,B)) )
       => k1_wellord1(k2_wellord1(C,k1_wellord1(C,B)),A) = k1_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(c_68,plain,(
    r2_hidden('#skF_6',k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_74,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_72,plain,(
    v2_wellord1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_70,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k2_wellord1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_106,plain,(
    ! [B_56,A_57] :
      ( r4_wellord1(B_56,A_57)
      | ~ r4_wellord1(A_57,B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_109,plain,
    ( r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
    | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_64,c_106])).

tff(c_178,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_181,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_181])).

tff(c_186,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_205,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_208,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_205])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_208])).

tff(c_214,plain,(
    v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_424,plain,(
    ! [A_133,C_134,B_135] :
      ( ~ r2_hidden(A_133,k1_wellord1(C_134,B_135))
      | r1_tarski(k1_wellord1(C_134,A_133),k1_wellord1(C_134,B_135))
      | ~ r2_hidden(B_135,k3_relat_1(C_134))
      | ~ r2_hidden(A_133,k3_relat_1(C_134))
      | ~ v2_wellord1(C_134)
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_187,plain,(
    v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_130,plain,(
    ! [C_65,B_66,A_67] :
      ( k2_wellord1(k2_wellord1(C_65,B_66),A_67) = k2_wellord1(C_65,A_67)
      | ~ r1_tarski(A_67,B_66)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ! [C_25,B_24,A_23] :
      ( k2_wellord1(k2_wellord1(C_25,B_24),A_23) = k2_wellord1(C_25,A_23)
      | ~ r1_tarski(A_23,B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_284,plain,(
    ! [C_100,B_101,A_102,A_103] :
      ( k2_wellord1(k2_wellord1(C_100,B_101),A_102) = k2_wellord1(k2_wellord1(C_100,A_103),A_102)
      | ~ r1_tarski(A_102,A_103)
      | ~ v1_relat_1(k2_wellord1(C_100,B_101))
      | ~ r1_tarski(A_103,B_101)
      | ~ v1_relat_1(C_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_46])).

tff(c_288,plain,(
    ! [A_102,A_103] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_102) = k2_wellord1(k2_wellord1('#skF_7',A_103),A_102)
      | ~ r1_tarski(A_102,A_103)
      | ~ r1_tarski(A_103,k1_wellord1('#skF_7','#skF_5'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_187,c_284])).

tff(c_298,plain,(
    ! [A_102,A_103] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_102) = k2_wellord1(k2_wellord1('#skF_7',A_103),A_102)
      | ~ r1_tarski(A_102,A_103)
      | ~ r1_tarski(A_103,k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_288])).

tff(c_431,plain,(
    ! [A_133,A_102] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_133)),A_102) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_102)
      | ~ r1_tarski(A_102,k1_wellord1('#skF_7',A_133))
      | ~ r2_hidden(A_133,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
      | ~ r2_hidden(A_133,k3_relat_1('#skF_7'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_424,c_298])).

tff(c_452,plain,(
    ! [A_136,A_137] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_136)),A_137) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_137)
      | ~ r1_tarski(A_137,k1_wellord1('#skF_7',A_136))
      | ~ r2_hidden(A_136,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_136,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_431])).

tff(c_1340,plain,(
    ! [A_177,A_178] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_177))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_178)))
      | ~ r1_tarski(A_177,k1_wellord1('#skF_7',A_178))
      | ~ r2_hidden(A_178,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_178,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_32])).

tff(c_1346,plain,(
    ! [A_177] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_177))
      | ~ r1_tarski(A_177,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_214,c_1340])).

tff(c_1356,plain,(
    ! [A_177] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_177))
      | ~ r1_tarski(A_177,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1346])).

tff(c_1389,plain,(
    ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1356])).

tff(c_24,plain,(
    ! [A_13] :
      ( v6_relat_2(A_13)
      | ~ v2_wellord1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_371,plain,(
    ! [C_124,B_125,A_126] :
      ( r2_hidden(k4_tarski(C_124,B_125),A_126)
      | r2_hidden(k4_tarski(B_125,C_124),A_126)
      | C_124 = B_125
      | ~ r2_hidden(C_124,k3_relat_1(A_126))
      | ~ r2_hidden(B_125,k3_relat_1(A_126))
      | ~ v6_relat_2(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [D_12,A_1,B_8] :
      ( r2_hidden(D_12,k1_wellord1(A_1,B_8))
      | ~ r2_hidden(k4_tarski(D_12,B_8),A_1)
      | D_12 = B_8
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_630,plain,(
    ! [C_145,A_146,B_147] :
      ( r2_hidden(C_145,k1_wellord1(A_146,B_147))
      | r2_hidden(k4_tarski(B_147,C_145),A_146)
      | C_145 = B_147
      | ~ r2_hidden(C_145,k3_relat_1(A_146))
      | ~ r2_hidden(B_147,k3_relat_1(A_146))
      | ~ v6_relat_2(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_371,c_2])).

tff(c_693,plain,(
    ! [B_154,A_155,C_156] :
      ( r2_hidden(B_154,k1_wellord1(A_155,C_156))
      | r2_hidden(C_156,k1_wellord1(A_155,B_154))
      | C_156 = B_154
      | ~ r2_hidden(C_156,k3_relat_1(A_155))
      | ~ r2_hidden(B_154,k3_relat_1(A_155))
      | ~ v6_relat_2(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_630,c_2])).

tff(c_527,plain,(
    ! [A_136,A_137] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_136)),A_137))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ r1_tarski(A_137,k1_wellord1('#skF_7',A_136))
      | ~ r2_hidden(A_136,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_136,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_32])).

tff(c_577,plain,(
    ! [A_138,A_139] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_138)),A_139))
      | ~ r1_tarski(A_139,k1_wellord1('#skF_7',A_138))
      | ~ r2_hidden(A_138,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_138,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_527])).

tff(c_587,plain,(
    ! [A_23,A_138] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',A_138))
      | ~ r2_hidden(A_138,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_138,k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',A_138))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_577])).

tff(c_591,plain,(
    ! [A_23,A_138] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r2_hidden(A_138,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_138,k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',A_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_587])).

tff(c_707,plain,(
    ! [A_23,B_154] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',B_154))
      | r2_hidden('#skF_5',k1_wellord1('#skF_7',B_154))
      | B_154 = '#skF_5'
      | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
      | ~ r2_hidden(B_154,k3_relat_1('#skF_7'))
      | ~ v6_relat_2('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_693,c_591])).

tff(c_789,plain,(
    ! [A_23,B_154] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',B_154))
      | r2_hidden('#skF_5',k1_wellord1('#skF_7',B_154))
      | B_154 = '#skF_5'
      | ~ r2_hidden(B_154,k3_relat_1('#skF_7'))
      | ~ v6_relat_2('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_707])).

tff(c_808,plain,(
    ~ v6_relat_2('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_964,plain,
    ( ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_808])).

tff(c_971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_964])).

tff(c_973,plain,(
    v6_relat_2('#skF_7') ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_660,plain,(
    ! [B_147,A_146,C_145] :
      ( r2_hidden(B_147,k1_wellord1(A_146,C_145))
      | r2_hidden(C_145,k1_wellord1(A_146,B_147))
      | C_145 = B_147
      | ~ r2_hidden(C_145,k3_relat_1(A_146))
      | ~ r2_hidden(B_147,k3_relat_1(A_146))
      | ~ v6_relat_2(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_630,c_2])).

tff(c_48,plain,(
    ! [B_27,A_26] :
      ( v2_wellord1(k2_wellord1(B_27,A_26))
      | ~ v2_wellord1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    ! [C_33,B_32] :
      ( r1_tarski(k1_wellord1(C_33,B_32),k1_wellord1(C_33,B_32))
      | ~ r2_hidden(B_32,k3_relat_1(C_33))
      | ~ v2_wellord1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_286,plain,(
    ! [A_102,A_103] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_102) = k2_wellord1(k2_wellord1('#skF_7',A_103),A_102)
      | ~ r1_tarski(A_102,A_103)
      | ~ r1_tarski(A_103,k1_wellord1('#skF_7','#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_214,c_284])).

tff(c_295,plain,(
    ! [A_102,A_103] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_102) = k2_wellord1(k2_wellord1('#skF_7',A_103),A_102)
      | ~ r1_tarski(A_102,A_103)
      | ~ r1_tarski(A_103,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_286])).

tff(c_434,plain,(
    ! [A_133,A_102] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_133)),A_102) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_102)
      | ~ r1_tarski(A_102,k1_wellord1('#skF_7',A_133))
      | ~ r2_hidden(A_133,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
      | ~ r2_hidden(A_133,k3_relat_1('#skF_7'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_424,c_295])).

tff(c_1089,plain,(
    ! [A_169,A_170] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_169)),A_170) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_170)
      | ~ r1_tarski(A_170,k1_wellord1('#skF_7',A_169))
      | ~ r2_hidden(A_169,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_169,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_434])).

tff(c_1171,plain,(
    ! [A_170,A_169] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_170) = k2_wellord1('#skF_7',A_170)
      | ~ r1_tarski(A_170,k1_wellord1('#skF_7',A_169))
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(A_170,k1_wellord1('#skF_7',A_169))
      | ~ r2_hidden(A_169,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_169,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_46])).

tff(c_1600,plain,(
    ! [A_199,A_200] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_199) = k2_wellord1('#skF_7',A_199)
      | ~ r1_tarski(A_199,k1_wellord1('#skF_7',A_200))
      | ~ r2_hidden(A_200,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_200,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1171])).

tff(c_1606,plain,(
    ! [B_32] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k1_wellord1('#skF_7',B_32)) = k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_56,c_1600])).

tff(c_1613,plain,(
    ! [B_201] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k1_wellord1('#skF_7',B_201)) = k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_201))
      | ~ r2_hidden(B_201,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_201,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1606])).

tff(c_1646,plain,(
    ! [B_201] :
      ( v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_201)))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r2_hidden(B_201,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_201,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_48])).

tff(c_1680,plain,(
    ! [B_201] :
      ( v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_201)))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r2_hidden(B_201,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_201,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1646])).

tff(c_1731,plain,(
    ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1680])).

tff(c_1737,plain,
    ( ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_1731])).

tff(c_1744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1737])).

tff(c_1746,plain,(
    v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1680])).

tff(c_1612,plain,(
    ! [B_32] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k1_wellord1('#skF_7',B_32)) = k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1606])).

tff(c_233,plain,(
    ! [C_94,B_95,A_96] :
      ( k1_wellord1(k2_wellord1(C_94,k1_wellord1(C_94,B_95)),A_96) = k1_wellord1(C_94,A_96)
      | ~ r2_hidden(A_96,k1_wellord1(C_94,B_95))
      | ~ v2_wellord1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    ! [B_35,A_34] :
      ( k3_relat_1(k2_wellord1(B_35,k1_wellord1(B_35,A_34))) = k1_wellord1(B_35,A_34)
      | ~ v2_wellord1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3676,plain,(
    ! [C_303,B_304,A_305] :
      ( k3_relat_1(k2_wellord1(k2_wellord1(C_303,k1_wellord1(C_303,B_304)),k1_wellord1(C_303,A_305))) = k1_wellord1(k2_wellord1(C_303,k1_wellord1(C_303,B_304)),A_305)
      | ~ v2_wellord1(k2_wellord1(C_303,k1_wellord1(C_303,B_304)))
      | ~ v1_relat_1(k2_wellord1(C_303,k1_wellord1(C_303,B_304)))
      | ~ r2_hidden(A_305,k1_wellord1(C_303,B_304))
      | ~ v2_wellord1(C_303)
      | ~ v1_relat_1(C_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_58])).

tff(c_3710,plain,(
    ! [B_32] :
      ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),B_32) = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32)))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_3676])).

tff(c_3769,plain,(
    ! [B_32] :
      ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),B_32) = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32)))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_214,c_1746,c_3710])).

tff(c_4672,plain,(
    ! [C_326,B_327,A_328] :
      ( r1_tarski(k1_wellord1(k2_wellord1(C_326,k1_wellord1(C_326,B_327)),A_328),k1_wellord1(C_326,A_328))
      | ~ r2_hidden(A_328,k3_relat_1(k2_wellord1(C_326,k1_wellord1(C_326,B_327))))
      | ~ v2_wellord1(k2_wellord1(C_326,k1_wellord1(C_326,B_327)))
      | ~ v1_relat_1(k2_wellord1(C_326,k1_wellord1(C_326,B_327)))
      | ~ r2_hidden(A_328,k1_wellord1(C_326,B_327))
      | ~ v2_wellord1(C_326)
      | ~ v1_relat_1(C_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_56])).

tff(c_4774,plain,(
    ! [B_32] :
      ( r1_tarski(k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))),k1_wellord1('#skF_7',B_32))
      | ~ r2_hidden(B_32,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_4672])).

tff(c_5490,plain,(
    ! [B_339] :
      ( r1_tarski(k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_339))),k1_wellord1('#skF_7',B_339))
      | ~ r2_hidden(B_339,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ r2_hidden(B_339,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_339,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_214,c_1746,c_4774])).

tff(c_5553,plain,(
    ! [A_102] :
      ( k2_wellord1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))),A_102) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_102)
      | ~ r1_tarski(A_102,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
      | ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_5490,c_298])).

tff(c_5607,plain,(
    ! [A_102] :
      ( k2_wellord1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))),A_102) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_102)
      | ~ r1_tarski(A_102,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
      | ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5553])).

tff(c_5617,plain,(
    ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5607])).

tff(c_5620,plain,
    ( r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
    | ~ v6_relat_2('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_660,c_5617])).

tff(c_5626,plain,
    ( r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_973,c_70,c_68,c_5620])).

tff(c_5628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1389,c_5626])).

tff(c_5630,plain,(
    r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5607])).

tff(c_54,plain,(
    ! [A_31,C_33,B_32] :
      ( ~ r2_hidden(A_31,k1_wellord1(C_33,B_32))
      | r1_tarski(k1_wellord1(C_33,A_31),k1_wellord1(C_33,B_32))
      | ~ r2_hidden(B_32,k3_relat_1(C_33))
      | ~ r2_hidden(A_31,k3_relat_1(C_33))
      | ~ v2_wellord1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4225,plain,(
    ! [C_315,A_316,B_317] :
      ( r1_tarski(k1_wellord1(C_315,A_316),k1_wellord1(k2_wellord1(C_315,k1_wellord1(C_315,B_317)),A_316))
      | ~ r2_hidden(A_316,k3_relat_1(k2_wellord1(C_315,k1_wellord1(C_315,B_317))))
      | ~ v2_wellord1(k2_wellord1(C_315,k1_wellord1(C_315,B_317)))
      | ~ v1_relat_1(k2_wellord1(C_315,k1_wellord1(C_315,B_317)))
      | ~ r2_hidden(A_316,k1_wellord1(C_315,B_317))
      | ~ v2_wellord1(C_315)
      | ~ v1_relat_1(C_315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_56])).

tff(c_4255,plain,(
    ! [B_32] :
      ( r1_tarski(k1_wellord1('#skF_7',B_32),k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))))
      | ~ r2_hidden(B_32,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_4225])).

tff(c_4902,plain,(
    ! [B_329] :
      ( r1_tarski(k1_wellord1('#skF_7',B_329),k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_329))))
      | ~ r2_hidden(B_329,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ r2_hidden(B_329,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_329,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_214,c_1746,c_4255])).

tff(c_4924,plain,(
    ! [A_34] :
      ( r1_tarski(k1_wellord1('#skF_7',A_34),k1_wellord1('#skF_7',A_34))
      | ~ r2_hidden(A_34,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ r2_hidden(A_34,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_34,k3_relat_1('#skF_7'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4902])).

tff(c_5059,plain,(
    ! [A_332] :
      ( r1_tarski(k1_wellord1('#skF_7',A_332),k1_wellord1('#skF_7',A_332))
      | ~ r2_hidden(A_332,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ r2_hidden(A_332,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_332,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4924])).

tff(c_5095,plain,(
    ! [A_332] :
      ( r1_tarski(k1_wellord1('#skF_7',A_332),k1_wellord1('#skF_7',A_332))
      | ~ r2_hidden(A_332,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_332,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_332,k3_relat_1('#skF_7'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_5059])).

tff(c_5119,plain,(
    ! [A_332] :
      ( r1_tarski(k1_wellord1('#skF_7',A_332),k1_wellord1('#skF_7',A_332))
      | ~ r2_hidden(A_332,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_332,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5095])).

tff(c_3784,plain,(
    ! [B_306] :
      ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),B_306) = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_306)))
      | ~ r2_hidden(B_306,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_306,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_214,c_1746,c_3710])).

tff(c_50,plain,(
    ! [C_30,B_29,A_28] :
      ( k1_wellord1(k2_wellord1(C_30,k1_wellord1(C_30,B_29)),A_28) = k1_wellord1(C_30,A_28)
      | ~ r2_hidden(A_28,k1_wellord1(C_30,B_29))
      | ~ v2_wellord1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3842,plain,(
    ! [B_306] :
      ( k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_306))) = k1_wellord1('#skF_7',B_306)
      | ~ r2_hidden(B_306,k1_wellord1('#skF_7','#skF_6'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(B_306,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_306,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3784,c_50])).

tff(c_3915,plain,(
    ! [B_306] :
      ( k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_306))) = k1_wellord1('#skF_7',B_306)
      | ~ r2_hidden(B_306,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_306,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3842])).

tff(c_4895,plain,(
    ! [B_32] :
      ( r1_tarski(k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))),k1_wellord1('#skF_7',B_32))
      | ~ r2_hidden(B_32,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_214,c_1746,c_4774])).

tff(c_1180,plain,(
    ! [A_169,A_170] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_169)),A_170))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r1_tarski(A_170,k1_wellord1('#skF_7',A_169))
      | ~ r2_hidden(A_169,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_169,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_32])).

tff(c_1433,plain,(
    ! [A_187,A_188] :
      ( v1_relat_1(k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_187)),A_188))
      | ~ r1_tarski(A_188,k1_wellord1('#skF_7',A_187))
      | ~ r2_hidden(A_187,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_187,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1180])).

tff(c_1452,plain,(
    ! [A_23,A_187] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',A_187))
      | ~ r2_hidden(A_187,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_187,k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',A_187))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1433])).

tff(c_1460,plain,(
    ! [A_23,A_187] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r2_hidden(A_187,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_187,k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7',A_187)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1452])).

tff(c_5642,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5630,c_1460])).

tff(c_5667,plain,(
    ! [A_340] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_340))
      | ~ r1_tarski(A_340,k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5642])).

tff(c_5671,plain,
    ( v1_relat_1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))))
    | ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
    | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4895,c_5667])).

tff(c_5698,plain,
    ( v1_relat_1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))))
    | ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5630,c_5671])).

tff(c_5717,plain,(
    ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_5698])).

tff(c_5726,plain,
    ( ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_5717])).

tff(c_5733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5630,c_5726])).

tff(c_5735,plain,(
    r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_5698])).

tff(c_5629,plain,(
    ! [A_102] :
      ( ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
      | k2_wellord1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))),A_102) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_102)
      | ~ r1_tarski(A_102,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ) ),
    inference(splitRight,[status(thm)],[c_5607])).

tff(c_5768,plain,(
    ! [A_341] :
      ( k2_wellord1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))),A_341) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_341)
      | ~ r1_tarski(A_341,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5735,c_5629])).

tff(c_5855,plain,(
    ! [A_341] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_341) = k2_wellord1('#skF_7',A_341)
      | ~ r1_tarski(A_341,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(A_341,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5768,c_46])).

tff(c_6273,plain,(
    ! [A_348] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_348) = k2_wellord1('#skF_7',A_348)
      | ~ r1_tarski(A_348,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5855])).

tff(c_6287,plain,(
    ! [A_348] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_348) = k2_wellord1('#skF_7',A_348)
      | ~ r1_tarski(A_348,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3915,c_6273])).

tff(c_7324,plain,(
    ! [A_360] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_360) = k2_wellord1('#skF_7',A_360)
      | ~ r1_tarski(A_360,k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5630,c_6287])).

tff(c_450,plain,(
    ! [A_133,A_102] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_133)),A_102) = k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_102)
      | ~ r1_tarski(A_102,k1_wellord1('#skF_7',A_133))
      | ~ r2_hidden(A_133,k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_133,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_434])).

tff(c_7454,plain,(
    ! [A_360] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_360) = k2_wellord1('#skF_7',A_360)
      | ~ r1_tarski(A_360,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
      | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_360,k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7324,c_450])).

tff(c_7702,plain,(
    ! [A_363] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_363) = k2_wellord1('#skF_7',A_363)
      | ~ r1_tarski(A_363,k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5630,c_7454])).

tff(c_255,plain,(
    ! [C_94,B_95,A_96] :
      ( k3_relat_1(k2_wellord1(k2_wellord1(C_94,k1_wellord1(C_94,B_95)),k1_wellord1(C_94,A_96))) = k1_wellord1(k2_wellord1(C_94,k1_wellord1(C_94,B_95)),A_96)
      | ~ v2_wellord1(k2_wellord1(C_94,k1_wellord1(C_94,B_95)))
      | ~ v1_relat_1(k2_wellord1(C_94,k1_wellord1(C_94,B_95)))
      | ~ r2_hidden(A_96,k1_wellord1(C_94,B_95))
      | ~ v2_wellord1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_58])).

tff(c_7760,plain,(
    ! [A_96] :
      ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_96) = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_96)))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
      | ~ r2_hidden(A_96,k1_wellord1('#skF_7','#skF_6'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(k1_wellord1('#skF_7',A_96),k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7702,c_255])).

tff(c_10484,plain,(
    ! [A_419] :
      ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),A_419) = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',A_419)))
      | ~ r2_hidden(A_419,k1_wellord1('#skF_7','#skF_6'))
      | ~ r1_tarski(k1_wellord1('#skF_7',A_419),k1_wellord1('#skF_7','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_214,c_1746,c_7760])).

tff(c_10488,plain,
    ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),'#skF_5') = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
    | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_5119,c_10484])).

tff(c_10503,plain,(
    k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),'#skF_5') = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5630,c_10488])).

tff(c_10646,plain,
    ( k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) = k1_wellord1('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10503,c_50])).

tff(c_10760,plain,(
    k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) = k1_wellord1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5630,c_10646])).

tff(c_10793,plain,(
    k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),'#skF_5') = k1_wellord1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10760,c_10503])).

tff(c_213,plain,(
    r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_199,plain,(
    ! [A_80,B_81] :
      ( ~ r4_wellord1(A_80,k2_wellord1(A_80,k1_wellord1(A_80,B_81)))
      | ~ r2_hidden(B_81,k3_relat_1(A_80))
      | ~ v2_wellord1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_203,plain,(
    ! [C_25,B_24,B_81] :
      ( ~ r4_wellord1(k2_wellord1(C_25,B_24),k2_wellord1(C_25,k1_wellord1(k2_wellord1(C_25,B_24),B_81)))
      | ~ r2_hidden(B_81,k3_relat_1(k2_wellord1(C_25,B_24)))
      | ~ v2_wellord1(k2_wellord1(C_25,B_24))
      | ~ v1_relat_1(k2_wellord1(C_25,B_24))
      | ~ r1_tarski(k1_wellord1(k2_wellord1(C_25,B_24),B_81),B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_199])).

tff(c_11223,plain,
    ( ~ r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
    | ~ r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6'))))
    | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))
    | ~ r1_tarski(k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')),'#skF_5'),k1_wellord1('#skF_7','#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10793,c_203])).

tff(c_11353,plain,(
    ~ r1_tarski(k1_wellord1('#skF_7','#skF_5'),k1_wellord1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10793,c_214,c_1746,c_5735,c_213,c_11223])).

tff(c_12057,plain,
    ( ~ r2_hidden('#skF_5',k1_wellord1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_11353])).

tff(c_12061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_5630,c_12057])).

tff(c_12063,plain,(
    r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1356])).

tff(c_518,plain,(
    ! [A_137,A_136] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_137) = k2_wellord1('#skF_7',A_137)
      | ~ r1_tarski(A_137,k1_wellord1('#skF_7',A_136))
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski(A_137,k1_wellord1('#skF_7',A_136))
      | ~ r2_hidden(A_136,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_136,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_46])).

tff(c_1006,plain,(
    ! [A_165,A_166] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),A_165) = k2_wellord1('#skF_7',A_165)
      | ~ r1_tarski(A_165,k1_wellord1('#skF_7',A_166))
      | ~ r2_hidden(A_166,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_166,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_518])).

tff(c_1012,plain,(
    ! [B_32] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),k1_wellord1('#skF_7',B_32)) = k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_56,c_1006])).

tff(c_1019,plain,(
    ! [B_167] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),k1_wellord1('#skF_7',B_167)) = k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_167))
      | ~ r2_hidden(B_167,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_167,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1012])).

tff(c_1049,plain,(
    ! [B_167] :
      ( v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_167)))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ r2_hidden(B_167,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_167,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_48])).

tff(c_1081,plain,(
    ! [B_167] :
      ( v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_167)))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ r2_hidden(B_167,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_167,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_1049])).

tff(c_1249,plain,(
    ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1081])).

tff(c_1252,plain,
    ( ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_1249])).

tff(c_1256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1252])).

tff(c_1258,plain,(
    v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_1018,plain,(
    ! [B_32] :
      ( k2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),k1_wellord1('#skF_7',B_32)) = k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1012])).

tff(c_13605,plain,(
    ! [C_518,B_519,A_520] :
      ( k3_relat_1(k2_wellord1(k2_wellord1(C_518,k1_wellord1(C_518,B_519)),k1_wellord1(C_518,A_520))) = k1_wellord1(k2_wellord1(C_518,k1_wellord1(C_518,B_519)),A_520)
      | ~ v2_wellord1(k2_wellord1(C_518,k1_wellord1(C_518,B_519)))
      | ~ v1_relat_1(k2_wellord1(C_518,k1_wellord1(C_518,B_519)))
      | ~ r2_hidden(A_520,k1_wellord1(C_518,B_519))
      | ~ v2_wellord1(C_518)
      | ~ v1_relat_1(C_518) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_58])).

tff(c_13639,plain,(
    ! [B_32] :
      ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),B_32) = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32)))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_13605])).

tff(c_13681,plain,(
    ! [B_32] :
      ( k1_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),B_32) = k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32)))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_187,c_1258,c_13639])).

tff(c_14242,plain,(
    ! [C_548,B_549,A_550] :
      ( r1_tarski(k1_wellord1(k2_wellord1(C_548,k1_wellord1(C_548,B_549)),A_550),k1_wellord1(C_548,A_550))
      | ~ r2_hidden(A_550,k3_relat_1(k2_wellord1(C_548,k1_wellord1(C_548,B_549))))
      | ~ v2_wellord1(k2_wellord1(C_548,k1_wellord1(C_548,B_549)))
      | ~ v1_relat_1(k2_wellord1(C_548,k1_wellord1(C_548,B_549)))
      | ~ r2_hidden(A_550,k1_wellord1(C_548,B_549))
      | ~ v2_wellord1(C_548)
      | ~ v1_relat_1(C_548) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_56])).

tff(c_14350,plain,(
    ! [B_32] :
      ( r1_tarski(k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32))),k1_wellord1('#skF_7',B_32))
      | ~ r2_hidden(B_32,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13681,c_14242])).

tff(c_15081,plain,(
    ! [B_575] :
      ( r1_tarski(k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_575))),k1_wellord1('#skF_7',B_575))
      | ~ r2_hidden(B_575,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
      | ~ r2_hidden(B_575,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_575,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_187,c_1258,c_14350])).

tff(c_12065,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_12063,c_591])).

tff(c_12068,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_wellord1('#skF_7',A_23))
      | ~ r1_tarski(A_23,k1_wellord1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12065])).

tff(c_15133,plain,
    ( v1_relat_1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))))
    | ~ r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
    | ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_15081,c_12068])).

tff(c_15198,plain,
    ( v1_relat_1(k2_wellord1('#skF_7',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_6')))))
    | ~ r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12063,c_15133])).

tff(c_15221,plain,(
    ~ r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_15198])).

tff(c_15357,plain,
    ( ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_15221])).

tff(c_15362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_12063,c_15357])).

tff(c_15364,plain,(
    r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_15198])).

tff(c_62,plain,(
    ! [A_39,B_41] :
      ( ~ r4_wellord1(A_39,k2_wellord1(A_39,k1_wellord1(A_39,B_41)))
      | ~ r2_hidden(B_41,k3_relat_1(A_39))
      | ~ v2_wellord1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_15665,plain,(
    ! [C_586,B_587,A_588] :
      ( ~ r4_wellord1(k2_wellord1(C_586,k1_wellord1(C_586,B_587)),k2_wellord1(k2_wellord1(C_586,k1_wellord1(C_586,B_587)),k1_wellord1(C_586,A_588)))
      | ~ r2_hidden(A_588,k3_relat_1(k2_wellord1(C_586,k1_wellord1(C_586,B_587))))
      | ~ v2_wellord1(k2_wellord1(C_586,k1_wellord1(C_586,B_587)))
      | ~ v1_relat_1(k2_wellord1(C_586,k1_wellord1(C_586,B_587)))
      | ~ r2_hidden(A_588,k1_wellord1(C_586,B_587))
      | ~ v2_wellord1(C_586)
      | ~ v1_relat_1(C_586) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_62])).

tff(c_15728,plain,(
    ! [B_32] :
      ( ~ r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_32)))
      | ~ r2_hidden(B_32,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
      | ~ v2_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ v1_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')))
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ v2_wellord1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(B_32,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_32,k3_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_15665])).

tff(c_18548,plain,(
    ! [B_709] :
      ( ~ r4_wellord1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5')),k2_wellord1('#skF_7',k1_wellord1('#skF_7',B_709)))
      | ~ r2_hidden(B_709,k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
      | ~ r2_hidden(B_709,k1_wellord1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_709,k3_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_187,c_1258,c_15728])).

tff(c_18551,plain,
    ( ~ r2_hidden('#skF_6',k3_relat_1(k2_wellord1('#skF_7',k1_wellord1('#skF_7','#skF_5'))))
    | ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_18548])).

tff(c_18555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12063,c_15364,c_18551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.43/4.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.50/4.80  
% 12.50/4.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.50/4.80  %$ r4_wellord1 > r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 12.50/4.80  
% 12.50/4.80  %Foreground sorts:
% 12.50/4.80  
% 12.50/4.80  
% 12.50/4.80  %Background operators:
% 12.50/4.80  
% 12.50/4.80  
% 12.50/4.80  %Foreground operators:
% 12.50/4.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.50/4.80  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 12.50/4.80  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.50/4.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.50/4.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.50/4.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.50/4.80  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 12.50/4.80  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 12.50/4.80  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 12.50/4.80  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 12.50/4.80  tff('#skF_7', type, '#skF_7': $i).
% 12.50/4.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.50/4.80  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 12.50/4.80  tff('#skF_5', type, '#skF_5': $i).
% 12.50/4.80  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 12.50/4.80  tff('#skF_6', type, '#skF_6': $i).
% 12.50/4.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.50/4.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.50/4.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.50/4.80  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.50/4.80  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 12.50/4.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.50/4.80  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 12.50/4.80  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 12.50/4.80  
% 12.50/4.83  tff(f_149, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ~((((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) & ~(A = B)) & r4_wellord1(k2_wellord1(C, k1_wellord1(C, A)), k2_wellord1(C, k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_wellord1)).
% 12.50/4.83  tff(f_56, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 12.50/4.83  tff(f_124, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 12.50/4.83  tff(f_109, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)) <=> ((A = B) | r2_hidden(A, k1_wellord1(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_wellord1)).
% 12.50/4.83  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 12.50/4.83  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 12.50/4.83  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 12.50/4.83  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 12.50/4.83  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => v2_wellord1(k2_wellord1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_wellord1)).
% 12.50/4.83  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => ((v2_wellord1(C) & r2_hidden(A, k1_wellord1(C, B))) => (k1_wellord1(k2_wellord1(C, k1_wellord1(C, B)), A) = k1_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_wellord1)).
% 12.50/4.83  tff(f_115, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => (k3_relat_1(k2_wellord1(B, k1_wellord1(B, A))) = k1_wellord1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_wellord1)).
% 12.50/4.83  tff(f_134, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 12.50/4.83  tff(c_68, plain, (r2_hidden('#skF_6', k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.50/4.83  tff(c_74, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.50/4.83  tff(c_72, plain, (v2_wellord1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.50/4.83  tff(c_70, plain, (r2_hidden('#skF_5', k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.50/4.83  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.50/4.83  tff(c_32, plain, (![A_14, B_15]: (v1_relat_1(k2_wellord1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.50/4.83  tff(c_64, plain, (r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.50/4.83  tff(c_106, plain, (![B_56, A_57]: (r4_wellord1(B_56, A_57) | ~r4_wellord1(A_57, B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.50/4.83  tff(c_109, plain, (r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(resolution, [status(thm)], [c_64, c_106])).
% 12.50/4.83  tff(c_178, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitLeft, [status(thm)], [c_109])).
% 12.50/4.83  tff(c_181, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_178])).
% 12.50/4.83  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_181])).
% 12.50/4.83  tff(c_186, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitRight, [status(thm)], [c_109])).
% 12.50/4.83  tff(c_205, plain, (~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_186])).
% 12.50/4.83  tff(c_208, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_205])).
% 12.50/4.83  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_208])).
% 12.50/4.83  tff(c_214, plain, (v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_186])).
% 12.50/4.83  tff(c_424, plain, (![A_133, C_134, B_135]: (~r2_hidden(A_133, k1_wellord1(C_134, B_135)) | r1_tarski(k1_wellord1(C_134, A_133), k1_wellord1(C_134, B_135)) | ~r2_hidden(B_135, k3_relat_1(C_134)) | ~r2_hidden(A_133, k3_relat_1(C_134)) | ~v2_wellord1(C_134) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.50/4.83  tff(c_187, plain, (v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitRight, [status(thm)], [c_109])).
% 12.50/4.83  tff(c_130, plain, (![C_65, B_66, A_67]: (k2_wellord1(k2_wellord1(C_65, B_66), A_67)=k2_wellord1(C_65, A_67) | ~r1_tarski(A_67, B_66) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.50/4.83  tff(c_46, plain, (![C_25, B_24, A_23]: (k2_wellord1(k2_wellord1(C_25, B_24), A_23)=k2_wellord1(C_25, A_23) | ~r1_tarski(A_23, B_24) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.50/4.83  tff(c_284, plain, (![C_100, B_101, A_102, A_103]: (k2_wellord1(k2_wellord1(C_100, B_101), A_102)=k2_wellord1(k2_wellord1(C_100, A_103), A_102) | ~r1_tarski(A_102, A_103) | ~v1_relat_1(k2_wellord1(C_100, B_101)) | ~r1_tarski(A_103, B_101) | ~v1_relat_1(C_100))), inference(superposition, [status(thm), theory('equality')], [c_130, c_46])).
% 12.50/4.83  tff(c_288, plain, (![A_102, A_103]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_102)=k2_wellord1(k2_wellord1('#skF_7', A_103), A_102) | ~r1_tarski(A_102, A_103) | ~r1_tarski(A_103, k1_wellord1('#skF_7', '#skF_5')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_187, c_284])).
% 12.50/4.83  tff(c_298, plain, (![A_102, A_103]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_102)=k2_wellord1(k2_wellord1('#skF_7', A_103), A_102) | ~r1_tarski(A_102, A_103) | ~r1_tarski(A_103, k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_288])).
% 12.50/4.83  tff(c_431, plain, (![A_133, A_102]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_133)), A_102)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_102) | ~r1_tarski(A_102, k1_wellord1('#skF_7', A_133)) | ~r2_hidden(A_133, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~r2_hidden(A_133, k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_424, c_298])).
% 12.50/4.83  tff(c_452, plain, (![A_136, A_137]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_136)), A_137)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_137) | ~r1_tarski(A_137, k1_wellord1('#skF_7', A_136)) | ~r2_hidden(A_136, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_136, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_431])).
% 12.50/4.83  tff(c_1340, plain, (![A_177, A_178]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_177)) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_178))) | ~r1_tarski(A_177, k1_wellord1('#skF_7', A_178)) | ~r2_hidden(A_178, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_178, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_452, c_32])).
% 12.50/4.83  tff(c_1346, plain, (![A_177]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_177)) | ~r1_tarski(A_177, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_214, c_1340])).
% 12.50/4.83  tff(c_1356, plain, (![A_177]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_177)) | ~r1_tarski(A_177, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1346])).
% 12.50/4.83  tff(c_1389, plain, (~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1356])).
% 12.50/4.83  tff(c_24, plain, (![A_13]: (v6_relat_2(A_13) | ~v2_wellord1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.50/4.83  tff(c_371, plain, (![C_124, B_125, A_126]: (r2_hidden(k4_tarski(C_124, B_125), A_126) | r2_hidden(k4_tarski(B_125, C_124), A_126) | C_124=B_125 | ~r2_hidden(C_124, k3_relat_1(A_126)) | ~r2_hidden(B_125, k3_relat_1(A_126)) | ~v6_relat_2(A_126) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.50/4.83  tff(c_2, plain, (![D_12, A_1, B_8]: (r2_hidden(D_12, k1_wellord1(A_1, B_8)) | ~r2_hidden(k4_tarski(D_12, B_8), A_1) | D_12=B_8 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.50/4.83  tff(c_630, plain, (![C_145, A_146, B_147]: (r2_hidden(C_145, k1_wellord1(A_146, B_147)) | r2_hidden(k4_tarski(B_147, C_145), A_146) | C_145=B_147 | ~r2_hidden(C_145, k3_relat_1(A_146)) | ~r2_hidden(B_147, k3_relat_1(A_146)) | ~v6_relat_2(A_146) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_371, c_2])).
% 12.50/4.83  tff(c_693, plain, (![B_154, A_155, C_156]: (r2_hidden(B_154, k1_wellord1(A_155, C_156)) | r2_hidden(C_156, k1_wellord1(A_155, B_154)) | C_156=B_154 | ~r2_hidden(C_156, k3_relat_1(A_155)) | ~r2_hidden(B_154, k3_relat_1(A_155)) | ~v6_relat_2(A_155) | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_630, c_2])).
% 12.50/4.83  tff(c_527, plain, (![A_136, A_137]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_136)), A_137)) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r1_tarski(A_137, k1_wellord1('#skF_7', A_136)) | ~r2_hidden(A_136, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_136, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_452, c_32])).
% 12.50/4.83  tff(c_577, plain, (![A_138, A_139]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_138)), A_139)) | ~r1_tarski(A_139, k1_wellord1('#skF_7', A_138)) | ~r2_hidden(A_138, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_138, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_527])).
% 12.50/4.83  tff(c_587, plain, (![A_23, A_138]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r1_tarski(A_23, k1_wellord1('#skF_7', A_138)) | ~r2_hidden(A_138, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_138, k3_relat_1('#skF_7')) | ~r1_tarski(A_23, k1_wellord1('#skF_7', A_138)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_577])).
% 12.50/4.83  tff(c_591, plain, (![A_23, A_138]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r2_hidden(A_138, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_138, k3_relat_1('#skF_7')) | ~r1_tarski(A_23, k1_wellord1('#skF_7', A_138)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_587])).
% 12.50/4.83  tff(c_707, plain, (![A_23, B_154]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r1_tarski(A_23, k1_wellord1('#skF_7', B_154)) | r2_hidden('#skF_5', k1_wellord1('#skF_7', B_154)) | B_154='#skF_5' | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~r2_hidden(B_154, k3_relat_1('#skF_7')) | ~v6_relat_2('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_693, c_591])).
% 12.50/4.83  tff(c_789, plain, (![A_23, B_154]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r1_tarski(A_23, k1_wellord1('#skF_7', B_154)) | r2_hidden('#skF_5', k1_wellord1('#skF_7', B_154)) | B_154='#skF_5' | ~r2_hidden(B_154, k3_relat_1('#skF_7')) | ~v6_relat_2('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_707])).
% 12.50/4.83  tff(c_808, plain, (~v6_relat_2('#skF_7')), inference(splitLeft, [status(thm)], [c_789])).
% 12.50/4.83  tff(c_964, plain, (~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_808])).
% 12.50/4.83  tff(c_971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_964])).
% 12.50/4.83  tff(c_973, plain, (v6_relat_2('#skF_7')), inference(splitRight, [status(thm)], [c_789])).
% 12.50/4.83  tff(c_660, plain, (![B_147, A_146, C_145]: (r2_hidden(B_147, k1_wellord1(A_146, C_145)) | r2_hidden(C_145, k1_wellord1(A_146, B_147)) | C_145=B_147 | ~r2_hidden(C_145, k3_relat_1(A_146)) | ~r2_hidden(B_147, k3_relat_1(A_146)) | ~v6_relat_2(A_146) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_630, c_2])).
% 12.50/4.83  tff(c_48, plain, (![B_27, A_26]: (v2_wellord1(k2_wellord1(B_27, A_26)) | ~v2_wellord1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.50/4.83  tff(c_56, plain, (![C_33, B_32]: (r1_tarski(k1_wellord1(C_33, B_32), k1_wellord1(C_33, B_32)) | ~r2_hidden(B_32, k3_relat_1(C_33)) | ~v2_wellord1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.50/4.83  tff(c_286, plain, (![A_102, A_103]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_102)=k2_wellord1(k2_wellord1('#skF_7', A_103), A_102) | ~r1_tarski(A_102, A_103) | ~r1_tarski(A_103, k1_wellord1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_214, c_284])).
% 12.50/4.83  tff(c_295, plain, (![A_102, A_103]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_102)=k2_wellord1(k2_wellord1('#skF_7', A_103), A_102) | ~r1_tarski(A_102, A_103) | ~r1_tarski(A_103, k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_286])).
% 12.50/4.83  tff(c_434, plain, (![A_133, A_102]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_133)), A_102)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_102) | ~r1_tarski(A_102, k1_wellord1('#skF_7', A_133)) | ~r2_hidden(A_133, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~r2_hidden(A_133, k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_424, c_295])).
% 12.50/4.83  tff(c_1089, plain, (![A_169, A_170]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_169)), A_170)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_170) | ~r1_tarski(A_170, k1_wellord1('#skF_7', A_169)) | ~r2_hidden(A_169, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_169, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_434])).
% 12.50/4.83  tff(c_1171, plain, (![A_170, A_169]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_170)=k2_wellord1('#skF_7', A_170) | ~r1_tarski(A_170, k1_wellord1('#skF_7', A_169)) | ~v1_relat_1('#skF_7') | ~r1_tarski(A_170, k1_wellord1('#skF_7', A_169)) | ~r2_hidden(A_169, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_169, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1089, c_46])).
% 12.50/4.83  tff(c_1600, plain, (![A_199, A_200]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_199)=k2_wellord1('#skF_7', A_199) | ~r1_tarski(A_199, k1_wellord1('#skF_7', A_200)) | ~r2_hidden(A_200, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_200, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1171])).
% 12.50/4.83  tff(c_1606, plain, (![B_32]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k1_wellord1('#skF_7', B_32))=k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32)) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_56, c_1600])).
% 12.50/4.83  tff(c_1613, plain, (![B_201]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k1_wellord1('#skF_7', B_201))=k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_201)) | ~r2_hidden(B_201, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_201, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1606])).
% 12.50/4.83  tff(c_1646, plain, (![B_201]: (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_201))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden(B_201, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_201, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1613, c_48])).
% 12.50/4.83  tff(c_1680, plain, (![B_201]: (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_201))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden(B_201, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_201, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_1646])).
% 12.50/4.83  tff(c_1731, plain, (~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1680])).
% 12.50/4.83  tff(c_1737, plain, (~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_48, c_1731])).
% 12.50/4.83  tff(c_1744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1737])).
% 12.50/4.83  tff(c_1746, plain, (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_1680])).
% 12.50/4.83  tff(c_1612, plain, (![B_32]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k1_wellord1('#skF_7', B_32))=k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32)) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1606])).
% 12.50/4.83  tff(c_233, plain, (![C_94, B_95, A_96]: (k1_wellord1(k2_wellord1(C_94, k1_wellord1(C_94, B_95)), A_96)=k1_wellord1(C_94, A_96) | ~r2_hidden(A_96, k1_wellord1(C_94, B_95)) | ~v2_wellord1(C_94) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.50/4.83  tff(c_58, plain, (![B_35, A_34]: (k3_relat_1(k2_wellord1(B_35, k1_wellord1(B_35, A_34)))=k1_wellord1(B_35, A_34) | ~v2_wellord1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.83  tff(c_3676, plain, (![C_303, B_304, A_305]: (k3_relat_1(k2_wellord1(k2_wellord1(C_303, k1_wellord1(C_303, B_304)), k1_wellord1(C_303, A_305)))=k1_wellord1(k2_wellord1(C_303, k1_wellord1(C_303, B_304)), A_305) | ~v2_wellord1(k2_wellord1(C_303, k1_wellord1(C_303, B_304))) | ~v1_relat_1(k2_wellord1(C_303, k1_wellord1(C_303, B_304))) | ~r2_hidden(A_305, k1_wellord1(C_303, B_304)) | ~v2_wellord1(C_303) | ~v1_relat_1(C_303))), inference(superposition, [status(thm), theory('equality')], [c_233, c_58])).
% 12.50/4.83  tff(c_3710, plain, (![B_32]: (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), B_32)=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1612, c_3676])).
% 12.50/4.83  tff(c_3769, plain, (![B_32]: (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), B_32)=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_214, c_1746, c_3710])).
% 12.50/4.83  tff(c_4672, plain, (![C_326, B_327, A_328]: (r1_tarski(k1_wellord1(k2_wellord1(C_326, k1_wellord1(C_326, B_327)), A_328), k1_wellord1(C_326, A_328)) | ~r2_hidden(A_328, k3_relat_1(k2_wellord1(C_326, k1_wellord1(C_326, B_327)))) | ~v2_wellord1(k2_wellord1(C_326, k1_wellord1(C_326, B_327))) | ~v1_relat_1(k2_wellord1(C_326, k1_wellord1(C_326, B_327))) | ~r2_hidden(A_328, k1_wellord1(C_326, B_327)) | ~v2_wellord1(C_326) | ~v1_relat_1(C_326))), inference(superposition, [status(thm), theory('equality')], [c_233, c_56])).
% 12.50/4.83  tff(c_4774, plain, (![B_32]: (r1_tarski(k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))), k1_wellord1('#skF_7', B_32)) | ~r2_hidden(B_32, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3769, c_4672])).
% 12.50/4.83  tff(c_5490, plain, (![B_339]: (r1_tarski(k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_339))), k1_wellord1('#skF_7', B_339)) | ~r2_hidden(B_339, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden(B_339, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_339, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_214, c_1746, c_4774])).
% 12.50/4.83  tff(c_5553, plain, (![A_102]: (k2_wellord1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), A_102)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_102) | ~r1_tarski(A_102, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_5490, c_298])).
% 12.50/4.83  tff(c_5607, plain, (![A_102]: (k2_wellord1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), A_102)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_102) | ~r1_tarski(A_102, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5553])).
% 12.50/4.83  tff(c_5617, plain, (~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_5607])).
% 12.50/4.83  tff(c_5620, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | '#skF_5'='#skF_6' | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~v6_relat_2('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_660, c_5617])).
% 12.50/4.83  tff(c_5626, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_973, c_70, c_68, c_5620])).
% 12.50/4.83  tff(c_5628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1389, c_5626])).
% 12.50/4.83  tff(c_5630, plain, (r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_5607])).
% 12.50/4.83  tff(c_54, plain, (![A_31, C_33, B_32]: (~r2_hidden(A_31, k1_wellord1(C_33, B_32)) | r1_tarski(k1_wellord1(C_33, A_31), k1_wellord1(C_33, B_32)) | ~r2_hidden(B_32, k3_relat_1(C_33)) | ~r2_hidden(A_31, k3_relat_1(C_33)) | ~v2_wellord1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.50/4.83  tff(c_4225, plain, (![C_315, A_316, B_317]: (r1_tarski(k1_wellord1(C_315, A_316), k1_wellord1(k2_wellord1(C_315, k1_wellord1(C_315, B_317)), A_316)) | ~r2_hidden(A_316, k3_relat_1(k2_wellord1(C_315, k1_wellord1(C_315, B_317)))) | ~v2_wellord1(k2_wellord1(C_315, k1_wellord1(C_315, B_317))) | ~v1_relat_1(k2_wellord1(C_315, k1_wellord1(C_315, B_317))) | ~r2_hidden(A_316, k1_wellord1(C_315, B_317)) | ~v2_wellord1(C_315) | ~v1_relat_1(C_315))), inference(superposition, [status(thm), theory('equality')], [c_233, c_56])).
% 12.50/4.83  tff(c_4255, plain, (![B_32]: (r1_tarski(k1_wellord1('#skF_7', B_32), k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32)))) | ~r2_hidden(B_32, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3769, c_4225])).
% 12.50/4.83  tff(c_4902, plain, (![B_329]: (r1_tarski(k1_wellord1('#skF_7', B_329), k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_329)))) | ~r2_hidden(B_329, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden(B_329, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_329, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_214, c_1746, c_4255])).
% 12.50/4.83  tff(c_4924, plain, (![A_34]: (r1_tarski(k1_wellord1('#skF_7', A_34), k1_wellord1('#skF_7', A_34)) | ~r2_hidden(A_34, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden(A_34, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_34, k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_4902])).
% 12.50/4.83  tff(c_5059, plain, (![A_332]: (r1_tarski(k1_wellord1('#skF_7', A_332), k1_wellord1('#skF_7', A_332)) | ~r2_hidden(A_332, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden(A_332, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_332, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4924])).
% 12.50/4.83  tff(c_5095, plain, (![A_332]: (r1_tarski(k1_wellord1('#skF_7', A_332), k1_wellord1('#skF_7', A_332)) | ~r2_hidden(A_332, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_332, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_332, k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_5059])).
% 12.50/4.83  tff(c_5119, plain, (![A_332]: (r1_tarski(k1_wellord1('#skF_7', A_332), k1_wellord1('#skF_7', A_332)) | ~r2_hidden(A_332, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_332, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5095])).
% 12.50/4.83  tff(c_3784, plain, (![B_306]: (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), B_306)=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_306))) | ~r2_hidden(B_306, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_306, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_214, c_1746, c_3710])).
% 12.50/4.83  tff(c_50, plain, (![C_30, B_29, A_28]: (k1_wellord1(k2_wellord1(C_30, k1_wellord1(C_30, B_29)), A_28)=k1_wellord1(C_30, A_28) | ~r2_hidden(A_28, k1_wellord1(C_30, B_29)) | ~v2_wellord1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.50/4.83  tff(c_3842, plain, (![B_306]: (k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_306)))=k1_wellord1('#skF_7', B_306) | ~r2_hidden(B_306, k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(B_306, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_306, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3784, c_50])).
% 12.50/4.83  tff(c_3915, plain, (![B_306]: (k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_306)))=k1_wellord1('#skF_7', B_306) | ~r2_hidden(B_306, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_306, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3842])).
% 12.50/4.83  tff(c_4895, plain, (![B_32]: (r1_tarski(k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))), k1_wellord1('#skF_7', B_32)) | ~r2_hidden(B_32, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_214, c_1746, c_4774])).
% 12.50/4.83  tff(c_1180, plain, (![A_169, A_170]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_169)), A_170)) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r1_tarski(A_170, k1_wellord1('#skF_7', A_169)) | ~r2_hidden(A_169, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_169, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1089, c_32])).
% 12.50/4.83  tff(c_1433, plain, (![A_187, A_188]: (v1_relat_1(k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_187)), A_188)) | ~r1_tarski(A_188, k1_wellord1('#skF_7', A_187)) | ~r2_hidden(A_187, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_187, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_1180])).
% 12.50/4.83  tff(c_1452, plain, (![A_23, A_187]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r1_tarski(A_23, k1_wellord1('#skF_7', A_187)) | ~r2_hidden(A_187, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_187, k3_relat_1('#skF_7')) | ~r1_tarski(A_23, k1_wellord1('#skF_7', A_187)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1433])).
% 12.50/4.83  tff(c_1460, plain, (![A_23, A_187]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r2_hidden(A_187, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_187, k3_relat_1('#skF_7')) | ~r1_tarski(A_23, k1_wellord1('#skF_7', A_187)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1452])).
% 12.50/4.83  tff(c_5642, plain, (![A_23]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~r1_tarski(A_23, k1_wellord1('#skF_7', '#skF_5')))), inference(resolution, [status(thm)], [c_5630, c_1460])).
% 12.50/4.83  tff(c_5667, plain, (![A_340]: (v1_relat_1(k2_wellord1('#skF_7', A_340)) | ~r1_tarski(A_340, k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5642])).
% 12.50/4.83  tff(c_5671, plain, (v1_relat_1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))))) | ~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_4895, c_5667])).
% 12.50/4.83  tff(c_5698, plain, (v1_relat_1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))))) | ~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5630, c_5671])).
% 12.50/4.83  tff(c_5717, plain, (~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))))), inference(splitLeft, [status(thm)], [c_5698])).
% 12.50/4.83  tff(c_5726, plain, (~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58, c_5717])).
% 12.50/4.83  tff(c_5733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5630, c_5726])).
% 12.50/4.83  tff(c_5735, plain, (r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))))), inference(splitRight, [status(thm)], [c_5698])).
% 12.50/4.83  tff(c_5629, plain, (![A_102]: (~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | k2_wellord1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), A_102)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_102) | ~r1_tarski(A_102, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))))), inference(splitRight, [status(thm)], [c_5607])).
% 12.50/4.83  tff(c_5768, plain, (![A_341]: (k2_wellord1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), A_341)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_341) | ~r1_tarski(A_341, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_5735, c_5629])).
% 12.50/4.83  tff(c_5855, plain, (![A_341]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_341)=k2_wellord1('#skF_7', A_341) | ~r1_tarski(A_341, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~v1_relat_1('#skF_7') | ~r1_tarski(A_341, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_5768, c_46])).
% 12.50/4.83  tff(c_6273, plain, (![A_348]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_348)=k2_wellord1('#skF_7', A_348) | ~r1_tarski(A_348, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5855])).
% 12.50/4.83  tff(c_6287, plain, (![A_348]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_348)=k2_wellord1('#skF_7', A_348) | ~r1_tarski(A_348, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3915, c_6273])).
% 12.50/4.83  tff(c_7324, plain, (![A_360]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_360)=k2_wellord1('#skF_7', A_360) | ~r1_tarski(A_360, k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5630, c_6287])).
% 12.50/4.83  tff(c_450, plain, (![A_133, A_102]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_133)), A_102)=k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_102) | ~r1_tarski(A_102, k1_wellord1('#skF_7', A_133)) | ~r2_hidden(A_133, k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden(A_133, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_434])).
% 12.50/4.83  tff(c_7454, plain, (![A_360]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_360)=k2_wellord1('#skF_7', A_360) | ~r1_tarski(A_360, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~r1_tarski(A_360, k1_wellord1('#skF_7', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_7324, c_450])).
% 12.50/4.83  tff(c_7702, plain, (![A_363]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_363)=k2_wellord1('#skF_7', A_363) | ~r1_tarski(A_363, k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5630, c_7454])).
% 12.50/4.83  tff(c_255, plain, (![C_94, B_95, A_96]: (k3_relat_1(k2_wellord1(k2_wellord1(C_94, k1_wellord1(C_94, B_95)), k1_wellord1(C_94, A_96)))=k1_wellord1(k2_wellord1(C_94, k1_wellord1(C_94, B_95)), A_96) | ~v2_wellord1(k2_wellord1(C_94, k1_wellord1(C_94, B_95))) | ~v1_relat_1(k2_wellord1(C_94, k1_wellord1(C_94, B_95))) | ~r2_hidden(A_96, k1_wellord1(C_94, B_95)) | ~v2_wellord1(C_94) | ~v1_relat_1(C_94))), inference(superposition, [status(thm), theory('equality')], [c_233, c_58])).
% 12.50/4.83  tff(c_7760, plain, (![A_96]: (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_96)=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_96))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r2_hidden(A_96, k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r1_tarski(k1_wellord1('#skF_7', A_96), k1_wellord1('#skF_7', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_7702, c_255])).
% 12.50/4.83  tff(c_10484, plain, (![A_419]: (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), A_419)=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', A_419))) | ~r2_hidden(A_419, k1_wellord1('#skF_7', '#skF_6')) | ~r1_tarski(k1_wellord1('#skF_7', A_419), k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_214, c_1746, c_7760])).
% 12.50/4.83  tff(c_10488, plain, (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), '#skF_5')=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_5119, c_10484])).
% 12.50/4.83  tff(c_10503, plain, (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), '#skF_5')=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5630, c_10488])).
% 12.50/4.83  tff(c_10646, plain, (k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))=k1_wellord1('#skF_7', '#skF_5') | ~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10503, c_50])).
% 12.50/4.83  tff(c_10760, plain, (k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))=k1_wellord1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5630, c_10646])).
% 12.50/4.83  tff(c_10793, plain, (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), '#skF_5')=k1_wellord1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10760, c_10503])).
% 12.50/4.83  tff(c_213, plain, (r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitRight, [status(thm)], [c_186])).
% 12.50/4.83  tff(c_199, plain, (![A_80, B_81]: (~r4_wellord1(A_80, k2_wellord1(A_80, k1_wellord1(A_80, B_81))) | ~r2_hidden(B_81, k3_relat_1(A_80)) | ~v2_wellord1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.50/4.83  tff(c_203, plain, (![C_25, B_24, B_81]: (~r4_wellord1(k2_wellord1(C_25, B_24), k2_wellord1(C_25, k1_wellord1(k2_wellord1(C_25, B_24), B_81))) | ~r2_hidden(B_81, k3_relat_1(k2_wellord1(C_25, B_24))) | ~v2_wellord1(k2_wellord1(C_25, B_24)) | ~v1_relat_1(k2_wellord1(C_25, B_24)) | ~r1_tarski(k1_wellord1(k2_wellord1(C_25, B_24), B_81), B_24) | ~v1_relat_1(C_25))), inference(superposition, [status(thm), theory('equality')], [c_46, c_199])).
% 12.50/4.83  tff(c_11223, plain, (~r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden('#skF_5', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))) | ~r1_tarski(k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6')), '#skF_5'), k1_wellord1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10793, c_203])).
% 12.50/4.83  tff(c_11353, plain, (~r1_tarski(k1_wellord1('#skF_7', '#skF_5'), k1_wellord1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10793, c_214, c_1746, c_5735, c_213, c_11223])).
% 12.50/4.83  tff(c_12057, plain, (~r2_hidden('#skF_5', k1_wellord1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_11353])).
% 12.50/4.83  tff(c_12061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_5630, c_12057])).
% 12.50/4.83  tff(c_12063, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5'))), inference(splitRight, [status(thm)], [c_1356])).
% 12.50/4.83  tff(c_518, plain, (![A_137, A_136]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_137)=k2_wellord1('#skF_7', A_137) | ~r1_tarski(A_137, k1_wellord1('#skF_7', A_136)) | ~v1_relat_1('#skF_7') | ~r1_tarski(A_137, k1_wellord1('#skF_7', A_136)) | ~r2_hidden(A_136, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_136, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_452, c_46])).
% 12.50/4.83  tff(c_1006, plain, (![A_165, A_166]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), A_165)=k2_wellord1('#skF_7', A_165) | ~r1_tarski(A_165, k1_wellord1('#skF_7', A_166)) | ~r2_hidden(A_166, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(A_166, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_518])).
% 12.50/4.83  tff(c_1012, plain, (![B_32]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), k1_wellord1('#skF_7', B_32))=k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32)) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_56, c_1006])).
% 12.50/4.83  tff(c_1019, plain, (![B_167]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), k1_wellord1('#skF_7', B_167))=k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_167)) | ~r2_hidden(B_167, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_167, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1012])).
% 12.50/4.83  tff(c_1049, plain, (![B_167]: (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_167))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden(B_167, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_167, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_48])).
% 12.50/4.83  tff(c_1081, plain, (![B_167]: (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_167))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden(B_167, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_167, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_1049])).
% 12.50/4.83  tff(c_1249, plain, (~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1081])).
% 12.50/4.83  tff(c_1252, plain, (~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_48, c_1249])).
% 12.50/4.83  tff(c_1256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1252])).
% 12.50/4.83  tff(c_1258, plain, (v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))), inference(splitRight, [status(thm)], [c_1081])).
% 12.50/4.83  tff(c_1018, plain, (![B_32]: (k2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), k1_wellord1('#skF_7', B_32))=k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32)) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1012])).
% 12.50/4.83  tff(c_13605, plain, (![C_518, B_519, A_520]: (k3_relat_1(k2_wellord1(k2_wellord1(C_518, k1_wellord1(C_518, B_519)), k1_wellord1(C_518, A_520)))=k1_wellord1(k2_wellord1(C_518, k1_wellord1(C_518, B_519)), A_520) | ~v2_wellord1(k2_wellord1(C_518, k1_wellord1(C_518, B_519))) | ~v1_relat_1(k2_wellord1(C_518, k1_wellord1(C_518, B_519))) | ~r2_hidden(A_520, k1_wellord1(C_518, B_519)) | ~v2_wellord1(C_518) | ~v1_relat_1(C_518))), inference(superposition, [status(thm), theory('equality')], [c_233, c_58])).
% 12.50/4.83  tff(c_13639, plain, (![B_32]: (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), B_32)=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_13605])).
% 12.50/4.83  tff(c_13681, plain, (![B_32]: (k1_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), B_32)=k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_187, c_1258, c_13639])).
% 12.50/4.83  tff(c_14242, plain, (![C_548, B_549, A_550]: (r1_tarski(k1_wellord1(k2_wellord1(C_548, k1_wellord1(C_548, B_549)), A_550), k1_wellord1(C_548, A_550)) | ~r2_hidden(A_550, k3_relat_1(k2_wellord1(C_548, k1_wellord1(C_548, B_549)))) | ~v2_wellord1(k2_wellord1(C_548, k1_wellord1(C_548, B_549))) | ~v1_relat_1(k2_wellord1(C_548, k1_wellord1(C_548, B_549))) | ~r2_hidden(A_550, k1_wellord1(C_548, B_549)) | ~v2_wellord1(C_548) | ~v1_relat_1(C_548))), inference(superposition, [status(thm), theory('equality')], [c_233, c_56])).
% 12.50/4.83  tff(c_14350, plain, (![B_32]: (r1_tarski(k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))), k1_wellord1('#skF_7', B_32)) | ~r2_hidden(B_32, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_13681, c_14242])).
% 12.50/4.83  tff(c_15081, plain, (![B_575]: (r1_tarski(k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_575))), k1_wellord1('#skF_7', B_575)) | ~r2_hidden(B_575, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~r2_hidden(B_575, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_575, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_187, c_1258, c_14350])).
% 12.50/4.83  tff(c_12065, plain, (![A_23]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~r1_tarski(A_23, k1_wellord1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_12063, c_591])).
% 12.50/4.83  tff(c_12068, plain, (![A_23]: (v1_relat_1(k2_wellord1('#skF_7', A_23)) | ~r1_tarski(A_23, k1_wellord1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12065])).
% 12.50/4.83  tff(c_15133, plain, (v1_relat_1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))))) | ~r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_15081, c_12068])).
% 12.50/4.83  tff(c_15198, plain, (v1_relat_1(k2_wellord1('#skF_7', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_6'))))) | ~r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12063, c_15133])).
% 12.50/4.83  tff(c_15221, plain, (~r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))))), inference(splitLeft, [status(thm)], [c_15198])).
% 12.50/4.83  tff(c_15357, plain, (~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58, c_15221])).
% 12.50/4.83  tff(c_15362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_12063, c_15357])).
% 12.50/4.83  tff(c_15364, plain, (r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))))), inference(splitRight, [status(thm)], [c_15198])).
% 12.50/4.83  tff(c_62, plain, (![A_39, B_41]: (~r4_wellord1(A_39, k2_wellord1(A_39, k1_wellord1(A_39, B_41))) | ~r2_hidden(B_41, k3_relat_1(A_39)) | ~v2_wellord1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.50/4.83  tff(c_15665, plain, (![C_586, B_587, A_588]: (~r4_wellord1(k2_wellord1(C_586, k1_wellord1(C_586, B_587)), k2_wellord1(k2_wellord1(C_586, k1_wellord1(C_586, B_587)), k1_wellord1(C_586, A_588))) | ~r2_hidden(A_588, k3_relat_1(k2_wellord1(C_586, k1_wellord1(C_586, B_587)))) | ~v2_wellord1(k2_wellord1(C_586, k1_wellord1(C_586, B_587))) | ~v1_relat_1(k2_wellord1(C_586, k1_wellord1(C_586, B_587))) | ~r2_hidden(A_588, k1_wellord1(C_586, B_587)) | ~v2_wellord1(C_586) | ~v1_relat_1(C_586))), inference(superposition, [status(thm), theory('equality')], [c_233, c_62])).
% 12.50/4.83  tff(c_15728, plain, (![B_32]: (~r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_32))) | ~r2_hidden(B_32, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~v2_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~v1_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5'))) | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(B_32, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_32, k3_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_15665])).
% 12.50/4.83  tff(c_18548, plain, (![B_709]: (~r4_wellord1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')), k2_wellord1('#skF_7', k1_wellord1('#skF_7', B_709))) | ~r2_hidden(B_709, k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~r2_hidden(B_709, k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden(B_709, k3_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_187, c_1258, c_15728])).
% 12.50/4.83  tff(c_18551, plain, (~r2_hidden('#skF_6', k3_relat_1(k2_wellord1('#skF_7', k1_wellord1('#skF_7', '#skF_5')))) | ~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_18548])).
% 12.50/4.83  tff(c_18555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_12063, c_15364, c_18551])).
% 12.50/4.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.50/4.83  
% 12.50/4.83  Inference rules
% 12.50/4.83  ----------------------
% 12.50/4.83  #Ref     : 0
% 12.50/4.83  #Sup     : 4073
% 12.50/4.83  #Fact    : 4
% 12.50/4.83  #Define  : 0
% 12.50/4.83  #Split   : 16
% 12.50/4.83  #Chain   : 0
% 12.50/4.83  #Close   : 0
% 12.50/4.83  
% 12.50/4.83  Ordering : KBO
% 12.50/4.83  
% 12.50/4.83  Simplification rules
% 12.50/4.83  ----------------------
% 12.50/4.83  #Subsume      : 1138
% 12.50/4.83  #Demod        : 3783
% 12.50/4.83  #Tautology    : 331
% 12.50/4.83  #SimpNegUnit  : 15
% 12.50/4.83  #BackRed      : 16
% 12.50/4.83  
% 12.50/4.83  #Partial instantiations: 0
% 12.50/4.83  #Strategies tried      : 1
% 12.50/4.83  
% 12.50/4.83  Timing (in seconds)
% 12.50/4.83  ----------------------
% 12.50/4.84  Preprocessing        : 0.37
% 12.50/4.84  Parsing              : 0.19
% 12.50/4.84  CNF conversion       : 0.03
% 12.50/4.84  Main loop            : 3.62
% 12.50/4.84  Inferencing          : 1.00
% 12.50/4.84  Reduction            : 1.11
% 12.50/4.84  Demodulation         : 0.78
% 12.50/4.84  BG Simplification    : 0.13
% 12.50/4.84  Subsumption          : 1.18
% 12.50/4.84  Abstraction          : 0.18
% 12.50/4.84  MUC search           : 0.00
% 12.50/4.84  Cooper               : 0.00
% 12.50/4.84  Total                : 4.06
% 12.50/4.84  Index Insertion      : 0.00
% 12.50/4.84  Index Deletion       : 0.00
% 12.50/4.84  Index Matching       : 0.00
% 12.50/4.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
